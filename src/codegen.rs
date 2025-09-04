use crate::ast::{AstNode, Pragma};
use crate::bytecode::{BytecodeChunk, CompiledProgram, Constant, Instruction};
use crate::errors::{CompilerError, CompilerResult};
use crate::register_allocator::{self, AllocationError, VirtualRegister, PhysicalRegister};
use crate::symbol_table::SymbolType;

use std::collections::HashMap;
use std::collections::HashSet;
const MAX_REGISTERS: usize = 32; // Example limit
const SECRET_REGISTER_START: usize = MAX_REGISTERS / 2; // Registers >= this are secret

/// It receives the generator state, the function definition node, and the pragma node.
type PragmaHandler = fn(&mut CodeGenerator, &AstNode, &Pragma) -> CompilerResult<()>;

#[derive(Debug)]
struct CodeGenerator {
    // Holds instructions using VirtualRegisters during generation for a scope.
    current_instructions: Vec<Instruction>,
    // Holds labels mapped to their *virtual* instruction index.
    current_labels: HashMap<String, usize>,
    // Counter for allocating new virtual registers.
    next_virtual_reg: usize,
    // Tracks the required secrecy for each virtual register. True = Secret.
    vr_secrecy: HashMap<VirtualRegister, bool>,
    // Variable symbol table (maps name to VirtualRegister index). Local to the current scope.
    symbol_table: HashMap<String, usize>,
    // Compiled functions.
    compiled_functions: HashMap<String, BytecodeChunk>,
    // If present, this chunk represents a 'proc main' (main without return type) to be used as program entry.
    main_proc_chunk: Option<BytecodeChunk>,
    // Known built-in functions (names only, no bytecode generated).
    known_builtins: HashSet<String>,
    // Pragma handlers: Maps pragma names to their handler functions.
    pragma_handlers: HashMap<String, PragmaHandler>,
    // Constants identified during code generation for this chunk.
    identified_constants: Vec<Constant>,
}

impl CodeGenerator {
    fn new() -> Self {
        CodeGenerator {
            current_instructions: Vec::new(),
            current_labels: HashMap::new(),
            next_virtual_reg: 0, // Start virtual registers from 0
            vr_secrecy: HashMap::new(),
            // Symbol table starts empty for each new generator instance (e.g., per function)
            symbol_table: HashMap::new(),
            compiled_functions: HashMap::new(),
            main_proc_chunk: None,
            known_builtins: HashSet::new(),
            pragma_handlers: Self::register_pragma_handlers(),
            identified_constants: Vec::new(),
        }
    }

    /// Registers built-in pragma handlers.
    fn register_pragma_handlers() -> HashMap<String, PragmaHandler> {
        let mut handlers: HashMap<String, PragmaHandler> = HashMap::new();

        // Register the "builtin" pragma handler
        handlers.insert("builtin".to_string(), handle_builtin_pragma);

        handlers
    }

    /// Allocates a new unique virtual register.
    /// Records whether the register needs to hold a secret value.
    fn allocate_virtual_register(&mut self, is_secret: bool) -> VirtualRegister {
        let vr = VirtualRegister(self.next_virtual_reg);
        self.next_virtual_reg += 1;
        self.vr_secrecy.insert(vr, is_secret);
        vr
    }

    /// Adds an instruction to the current temporary list.
    fn emit(&mut self, instruction: Instruction) {
        self.current_instructions.push(instruction);
    }

    /// Adds a label pointing to the *next* instruction index.
    fn add_label(&mut self, label: String) {
        let pos = self.current_instructions.len();
        self.current_labels.insert(label, pos);
    }

    /// Compiles an AST node, returning the VirtualRegister holding the result
    /// and a boolean indicating if the result is secret.
    fn compile_node(&mut self, node: &AstNode) -> CompilerResult<(VirtualRegister, bool)> {
        match node {
            // --- Literals ---
            AstNode::Literal(lit) => { // Literals are initially clear
                let vr = self.allocate_virtual_register(false); // Literals are clear
                let constant = match lit {
                    crate::ast::Value::Int { value, kind } => {
                        match kind {
                            Some(crate::ast::IntKind::Signed(w)) => match w {
                                crate::ast::IntWidth::W8 => Constant::I8(*value as i8),
                                crate::ast::IntWidth::W16 => Constant::I16(*value as i16),
                                crate::ast::IntWidth::W32 => Constant::I32(*value as i32),
                                crate::ast::IntWidth::W64 => Constant::I64(*value as i64),
                            },
                            Some(crate::ast::IntKind::Unsigned(w)) => match w {
                                crate::ast::IntWidth::W8 => Constant::U8(*value as u8),
                                crate::ast::IntWidth::W16 => Constant::U16(*value as u16),
                                crate::ast::IntWidth::W32 => Constant::U32(*value as u32),
                                crate::ast::IntWidth::W64 => Constant::U64(*value as u64),
                            },
                            None => Constant::I64(*value as i64), // default behavior
                        }
                    }
                    crate::ast::Value::Float(f) => Constant::Float(*f as i64),
                    crate::ast::Value::String(s) => Constant::String(s.clone()),
                    crate::ast::Value::Bool(b) => Constant::Bool(*b),
                    crate::ast::Value::Nil => Constant::Unit,
                };
                // Record constant and convert to Value
                self.identified_constants.push(constant.clone());
                let value = crate::core_types::Value::from(constant);
                self.emit(Instruction::LDI(vr.0, value));
                Ok((vr, false)) // Return VR and its secrecy (false)
            },
            // --- Identifiers ---
            AstNode::Identifier(name, location) => {
                // Semantic analysis already verified this identifier exists.
                // Look it up to get its register.
                if let Some(&vr_index) = self.symbol_table.get(name) {
                    let vr = VirtualRegister(vr_index);
                    let is_secret = *self.vr_secrecy.get(&vr)
                        .expect("Identifier VR missing from secrecy map");
                    Ok((vr, is_secret))
                } else {
                    Err(CompilerError::internal_error(format!(
                        "Codegen failed: Symbol '{}' passed semantic analysis but not found in codegen symbol table", name
                    )))
                }
            },
            AstNode::VariableDeclaration { name, value, type_annotation, is_mutable, is_secret, location } => {
                // Determine if the initial value needs a secret register
                // Secrecy comes from 'secret let/var' or a 'secret' type annotation.
                // Semantic analysis should have ensured consistency if both are present.
                let type_is_secret = type_annotation.as_ref().map_or(false, |n| SymbolType::from_ast(n).is_secret());
                let needs_secret = *is_secret || type_is_secret;

                let (value_vr, value_is_secret) = match value {
                    Some(val_expr) => {
                        let (vr, is_sec) = self.compile_node(val_expr)?; // Compile the expression first
                        // Check if value secrecy matches declaration requirement
                        if is_sec != needs_secret { // Implicit hide/reveal via MOV
                            let target_vr = self.allocate_virtual_register(needs_secret);
                            self.emit(Instruction::MOV(target_vr.0, vr.0));
                            (target_vr, needs_secret) // Variable gets the new VR
                        } else {
                            (vr, is_sec) // Secrecy matches, use the value's VR directly
                        }
                    }
                    None => { // No initial value, load default (Nil for now)
                        let vr = self.allocate_virtual_register(needs_secret);
                        self.identified_constants.push(Constant::Unit);
                                                self.emit(Instruction::LDI(vr.0, crate::core_types::Value::Unit)); // Load Unit
                        (vr, needs_secret)
                    }
                };

                // Store the variable name and its register in the symbol table.
                self.symbol_table.insert(name.clone(), value_vr.0);
                // Update vr_secrecy map for this VR to ensure it has the correct flag
                self.vr_secrecy.insert(value_vr, needs_secret);

                Ok((value_vr, needs_secret)) // Return the VR holding the initial value and its secrecy
            },
            // --- Operations ---
            AstNode::UnaryOperation { op, operand, location } => {
                let (operand_vr, operand_is_secret) = self.compile_node(operand)?;
                let result_is_secret = operand_is_secret; // Unary ops preserve secrecy
                let dest_vr = self.allocate_virtual_register(result_is_secret);

                // TODO: Implement specific unary instructions (NEG, NOT)
                self.emit(Instruction::MOV(dest_vr.0, operand_vr.0));

                Ok((dest_vr, result_is_secret))
            },
            AstNode::BinaryOperation { op, left, right, location } => {
                let (left_vr, left_is_secret) = self.compile_node(left)?;
                let (right_vr, right_is_secret) = self.compile_node(right)?;

                let mut result_is_secret = left_is_secret || right_is_secret;

                match op.as_str() {
                    "+" | "-" | "*" | "/" | "%" | // Arithmetic
                    "and" | "or" | "xor" | // Logical/Bitwise
                    "shl" | "shr" // Shifts
                    => {
                        let dest_vr = self.allocate_virtual_register(result_is_secret);
                        match op.as_str() {
                            "+" => self.emit(Instruction::ADD(dest_vr.0, left_vr.0, right_vr.0)),
                            "-" => self.emit(Instruction::SUB(dest_vr.0, left_vr.0, right_vr.0)),
                            "*" => self.emit(Instruction::MUL(dest_vr.0, left_vr.0, right_vr.0)),
                            "/" => self.emit(Instruction::DIV(dest_vr.0, left_vr.0, right_vr.0)),
                            "%" => self.emit(Instruction::MOD(dest_vr.0, left_vr.0, right_vr.0)),
                            "and" => self.emit(Instruction::AND(dest_vr.0, left_vr.0, right_vr.0)),
                            "or" => self.emit(Instruction::OR(dest_vr.0, left_vr.0, right_vr.0)),
                            "xor" => self.emit(Instruction::XOR(dest_vr.0, left_vr.0, right_vr.0)),
                            "shl" => self.emit(Instruction::SHL(dest_vr.0, left_vr.0, right_vr.0)),
                            "shr" => self.emit(Instruction::SHR(dest_vr.0, left_vr.0, right_vr.0)),
                            _ => unreachable!(),
                        }
                        Ok((dest_vr, result_is_secret))
                    }
                    "==" | "!=" | "<" | "<=" | ">" | ">=" => {
                        // Comparison operators produce a boolean result, which is always clear.
                        result_is_secret = false; // Override secrecy for comparisons
                        let bool_dest_vr = self.allocate_virtual_register(result_is_secret);

                        // Emit CMP instruction
                        self.emit(Instruction::CMP(left_vr.0, right_vr.0));

                        // Emit the appropriate conditional jump
                        match op.as_str() {
                            "==" | "!=" | "<" | ">" => {
                                // Standard logic: Jump to true label if condition met
                                let true_label = format!("cmp_true_{}", self.current_instructions.len());
                                let end_label = format!("cmp_end_{}", self.current_instructions.len());

                                let jump_instruction = match op.as_str() {
                                    "==" => Instruction::JMPEQ(true_label.clone()),
                                    "!=" => Instruction::JMPNEQ(true_label.clone()),
                                    "<" => Instruction::JMPLT(true_label.clone()),
                                    ">" => Instruction::JMPGT(true_label.clone()),
                                    _ => unreachable!(),
                                };
                                self.emit(jump_instruction);

                                // If condition is false
                                self.identified_constants.push(Constant::Bool(false));
                                self.emit(Instruction::LDI(bool_dest_vr.0, crate::core_types::Value::Bool(false)));
                                self.emit(Instruction::JMP(end_label.clone()));

                                // Define the true label's position
                                self.add_label(true_label);
                                self.identified_constants.push(Constant::Bool(true));
                                self.emit(Instruction::LDI(bool_dest_vr.0, crate::core_types::Value::Bool(true)));

                                // Define the end label's position
                                self.add_label(end_label);
                            },
                            "<=" | ">=" => {
                                // Inverted logic: Jump to false label if opposite condition met
                                let false_label = format!("cmp_false_{}", self.current_instructions.len());
                                let end_label = format!("cmp_end_{}", self.current_instructions.len());

                                let jump_instruction = match op.as_str() {
                                    "<=" => Instruction::JMPGT(false_label.clone()), // Jump if >
                                    ">=" => Instruction::JMPLT(false_label.clone()), // Jump if <
                                    _ => unreachable!(),
                                };
                                self.emit(jump_instruction);

                                // If condition is true (jump not taken)
                                self.identified_constants.push(Constant::Bool(true));
                                self.emit(Instruction::LDI(bool_dest_vr.0, crate::core_types::Value::Bool(true)));
                                self.emit(Instruction::JMP(end_label.clone()));

                                // Define the false label's position
                                self.add_label(false_label);
                                self.identified_constants.push(Constant::Bool(false));
                                self.emit(Instruction::LDI(bool_dest_vr.0, crate::core_types::Value::Bool(false)));

                                // Define the end label's position
                                self.add_label(end_label);
                            },
                            _ => unreachable!(), // Should be covered by outer match
                        };

                        // left_vr and right_vr are used. bool_dest_vr is defined.
                        Ok((bool_dest_vr, result_is_secret))
                    },
                    _ => Err(CompilerError::semantic_error(format!("Unsupported binary operator: {}", op), location.clone())
                        .with_hint(format!("Supported operators are: +, -, *, /, ==, !=, <, <=, >, >="))),
                }
            },
            // --- Assignment ---
            AstNode::Assignment { target, value, location } => {
                let (value_vr, value_is_secret) = self.compile_node(value)?;
                match target.as_ref() {
                    AstNode::Identifier(name, target_loc) => {
                        let dest_vr_index = self.symbol_table.get(name).cloned().ok_or_else(|| CompilerError::internal_error(format!("Assignment target '{}' not found in symbol table", name)))?;
                        // The MOV instruction implicitly handles potential hide/reveal
                        // based on the source and destination register halves.
                        self.emit(Instruction::MOV(dest_vr_index, value_vr.0));

                        // The destination VR retains its original secrecy property,
                        let dest_vr = VirtualRegister(dest_vr_index);
                        let dest_is_secret = *self.vr_secrecy.get(&dest_vr)
                            .expect("Destination VR missing from secrecy map in assignment");

                        // Assignment itself doesn't produce a value/register to be used further.
                        Ok((dest_vr, dest_is_secret))
                    }
                    AstNode::FieldAccess { object, field_name, location: _ } => {
                        let (object_vr, object_is_secret) = self.compile_node(object)?;
                        // We don't have a direct SetField instruction in the new set
                        // This would need custom implementation (e.g., STR instruction)
                        Ok((object_vr, object_is_secret)) // Return object vr, though it's now free
                    } // TODO: Implement field assignment
                    _ => Err(CompilerError::semantic_error("Invalid assignment target", location.clone())),
                }
            },
            // --- Control Flow & Functions ---
            AstNode::FunctionCall { function, arguments, location, resolved_return_type } => {
                // 1. Identify the function name
                // Semantic analysis already verified the function exists and is callable.
                let function_name = match function.as_ref() {
                    AstNode::Identifier(name, _) => name.clone(),
                    // Semantic analysis should have caught non-identifier calls if unsupported
                    _ => return Err(CompilerError::internal_error(
                        "Codegen expected identifier for function call after semantic analysis".to_string())),
                };

                // 3. Compile arguments first (do NOT emit PUSHARG yet) to keep PUSHARGs contiguous before CALL
                let mut arg_vrs = Vec::with_capacity(arguments.len());
                for arg in arguments {
                    let (arg_vr, _arg_is_secret) = self.compile_node(arg)?;
                    arg_vrs.push(arg_vr);
                }
                // After all arguments are compiled, emit contiguous PUSHARGs in order
                for vr in &arg_vrs {
                    self.emit(Instruction::PUSHARG(vr.0));
                }

                // 4. Determine result type and secrecy from resolved type (added by semantic analysis)
                let return_type = resolved_return_type.as_ref().cloned()
                    .unwrap_or(SymbolType::Unknown);

                let result_is_secret = return_type.is_secret();
                let result_vr = self.allocate_virtual_register(result_is_secret);

                self.emit(Instruction::CALL(function_name.clone()));
                // Only move the result if the function actually returns something
                if return_type != SymbolType::Void {
                    self.emit(Instruction::MOV(result_vr.0, 0)); // Assume result is in r0 (physical) after call
                }

                Ok((result_vr, result_is_secret)) // Return the VR holding the result
            },
            AstNode::IfExpression { condition, then_branch, else_branch } => {
                let (condition_vr, condition_is_secret) = self.compile_node(condition)?;
                if condition_is_secret {
                    return Err(CompilerError::semantic_error("Cannot use secret value as condition in 'if'", condition.location()));
                }

                // Compare the boolean condition VR against Bool(false)
                // Note: Condition itself is already boolean, but CMP sets flags for jumps.
                let false_vr = self.allocate_virtual_register(false); // false is clear
                self.identified_constants.push(Constant::Bool(false));
                self.emit(Instruction::LDI(false_vr.0, crate::core_types::Value::Bool(false)));
                self.emit(Instruction::CMP(condition_vr.0, false_vr.0)); // Compare condition == false

                let else_label = format!("else_{}", self.current_instructions.len());
                let end_label = format!("end_if_{}", self.current_instructions.len());

                // Jump to else when condition == false
                self.emit(Instruction::JMPEQ(else_label.clone()));

                // --- Then Branch ---
                let (then_vr, then_is_secret) = self.compile_node(then_branch)?;
                // Provisional result register uses then-branch secrecy; may be updated after else
                let mut result_is_secret = then_is_secret;
                let result_vr = self.allocate_virtual_register(result_is_secret);
                self.emit(Instruction::MOV(result_vr.0, then_vr.0));
                // Skip else branch after executing then branch
                self.emit(Instruction::JMP(end_label.clone()));

                // --- Else Branch ---
                self.add_label(else_label);
                let (else_vr, else_is_secret) = match else_branch.as_deref() {
                    Some(branch) => self.compile_node(branch)?,
                    None => {
                        // If no else, evaluate to Unit (clear)
                        let vr = self.allocate_virtual_register(false);
                        self.identified_constants.push(Constant::Unit);
                        self.emit(Instruction::LDI(vr.0, crate::core_types::Value::Unit));
                        (vr, false)
                    }
                };
                // Update secrecy if needed (result is secret if either branch is secret)
                let final_result_is_secret = result_is_secret || else_is_secret;
                if final_result_is_secret != result_is_secret {
                    // Update secrecy map so allocator places this VR into correct bank
                    self.vr_secrecy.insert(result_vr, final_result_is_secret);
                }
                self.emit(Instruction::MOV(result_vr.0, else_vr.0));

                // --- End Label ---
                self.add_label(end_label);
                Ok((result_vr, final_result_is_secret))
            },
            AstNode::Block(nodes) => {
                let mut last_vr = self.allocate_virtual_register(false); // Default VR for empty block (clear)
                let mut last_vr_is_secret = false;
                for node in nodes {
                    (last_vr, last_vr_is_secret) = self.compile_node(node)?;
                }
                Ok((last_vr, last_vr_is_secret))
            },
            AstNode::Return { value, location: _ } => {
                // Determine secrecy based on function signature's return type (TODO)
                let (value_vr, value_is_secret) = match value {
                    Some(v) => self.compile_node(v)?,
                    None => {
                        // Return Unit (assume clear default)
                        let vr = self.allocate_virtual_register(false);
                        self.identified_constants.push(Constant::Unit);
                        self.emit(Instruction::LDI(vr.0, crate::core_types::Value::Unit));
                        (vr, false)
                    }
                };
                // Return the value directly from its virtual register; the VM will place it in caller's R0.
                self.emit(Instruction::RET(value_vr.0));
                Ok((value_vr, value_is_secret)) // Return VR, though RET is terminal
            },
            AstNode::DiscardStatement { expression, location } => {
                let (vr, is_secret) = self.compile_node(expression)?;
                // The VR's live range ends here. Allocator handles it.
                Ok((vr, is_secret)) // Return the VR, but its value isn't used further
            },
            AstNode::FieldAccess { object, field_name, location } => {
                let (object_vr, object_is_secret) = self.compile_node(object)?;
                // Determine result secrecy based on field type (lookup needed)
                let result_is_secret = false; // TODO: Lookup field type
                let result_vr = self.allocate_virtual_register(result_is_secret);
                // We need to implement field access differently with the new instruction set
                Ok((result_vr, result_is_secret))
            },
            AstNode::WhileLoop { condition, body, location } => {
                let loop_start_label = format!("loop_start_{}", self.current_instructions.len());
                let end_loop_label = format!("loop_end_{}", self.current_instructions.len());

                // Define the label for the start of the loop (condition check)
                self.add_label(loop_start_label.clone());

                // Compile condition (assume clear for CMP/JMP)
                let (condition_vr, condition_is_secret) = self.compile_node(condition)?;
                if condition_is_secret {
                    return Err(CompilerError::semantic_error("Cannot use secret value as condition in 'while'", condition.location()));
                }

                // Compare the boolean condition VR against Bool(false)
                let false_vr = self.allocate_virtual_register(false); // false is clear
                self.identified_constants.push(Constant::Bool(false));
                self.emit(Instruction::LDI(false_vr.0, crate::core_types::Value::Bool(false)));
                self.emit(Instruction::CMP(condition_vr.0, false_vr.0)); // Compare condition == false

                self.emit(Instruction::JMPEQ(end_loop_label.clone()));
                // condition_vr, false_vr used up to here.

                let (_body_vr, _body_is_secret) = self.compile_node(body)?;
                // Result of body is discarded. Its live range ends.

                // Jump back to condition check
                self.emit(Instruction::JMP(loop_start_label));

                // Define the end label's position
                self.add_label(end_loop_label);

                // While loops evaluate to Unit
                let nil_vr = self.allocate_virtual_register(false); // Unit is clear
                self.identified_constants.push(Constant::Unit);
                self.emit(Instruction::LDI(nil_vr.0, crate::core_types::Value::Unit));
                Ok((nil_vr, false))
            },
            AstNode::ForLoop { variables, iterable, body, location } => {
                // Support: single var over range a .. b (inclusive), clear values only.
                if variables.len() != 1 {
                    return Err(CompilerError::semantic_error("For-loop with multiple variables not supported yet", location.clone()));
                }
                // Expect iterable to be a range binary operation
                let (start_expr, end_expr) = match iterable.as_ref() {
                    AstNode::BinaryOperation { op, left, right, location: _ } if op == ".." => (left, right),
                    _ => {
                        return Err(CompilerError::semantic_error("Unsupported for-loop iterable; expected 'a .. b' range", iterable.location()));
                    }
                };

                // Compile start and end expressions
                let (start_vr, start_is_secret) = self.compile_node(start_expr)?;
                let (end_vr, end_is_secret) = self.compile_node(end_expr)?;
                if start_is_secret || end_is_secret {
                    return Err(CompilerError::semantic_error("Secret values are not supported in for-loop range bounds", iterable.location()));
                }

                // Allocate loop variable (clear) and initialize with start
                let loop_vr = self.allocate_virtual_register(false);
                self.emit(Instruction::MOV(loop_vr.0, start_vr.0));

                // Insert loop variable into symbol table, saving any previous binding
                let var_name = variables[0].clone();
                let prev_binding = self.symbol_table.insert(var_name.clone(), loop_vr.0);

                // Labels
                let loop_start_label = format!("for_start_{}", self.current_instructions.len());
                let loop_end_label = format!("for_end_{}", self.current_instructions.len());

                // Start label
                self.add_label(loop_start_label.clone());

                // If i > end: exit
                self.emit(Instruction::CMP(loop_vr.0, end_vr.0));
                self.emit(Instruction::JMPGT(loop_end_label.clone()));

                // Body
                let (_body_vr, _body_is_secret) = self.compile_node(body)?;

                // i = i + 1
                let one_vr = self.allocate_virtual_register(false);
                let one_val = crate::core_types::Value::from(Constant::I64(1));
                self.identified_constants.push(Constant::I64(1));
                self.emit(Instruction::LDI(one_vr.0, one_val));
                self.emit(Instruction::ADD(loop_vr.0, loop_vr.0, one_vr.0));

                // Keep the upper bound (end_vr) live across the body to avoid clobbering by temps
                let end_keepalive = self.allocate_virtual_register(false);
                self.emit(Instruction::MOV(end_keepalive.0, end_vr.0));

                // Jump back
                self.emit(Instruction::JMP(loop_start_label));

                // End label
                self.add_label(loop_end_label);

                // Restore/cleanup symbol table mapping
                match prev_binding {
                    Some(old_idx) => { self.symbol_table.insert(var_name, old_idx); },
                    None => { self.symbol_table.remove(&variables[0]); }
                }

                // For-loops evaluate to Unit
                let nil_vr = self.allocate_virtual_register(false);
                self.identified_constants.push(Constant::Unit);
                self.emit(Instruction::LDI(nil_vr.0, crate::core_types::Value::Unit));
                Ok((nil_vr, false))
            },
            AstNode::FunctionDefinition { name, parameters, return_type, body, is_secret, pragmas, location, node_id } => {
                // --- Check for Pragmas ---
                let mut skip_compilation = false;
                for pragma in pragmas {
                    let pragma_name = match pragma {
                        Pragma::Simple(name, _) => name,
                        Pragma::KeyValue(name, _, _) => name,
                    };

                    if let Some(handler) = self.pragma_handlers.get(pragma_name) {
                        handler(self, node, pragma)?;
                        // Check if the handler indicates compilation should be skipped
                        if pragma_name == "builtin" {
                            // Register the function name as a known built-in.
                            if let Some(name) = name {
                                self.known_builtins.insert(name.clone());
                            }
                            skip_compilation = true;
                        }
                    }
                }
                if skip_compilation {
                    return Ok((VirtualRegister(usize::MAX), false)); // Indicate success, no VR
                }
                // --- Compile the function body ---
                let mut function_generator = CodeGenerator::new();

                // --- Add parameters to the function_generator's symbol table ---
                let mut param_vrs: Vec<VirtualRegister> = Vec::new();
                for (i, param) in parameters.iter().enumerate() {
                    // Determine parameter secrecy from its type annotation
                    let param_type = param.type_annotation.as_ref()
                        .map(|n| SymbolType::from_ast(n))
                        .unwrap_or(SymbolType::Unknown);
                    let param_is_secret = param_type.is_secret();
                    // Allocate a virtual register for the parameter. These will typically
                    let param_vr = function_generator.allocate_virtual_register(param_is_secret);
                    function_generator.symbol_table.insert(param.name.clone(), param_vr.0); // Store VR index
                    param_vrs.push(param_vr);
                }

                // Compile the function body using the new generator.
                let (_body_result_reg, _body_is_secret) = function_generator.compile_node(body)?;

                // --- Perform Register Allocation ---
                let virtual_instructions = function_generator.current_instructions;
                let intervals = register_allocator::analyze_liveness_cfg_with_liveins(&virtual_instructions, &function_generator.current_labels, &param_vrs);
                let graph = register_allocator::build_interference_graph(&intervals);

                let k_clear = SECRET_REGISTER_START;
                let k_secret = MAX_REGISTERS - k_clear;
                let secrecy_map = function_generator.vr_secrecy;

                // Precolor parameter VRs to ABI registers R0..Rn-1
                let mut precolored: HashMap<VirtualRegister, PhysicalRegister> = HashMap::new();
                for (i, vr) in param_vrs.iter().enumerate() {
                    precolored.insert(*vr, PhysicalRegister(i));
                }

                let allocation_result = register_allocator::color_graph(&graph, k_clear, k_secret, &secrecy_map, &precolored);
                let allocation = match allocation_result {
                    Ok(alloc) => alloc,
                    Err(AllocationError::NeedsSpilling(spilled_vrs)) => {
                        // Basic error handling for now. Real implementation needs spilling logic.
                        return Err(CompilerError::internal_error(format!(
                            "Register allocation failed for function '{}': Need to spill registers {:?}",
                            name.as_deref().unwrap_or("<anon>"), spilled_vrs
                        )).with_hint("Spilling not yet implemented. Try simplifying the function."));
                    }
                    Err(AllocationError::PoolExhausted(_, _)) => return Err(CompilerError::internal_error("Register allocation failed: Pool exhausted".to_string())),
                };

                // Rewrite instructions with physical registers
                let final_instructions = register_allocator::rewrite_instructions(&virtual_instructions, &allocation);

                // Finalize the function's bytecode chunk.
                let mut function_chunk = BytecodeChunk::new();
                function_chunk.instructions = final_instructions;
                function_chunk.labels = function_generator.current_labels; // TODO: Adjust label indices after rewrite/spilling?
                function_chunk.constants = dedupe_constants(function_generator.identified_constants);

                // Store the compiled chunk appropriately.
                if let Some(func_name) = name {
                    if func_name == "main" && return_type.is_none() {
                        // Treat 'proc main()' as the program's main chunk.
                        if self.main_proc_chunk.is_some() {
                            return Err(CompilerError::semantic_error(
                                "Multiple 'main' procedures defined".to_string(),
                                location.clone()
                            ));
                        }
                        self.main_proc_chunk = Some(function_chunk);
                    } else {
                        if self.compiled_functions.contains_key(func_name) {
                            // TODO: Allow overloading later?
                            return Err(CompilerError::semantic_error(format!("Function '{}' already defined", func_name), location.clone()));
                        }
                        self.compiled_functions.insert(func_name.clone(), function_chunk);
                    }
                } else {
                    // TODO: Handle anonymous functions (lambdas)
                    return Err(CompilerError::internal_error("Anonymous function definition not yet supported".to_string()));
                }

                // Function definition itself doesn't produce a value in the outer scope.
                Ok((VirtualRegister(usize::MAX), false)) // Return dummy VR
            },
            _ => todo!(),
        }
    }

    /// Finalizes the entire compiled program, including the main chunk and all function chunks.
    fn finalize_program(mut self) -> CompilerResult<CompiledProgram> {
        // If a 'proc main()' was compiled, prefer it as main only when there are no top-level instructions.
        if let Some(main_proc) = self.main_proc_chunk.take() {
            if self.current_instructions.is_empty() {
                return Ok(CompiledProgram {
                    main_chunk: main_proc,
                    function_chunks: self.compiled_functions,
                });
            } else {
                // Preserve the compiled main proc as a normal function.
                self.compiled_functions.insert("main".to_string(), main_proc);
            }
        }

        // If there are no top-level instructions but a 'main' function exists,
        // insert a call to 'main' so the program entry has executable bytecode.
        if self.current_instructions.is_empty() && self.compiled_functions.contains_key("main") {
            self.current_instructions.push(Instruction::CALL("main".to_string()));
        }
        // Perform register allocation for the main chunk's instructions
        let main_instructions = self.current_instructions; // Instructions generated for the main body
        let intervals = register_allocator::analyze_liveness_cfg_with_liveins(&main_instructions, &self.current_labels, &[]);
        let graph = register_allocator::build_interference_graph(&intervals);

        let k_clear = SECRET_REGISTER_START;
        let k_secret = MAX_REGISTERS - k_clear;
        let secrecy_map = self.vr_secrecy;
        // No precolored mapping for top-level/main chunk
        let empty_pre: HashMap<VirtualRegister, PhysicalRegister> = HashMap::new();
        let allocation_result = register_allocator::color_graph(&graph, k_clear, k_secret, &secrecy_map, &empty_pre);
        let allocation = match allocation_result {
            Ok(alloc) => alloc,
            Err(AllocationError::NeedsSpilling(spilled_vrs)) => {
                // Basic error handling for now. Real implementation needs spilling logic.
                return Err(CompilerError::internal_error(format!(
                    "Register allocation failed for main program body: Need to spill registers {:?}",
                    spilled_vrs
                )).with_hint("Spilling not yet implemented."));
            }
            Err(AllocationError::PoolExhausted(_, _)) => return Err(CompilerError::internal_error("Register allocation failed: Pool exhausted".to_string())),
        };

        let final_main_instructions = register_allocator::rewrite_instructions(&main_instructions, &allocation);
        let mut main_chunk = BytecodeChunk::new();
        main_chunk.instructions = final_main_instructions;
        main_chunk.labels = self.current_labels; // TODO: Adjust label indices?
        main_chunk.constants = dedupe_constants(self.identified_constants);

        Ok(CompiledProgram {
            main_chunk,
            function_chunks: self.compiled_functions,
        })
    }
}

// --- Pragma Handler Implementations ---

/// Handles the `{.builtin.}` pragma.
/// This function is called when the "builtin" pragma is encountered during code generation.
fn handle_builtin_pragma(
    _generator: &mut CodeGenerator, // We need this to register the name
    _func_def_node: &AstNode,      // The FunctionDefinition node
    _pragma: &Pragma,              // The specific pragma node
) -> CompilerResult<()> {
    // The core logic for 'builtin' is simply *not* compiling the body.
    Ok(())
}

fn dedupe_constants(constants: Vec<Constant>) -> Vec<Constant> {
    use std::collections::HashSet;
    let mut seen: HashSet<crate::core_types::Value> = HashSet::new();
    let mut out = Vec::with_capacity(constants.len());
    for c in constants.into_iter() {
        let v = crate::core_types::Value::from(c.clone());
        if seen.insert(v) {
            out.push(c);
        }
    }
    out
}

pub fn generate_bytecode(node: &AstNode) -> CompilerResult<CompiledProgram> {
    let mut generator = CodeGenerator::new();
    let (_result_vr, _result_is_secret) = generator.compile_node(node)?;
    generator.finalize_program()
}

#[cfg(test)]
mod tests {
    use super::{dedupe_constants, Constant};

    #[test]
    fn dedupe_removes_duplicates_and_preserves_order() {
        let input = vec![
            Constant::I64(1),
            Constant::Bool(true),
            Constant::I64(1),           // dup
            Constant::String("a".into()),
            Constant::String("a".into()), // dup
            Constant::Unit,
            Constant::Unit,               // dup
            Constant::Bool(true),         // dup
            Constant::I64(2),
        ];

        let out = dedupe_constants(input);

        assert_eq!(out.len(), 5, "Expected 5 unique constants");
        assert!(matches!(out[0], Constant::I64(1)));
        assert!(matches!(out[1], Constant::Bool(true)));
        assert!(matches!(out[2], Constant::String(ref s) if s == "a"));
        assert!(matches!(out[3], Constant::Unit));
        assert!(matches!(out[4], Constant::I64(2)));
    }
}
