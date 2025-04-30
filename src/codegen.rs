use crate::ast::{AstNode, Pragma};
use crate::bytecode::{BytecodeChunk, CompiledProgram, Constant, Instruction};
use crate::errors::{CompilerError, CompilerResult};
use crate::register_allocator::{self, AllocationError, VirtualRegister};
use crate::symbol_table::SymbolType;

use std::collections::HashMap;
use std::collections::HashSet;
const MAX_REGISTERS: usize = 64; // Example limit
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
    // Known built-in functions (names only, no bytecode generated).
    known_builtins: HashSet<String>,
    // Pragma handlers: Maps pragma names to their handler functions.
    pragma_handlers: HashMap<String, PragmaHandler>,
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
            known_builtins: HashSet::new(),
            pragma_handlers: Self::register_pragma_handlers(),
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
                    crate::ast::Value::Int(i) => Constant::Int(*i),
                    crate::ast::Value::Float(f) => Constant::Float(*f),
                    crate::ast::Value::String(s) => Constant::String(s.clone()),
                    crate::ast::Value::Bool(b) => Constant::Bool(*b),
                    crate::ast::Value::Nil => Constant::Nil,
                };
                // Convert Constant to Value
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
                        self.emit(Instruction::LDI(vr.0, crate::core_types::Value::Nil)); // Load Nil
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
                                self.emit(Instruction::LDI(bool_dest_vr.0, crate::core_types::Value::Bool(false)));
                                self.emit(Instruction::JMP(end_label.clone()));

                                // Define the true label's position
                                self.add_label(true_label);
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
                                self.emit(Instruction::LDI(bool_dest_vr.0, crate::core_types::Value::Bool(true)));
                                self.emit(Instruction::JMP(end_label.clone()));

                                // Define the false label's position
                                self.add_label(false_label);
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

                // 3. Compile arguments
                let mut arg_vrs = Vec::with_capacity(arguments.len());
                for arg in arguments {
                    let (arg_vr, arg_is_secret) = self.compile_node(arg)?;
                    self.emit(Instruction::PUSHARG(arg_vr.0));
                    arg_vrs.push(arg_vr);
                }

                // 4. Determine result type and secrecy from resolved type (added by semantic analysis)
                let return_type = resolved_return_type.as_ref().cloned()
                    .unwrap_or_else(|| {
                        // Should not happen if semantic analysis ran correctly
                        eprintln!("Warning: Function call node missing resolved return type during codegen for '{}'", function_name);
                        SymbolType::Unknown
                    });

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
                self.emit(Instruction::LDI(false_vr.0, crate::core_types::Value::Bool(false)));
                self.emit(Instruction::CMP(condition_vr.0, false_vr.0)); // Compare condition == false

                let else_label = format!("else_{}", self.current_instructions.len());
                let end_label = format!("end_if_{}", self.current_instructions.len());

                self.emit(Instruction::JMPEQ(else_label.clone()));
                // condition_vr and false_vr are used up to this point.

                // Compile then branch
                let (then_vr, then_is_secret) = self.compile_node(then_branch)?;

                // Compile else branch (or load nil)
                let (else_vr, else_is_secret) = match else_branch.as_deref() {
                    Some(branch) => self.compile_node(branch)?,
                    None => {
                        // If no else, result type depends only on then branch.
                        let vr = self.allocate_virtual_register(then_is_secret);
                        self.emit(Instruction::LDI(vr.0, crate::core_types::Value::Nil));
                        (vr, then_is_secret)
                    }
                };

                // Result secrecy is secret if EITHER branch is secret
                let result_is_secret = then_is_secret || else_is_secret;
                let result_vr = self.allocate_virtual_register(result_is_secret);

                // --- Then Branch Logic ---
                self.emit(Instruction::MOV(result_vr.0, then_vr.0)); // Move result from then branch
                self.emit(Instruction::JMP(end_label.clone()));

                // Define the else label's position
                self.add_label(else_label);
                // --- Else Branch Logic ---
                self.emit(Instruction::MOV(result_vr.0, else_vr.0)); // Move result from else branch

                // Define the end label's position
                self.add_label(end_label);
                Ok((result_vr, result_is_secret)) // Return the VR holding the result
            },
            AstNode::Block(nodes) => {
                let mut last_vr = self.allocate_virtual_register(false); // Default VR for empty block (clear)
                let mut last_vr_is_secret = false;
                for node in nodes {
                    (last_vr, last_vr_is_secret) = self.compile_node(node)?;
                }
                Ok((last_vr, last_vr_is_secret))
            },
            AstNode::Return(value) => {
                // Determine secrecy based on function signature's return type (TODO)
                let (value_vr, value_is_secret) = match value {
                    Some(v) => self.compile_node(v)?,
                    None => {
                        // Return Nil (assume clear default)
                        let vr = self.allocate_virtual_register(false);
                        self.emit(Instruction::LDI(vr.0, crate::core_types::Value::Nil));
                        (vr, false)
                    }
                };
                // Move the return value into the conventional return register (physical r0)
                self.emit(Instruction::MOV(0, value_vr.0));
                self.emit(Instruction::RET(0)); // Use RET 0 convention
                // value_vr is used by RET.
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

                // While loops evaluate to Nil
                let nil_vr = self.allocate_virtual_register(false); // Nil is clear
                self.emit(Instruction::LDI(nil_vr.0, crate::core_types::Value::Nil));
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
                for (i, param) in parameters.iter().enumerate() {
                    // Determine parameter secrecy from its type annotation
                    let param_type = param.type_annotation.as_ref()
                        .map(|n| SymbolType::from_ast(n))
                        .unwrap_or(SymbolType::Unknown);
                    let param_is_secret = param_type.is_secret();
                    // Allocate a virtual register for the parameter. These will typically
                    let param_vr = function_generator.allocate_virtual_register(param_is_secret);
                    function_generator.symbol_table.insert(param.name.clone(), param_vr.0); // Store VR index
                }

                // Compile the function body using the new generator.
                let (_body_result_reg, _body_is_secret) = function_generator.compile_node(body)?;

                // --- Perform Register Allocation ---
                let virtual_instructions = function_generator.current_instructions;
                let intervals = register_allocator::analyze_liveness(&virtual_instructions);
                let graph = register_allocator::build_interference_graph(&intervals);

                let k_clear = SECRET_REGISTER_START;
                let k_secret = MAX_REGISTERS - k_clear;
                let secrecy_map = function_generator.vr_secrecy;

                let allocation_result = register_allocator::color_graph(&graph, k_clear, k_secret, &secrecy_map);
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
                let final_instructions = register_allocator::rewrite_instructions(&virtual_instructions, &allocation, k_clear);

                // Finalize the function's bytecode chunk.
                let mut function_chunk = BytecodeChunk::new();
                function_chunk.instructions = final_instructions;
                function_chunk.labels = function_generator.current_labels; // TODO: Adjust label indices after rewrite/spilling?

                // Store the compiled chunk in the main generator's map.
                if let Some(func_name) = name {
                    if self.compiled_functions.contains_key(func_name) {
                        // TODO: Allow overloading later?
                        return Err(CompilerError::semantic_error(format!("Function '{}' already defined", func_name), location.clone()));
                    }
                    self.compiled_functions.insert(func_name.clone(), function_chunk);
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
        // Add a default RET instruction at the end of the main chunk if needed.
        // Perform register allocation for the main chunk's instructions
        let main_instructions = self.current_instructions; // Instructions generated for the main body
        let intervals = register_allocator::analyze_liveness(&main_instructions);
        let graph = register_allocator::build_interference_graph(&intervals);

        let k_clear = SECRET_REGISTER_START;
        let k_secret = MAX_REGISTERS - k_clear;
        let secrecy_map = self.vr_secrecy;
        let allocation_result = register_allocator::color_graph(&graph, k_clear, k_secret, &secrecy_map);
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

        let final_main_instructions = register_allocator::rewrite_instructions(&main_instructions, &allocation, k_clear);
        let mut main_chunk = BytecodeChunk::new();
        main_chunk.instructions = final_main_instructions;
        main_chunk.labels = self.current_labels; // TODO: Adjust label indices?

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

pub fn generate_bytecode(node: &AstNode) -> CompilerResult<CompiledProgram> {
    let mut generator = CodeGenerator::new();
    let (_result_vr, _result_is_secret) = generator.compile_node(node)?;
    generator.finalize_program()
}
