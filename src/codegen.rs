use crate::ast::AstNode;
use crate::bytecode::{BytecodeChunk, Instruction, Constant, Operand};
use crate::errors::{CompilerError, SourceLocation, CompilerResult};

const MAX_REGISTERS: usize = 64; // Example limit

#[derive(Debug)]
struct CodeGenerator {
    chunk: BytecodeChunk,
    // Tracks which registers are currently free (true) or used (false).
    free_registers: Vec<bool>,
    // Add symbol table, scope management, etc.
}

impl CodeGenerator {
    fn new() -> Self {
        CodeGenerator {
            chunk: BytecodeChunk::new(),
            free_registers: vec![true; MAX_REGISTERS],
        }
    }

    // Finds the first available register, marks it as used, and returns it.
    fn allocate_register(&mut self) -> CompilerResult<usize> {
        for (i, is_free) in self.free_registers.iter_mut().enumerate() {
            if *is_free {
                *is_free = false;
                return Ok(i);
            }
        }
        Err(CompilerError::internal_error("Register allocation failed: Out of registers")
            .with_hint("The program is too complex and requires more registers than available"))
    }

    // Marks a specific register as free.
    fn free_register(&mut self, reg: usize) {
        if reg < self.free_registers.len() {
            if self.free_registers[reg] {
                // Optionally warn or error if freeing an already free register
                // eprintln!("Warning: Attempting to free already free register {}", reg);
            }
            self.free_registers[reg] = true;
        } else {
            // Optionally error if freeing an invalid register index
            eprintln!("Error: Attempting to free invalid register index {}", reg);
        }
    }

    fn compile_node(&mut self, node: &AstNode) -> CompilerResult<usize> {
        match node {
            AstNode::Literal(lit) => {
                let reg = self.allocate_register()?;
                let constant = match lit {
                    crate::ast::Literal::Int(i) => Constant::Int(*i),
                    crate::ast::Literal::Float(f) => Constant::Float(*f),
                    crate::ast::Literal::String(s) => Constant::String(s.clone()),
                    crate::ast::Literal::Bool(b) => Constant::Bool(*b),
                    crate::ast::Literal::Nil => Constant::Nil,
                };
                // Convert Constant to Value
                let value = crate::core_types::Value::from(constant);
                self.chunk.add_instruction(Instruction::LDI(reg, value));
                Ok(reg)
            }
            AstNode::Identifier(name) => {
                let reg = self.allocate_register()?;
                // Look up identifier in symbol table (local, global?)
                // For now, assume global
                let name_idx = self.chunk.add_constant(Constant::String(name.clone()));

                // This is a simplification - in a real implementation, we'd need to handle
                // global variable lookup differently, possibly with a dedicated instruction
                // For now, we'll just load a constant with the name
                let value = crate::core_types::Value::String(name.clone());
                self.chunk.add_instruction(Instruction::LDI(reg, value));

                Ok(reg)
            }
            AstNode::BinaryOperation { op, left, right } => {
                let left_reg = self.compile_node(left)?;
                let right_reg = self.compile_node(right)?;
                // We can reuse the left register for the destination.
                // The right register can be freed immediately after the operation.
                let dest_reg = left_reg;

                let instruction = match op.as_str() {
                    "+" => Instruction::ADD(dest_reg, left_reg, right_reg),
                    "-" => Instruction::SUB(dest_reg, left_reg, right_reg),
                    "*" => Instruction::MUL(dest_reg, left_reg, right_reg),
                    "/" => Instruction::DIV(dest_reg, left_reg, right_reg),
                    "==" => {
                        self.chunk.add_instruction(Instruction::CMP(left_reg, right_reg));
                        Instruction::JMPEQ(format!("cmp_true_{}", self.chunk.instructions.len()))
                    },
                    _ => return Err(CompilerError::semantic_error(format!("Unsupported binary operator: {}", op), SourceLocation::default())
                        .with_hint(format!("Supported operators are: +, -, *, /, =="))),
                };
                self.chunk.add_instruction(instruction);
                self.free_register(right_reg); // Free the right operand's register
                Ok(dest_reg)
            }
            AstNode::Assignment { target, value } => {
                let value_reg = self.compile_node(value)?;
                match target.as_ref() {
                    AstNode::Identifier(name) => {
                        // In the new instruction set, we don't have a direct SetGlobal instruction
                        // We would need to implement global variable storage differently
                        // For now, we'll just move the value to a register (simplified)
                        let dest_reg = self.allocate_register()?;
                        self.chunk.add_instruction(Instruction::MOV(dest_reg, value_reg));
                        self.free_register(dest_reg);
                        
                        // Value register is no longer needed after SetGlobal
                        self.free_register(value_reg);
                        Ok(value_reg) // Return the register, though it's now free
                    }
                    AstNode::FieldAccess { object, field_name } => {
                        let object_reg = self.compile_node(object)?;
                        let field_idx = self.chunk.add_constant(Constant::String(field_name.clone()));
                        // We don't have a direct SetField instruction in the new set
                        // This would need custom implementation
                        
                        self.free_register(value_reg); // Free value reg after SetField
                        self.free_register(object_reg); // Free object reg after SetField
                        Ok(object_reg) // Return object reg, though it's now free
                    }
                    _ => return Err(CompilerError::semantic_error("Invalid assignment target", SourceLocation::default())),
                }
            }
            AstNode::FunctionCall { function, arguments } => {
                let function_reg = self.compile_node(function)?;
                let mut arg_regs = Vec::with_capacity(arguments.len());
                for arg in arguments {
                    let arg_reg = self.compile_node(arg)?;
                    arg_regs.push(arg_reg);
                }
                let result_reg = self.allocate_register()?;
                
                // In the new instruction set, CALL takes a function name (string)
                // We'll need to extract the function name from the function_reg
                // For simplicity, we'll just use a placeholder function name
                self.chunk.add_instruction(Instruction::CALL("function_placeholder".to_string()));
                self.chunk.add_instruction(Instruction::MOV(result_reg, 0)); // Assume result is in r0

                // Free argument registers and the function register *after* the call
                self.free_register(function_reg);
                for reg in arg_regs {
                    self.free_register(reg);
                }
                Ok(result_reg)
            }
            AstNode::IfExpression { condition, then_branch, else_branch } => {
                let condition_reg = self.compile_node(condition)?;

                // Generate unique labels for jumps
                let else_label = format!("else_{}", self.chunk.instructions.len());
                let end_label = format!("end_if_{}", self.chunk.instructions.len());
                
                // Compare condition with false and jump to else branch if equal
                self.chunk.add_instruction(Instruction::CMP(condition_reg, 0)); // Assuming 0 is false
                self.chunk.add_instruction(Instruction::JMPEQ(else_label.clone()));

                // Compile then branch
                let then_reg = self.compile_node(then_branch)?;
                self.chunk.add_instruction(Instruction::MOV(condition_reg, then_reg));
                let else_label = self.chunk.add_instruction(Instruction::JMP(end_label.clone()));

                // Patch jump to else/end
                self.patch_jump(else_label, (self.chunk.instructions.len() - else_label - 1) as i16);

                // Compile else branch (or load nil)
                let else_reg = match else_branch {
                    Some(branch) => self.compile_node(branch)?,
                    None => {
                        let reg = self.allocate_register()?;
                        self.chunk.add_instruction(Instruction::LDI(reg, crate::core_types::Value::Nil));
                    }
                };
                self.chunk.add_instruction(Instruction::MOV(condition_reg, else_reg));
                self.free_register(else_reg); // Free else_reg after move

                // Patch jump over else branch
                self.patch_jump(else_label, (self.chunk.instructions.len() - else_label - 1) as i16);
                // The result of the if expression is now in condition_reg
                Ok(condition_reg)
            }
            AstNode::Block(nodes) => {
                let mut last_reg = 0;
                for node in nodes {
                    last_reg = self.compile_node(node)?;
                }
                // TODO: Free registers from intermediate statements within the block
                // This requires more sophisticated liveness analysis or freeing conventions.
                // For now, assume the last expression's register is the block's result.
                Ok(last_reg)
            }
            AstNode::Return(value) => {
                let value_reg = match value {
                    Some(v) => self.compile_node(v)?,
                    None => {
                        let reg = self.allocate_register()?;
                        self.chunk.add_instruction(Instruction::LDI(reg, crate::core_types::Value::Nil));
                        reg
                    }
                };
                self.chunk.add_instruction(Instruction::RET(value_reg));
                self.free_register(value_reg); // Value register is consumed by Return
                Ok(value_reg)
            }
            AstNode::FieldAccess { object, field_name } => {
                let object_reg = self.compile_node(object)?;
                let field_idx = self.chunk.add_constant(Constant::String(field_name.clone()));
                let result_reg = self.allocate_register()?;
                // We need to implement field access differently with the new instruction set
                self.free_register(object_reg); // Free object register after GetField
                Ok(result_reg)
            }
            AstNode::WhileLoop { condition, body } => {
                let loop_start_pos = self.chunk.instructions.len();
                let condition_reg = self.compile_node(condition)?;
                let jump_end_label = self.chunk.add_instruction(Instruction::JMPEQ(format!("end_loop_{}", self.chunk.instructions.len())));

                let body_reg = self.compile_node(body)?;
                self.free_register(body_reg); // Free the result of the body, it's not used

                // Jump back to condition check
                self.chunk.add_instruction(Instruction::JMP(format!("loop_{}", loop_start_pos)));

                // Patch the jump to the end of the loop
                self.patch_jump(jump_end_label, (self.chunk.instructions.len() - jump_end_label - 1) as i16);
                self.free_register(condition_reg); // Condition register is no longer needed after the loop
                // While loops evaluate to Nil
                let nil_reg = self.allocate_register()?;
                self.chunk.add_instruction(Instruction::LDI(nil_reg, crate::core_types::Value::Nil));
                Ok(nil_reg)
            }
            _ => Err(CompilerError::internal_error(format!("Codegen not implemented for {:?}", node))),
        }
    }

    fn patch_jump(&mut self, label: usize, offset: i16) {
        // This method needs to be completely rewritten for the new instruction set
        // which uses string labels instead of offsets
    }

    fn finalize(mut self) -> BytecodeChunk {
        // Add a return instruction at the end
        self.chunk
    }
}

pub fn generate_bytecode(node: &AstNode) -> CompilerResult<BytecodeChunk> {
    let mut generator = CodeGenerator::new();
    let _result_reg = generator.compile_node(node)?;
    // Potentially handle the final result register if the root node is an expression
    Ok(generator.finalize())
}
