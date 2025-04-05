use crate::ast::AstNode;
use crate::bytecode::{BytecodeChunk, BytecodeInstruction, Constant, Register};
use std::fmt;

#[derive(Debug, Clone, PartialEq)]
pub struct CodegenError {
    pub message: String,
    // Potentially add AST node location info
}

impl fmt::Display for CodegenError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Codegen Error: {}", self.message)
    }
}

impl std::error::Error for CodegenError {}

struct CodeGenerator {
    chunk: BytecodeChunk,
    next_register: Register,
    // Add symbol table, scope management, etc.
}

impl CodeGenerator {
    fn new() -> Self {
        CodeGenerator {
            chunk: BytecodeChunk::new(),
            next_register: 0,
        }
    }

    fn allocate_register(&mut self) -> Register {
        let reg = self.next_register;
        self.next_register += 1;
        // Handle register exhaustion
        reg
    }

    fn free_register(&mut self) {
        // Simple register freeing for now
        if self.next_register > 0 {
            self.next_register -= 1;
        }
    }

    fn compile_node(&mut self, node: &AstNode) -> Result<Register, CodegenError> {
        match node {
            AstNode::Literal(lit) => {
                let reg = self.allocate_register();
                let constant = match lit {
                    crate::ast::Literal::Int(i) => Constant::Int(*i),
                    crate::ast::Literal::Float(f) => Constant::Float(*f),
                    crate::ast::Literal::String(s) => Constant::String(s.clone()),
                    crate::ast::Literal::Bool(b) => Constant::Bool(*b),
                    crate::ast::Literal::Nil => Constant::Nil,
                };
                let const_idx = self.chunk.add_constant(constant);
                self.chunk.add_instruction(BytecodeInstruction::LoadConst { dest: reg, index: const_idx });
                Ok(reg)
            }
            AstNode::Identifier(name) => {
                 let reg = self.allocate_register();
                 // Look up identifier in symbol table (local, global?)
                 // For now, assume global
                 let name_idx = self.chunk.add_constant(Constant::String(name.clone()));
                 self.chunk.add_instruction(BytecodeInstruction::GetGlobal { dest: reg, name_idx });
                 Ok(reg)
            }
            AstNode::BinaryOperation { op, left, right } => {
                let left_reg = self.compile_node(left)?;
                let right_reg = self.compile_node(right)?;
                let dest_reg = left_reg; // Reuse left register for result

                let instruction = match op.as_str() {
                    "+" => BytecodeInstruction::Add { dest: dest_reg, lhs: left_reg, rhs: right_reg },
                    "-" => BytecodeInstruction::Subtract { dest: dest_reg, lhs: left_reg, rhs: right_reg },
                    "*" => BytecodeInstruction::Multiply { dest: dest_reg, lhs: left_reg, rhs: right_reg },
                    "/" => BytecodeInstruction::Divide { dest: dest_reg, lhs: left_reg, rhs: right_reg },
                    "==" => BytecodeInstruction::Equal { dest: dest_reg, lhs: left_reg, rhs: right_reg },
                    "!=" => BytecodeInstruction::NotEqual { dest: dest_reg, lhs: left_reg, rhs: right_reg },
                    ">" => BytecodeInstruction::Greater { dest: dest_reg, lhs: left_reg, rhs: right_reg },
                    ">=" => BytecodeInstruction::GreaterEqual { dest: dest_reg, lhs: left_reg, rhs: right_reg },
                    "<" => BytecodeInstruction::Less { dest: dest_reg, lhs: left_reg, rhs: right_reg },
                    "<=" => BytecodeInstruction::LessEqual { dest: dest_reg, lhs: left_reg, rhs: right_reg },
                    _ => return Err(CodegenError { message: format!("Unsupported binary operator: {}", op) }),
                };
                self.chunk.add_instruction(instruction);
                self.free_register(); // Free the right register
                Ok(dest_reg)
            }
            AstNode::Assignment { target, value } => {
                let value_reg = self.compile_node(value)?;
                match target.as_ref() {
                    AstNode::Identifier(name) => {
                        let name_idx = self.chunk.add_constant(Constant::String(name.clone()));
                        self.chunk.add_instruction(BytecodeInstruction::SetGlobal { name_idx, src: value_reg });
                    }
                    AstNode::FieldAccess { object, field_name } => {
                        let object_reg = self.compile_node(object)?;
                        let field_idx = self.chunk.add_constant(Constant::String(field_name.clone()));
                        self.chunk.add_instruction(BytecodeInstruction::SetField { object: object_reg, field_idx, src: value_reg });
                    }
                    _ => return Err(CodegenError { message: "Invalid assignment target".to_string() }),
                }
                self.free_register(); // Free the value register
                Ok(value_reg)
            }
            AstNode::FunctionCall { function, arguments } => {
                let function_reg = self.compile_node(function)?;
                let mut arg_regs = Vec::with_capacity(arguments.len());
                for arg in arguments {
                    let arg_reg = self.compile_node(arg)?;
                    arg_regs.push(arg_reg);
                }
                let result_reg = self.allocate_register();
                // Assume function is a global function for now
                let function_id = 0; // TODO: Look up function ID
                self.chunk.add_instruction(BytecodeInstruction::Call { dest: result_reg, function: function_id, args: arg_regs });
                //todo: fixme!
                self.free_registers(&arg_regs);
                Ok(result_reg)
            }
            AstNode::IfExpression { condition, then_branch, else_branch } => {
                let condition_reg = self.compile_node(condition)?;
                let then_reg = self.compile_node(then_branch)?;
                let else_reg = match else_branch {
                    Some(branch) => self.compile_node(branch)?,
                    None => {
                        let reg = self.allocate_register();
                        self.chunk.add_instruction(BytecodeInstruction::LoadConst { dest: reg, index: self.chunk.add_constant(Constant::Nil) });
                        reg
                    }
                };

                let then_label = self.chunk.add_instruction(BytecodeInstruction::JumpIfFalse { condition: condition_reg, offset: 0 });
                self.chunk.add_instruction(BytecodeInstruction::Move { dest: condition_reg, src: then_reg });
                let else_label = self.chunk.add_instruction(BytecodeInstruction::Jump { offset: 0 });
                self.patch_jump(then_label, (self.chunk.instructions.len() - then_label - 1) as i16);
                self.chunk.add_instruction(BytecodeInstruction::Move { dest: condition_reg, src: else_reg });
                self.patch_jump(else_label, (self.chunk.instructions.len() - else_label - 1) as i16);
                Ok(condition_reg)
            }
            AstNode::WhileLoop { condition, body } => {
                let condition_label = self.chunk.instructions.len();
                let condition_reg = self.compile_node(condition)?;
                let body_label = self.chunk.add_instruction(BytecodeInstruction::JumpIfFalse { condition: condition_reg, offset: 0 });
                self.compile_node(body)?;
                self.chunk.add_instruction(BytecodeInstruction::Jump { offset: (condition_label - self.chunk.instructions.len() - 1) as i16 });
                self.patch_jump(body_label, (self.chunk.instructions.len() - body_label - 1) as i16);
                self.free_register(); // Free the condition register
                Ok(condition_reg)
            }
            AstNode::Block(nodes) => {
                let mut last_reg = 0;
                for node in nodes {
                    last_reg = self.compile_node(node)?;
                }
                Ok(last_reg)
            }
            AstNode::Return(value) => {
                let value_reg = match value {
                    Some(v) => self.compile_node(v)?,
                    None => {
                        let reg = self.allocate_register();
                        self.chunk.add_instruction(BytecodeInstruction::LoadConst { dest: reg, index: self.chunk.add_constant(Constant::Nil) });
                        reg
                    }
                };
                self.chunk.add_instruction(BytecodeInstruction::Return { src: value_reg });
                self.free_register(); // Free the return value register
                Ok(value_reg)
            }
            AstNode::ObjectConstruction { type_name, fields } => {
                let type_idx = self.chunk.add_constant(Constant::String(type_name.clone()));
                let object_reg = self.allocate_register();
                self.chunk.add_instruction(BytecodeInstruction::MakeObject { dest: object_reg, type_idx });

                for (field_name, field_value) in fields {
                    let field_idx = self.chunk.add_constant(Constant::String(field_name.clone()));
                    let field_value_reg = self.compile_node(&field_value)?;
                    self.chunk.add_instruction(BytecodeInstruction::SetField { object: object_reg, field_idx, src: field_value_reg });
                    self.free_register(); // Free the field value register
                }

                Ok(object_reg)
            }
            AstNode::FieldAccess { object, field_name } => {
                let object_reg = self.compile_node(object)?;
                let field_idx = self.chunk.add_constant(Constant::String(field_name.clone()));
                let result_reg = self.allocate_register();
                self.chunk.add_instruction(BytecodeInstruction::GetField { dest: result_reg, object: object_reg, field_idx });
                self.free_register(); // Free the object register
                Ok(result_reg)
            }
            _ => Err(CodegenError { message: format!("Codegen not implemented for {:?}", node) }),
        }
    }

    fn free_registers(&mut self, regs: &[Register]) {
        for reg in regs {
            self.free_register();
        }
    }

    fn patch_jump(&mut self, label: usize, offset: i16) {
        if let BytecodeInstruction::JumpIfFalse { condition: _, offset: ref mut jump_offset } = self.chunk.instructions[label] {
            *jump_offset = offset;
        } else if let BytecodeInstruction::Jump { offset: ref mut jump_offset } = self.chunk.instructions[label] {
            *jump_offset = offset;
        } else {
            panic!("Invalid jump instruction at label {}", label);
        }
    }

    fn finalize(mut self) -> BytecodeChunk {
        self.chunk.add_instruction(BytecodeInstruction::Halt);
        self.chunk
    }
}


pub fn generate_bytecode(node: &AstNode) -> Result<BytecodeChunk, CodegenError> {
    let mut generator = CodeGenerator::new();
    let _result_reg = generator.compile_node(node)?;
    // Potentially handle the final result register if the root node is an expression
    Ok(generator.finalize())
}
