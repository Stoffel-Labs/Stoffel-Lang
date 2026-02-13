pub(crate) use stoffel_vm_types::core_types::{Value, F64};
pub(crate) use stoffel_vm_types::instructions::Instruction;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Constant {
    /// 64-bit signed integer
    I64(i64),
    /// 32-bit signed integer
    I32(i32),
    /// 16-bit signed integer
    I16(i16),
    /// 8-bit signed integer
    I8(i8),
    /// 8-bit unsigned integer
    U8(u8),
    /// 16-bit unsigned integer
    U16(u16),
    /// 32-bit unsigned integer
    U32(u32),
    /// 64-bit unsigned integer
    U64(u64),
    /// 64-bit floating point number (uses F64 wrapper for Eq/Hash)
    Float(F64),
    /// Boolean value
    Bool(bool),
    /// String value
    String(String),
    /// Reference to an object (key-value map)
    Object(usize),
    /// Reference to an array
    Array(usize),
    /// Reference to a foreign object (Rust object exposed to VM)
    Foreign(usize),
    /// Function closure (function with captured environment)
    Closure(String, Vec<String>), // function_id, upvalue names
    /// Unit/void/nil value
    Unit,
    /// Secret shared value (for SMPC)
    Share(crate::core_types::ShareType, Vec<u8>),
}

pub(crate) use stoffel_vm_types::instructions::ResolvedInstruction;

#[derive(Debug, Clone, Default)]
pub struct BytecodeChunk {
    pub instructions: Vec<Instruction>,
    pub constants: Vec<Constant>,
    pub labels: std::collections::HashMap<String, usize>,
}

/// Represents the complete compiled output, including the main code chunk
/// and the bytecode for all defined functions.
#[derive(Debug, Clone, Default)]
pub struct CompiledProgram {
    pub main_chunk: BytecodeChunk,
    pub function_chunks: std::collections::HashMap<String, BytecodeChunk>,
}

impl BytecodeChunk {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn add_instruction(&mut self, instruction: Instruction) -> usize {
        self.instructions.push(instruction);
        self.instructions.len() - 1
    }
    
    pub fn add_label(&mut self, label: String) -> usize {
        let pos = self.instructions.len();
        self.labels.insert(label, pos);
        pos // Return the position (index) associated with the label
    }

    pub fn add_constant(&mut self, constant: Constant) -> usize {
        self.constants.push(constant);
        self.constants.len() - 1
    }
    
    /// Resolves symbolic instructions to optimized resolved instructions
    ///
    /// This function converts the human-readable `Instruction` enum to the more efficient
    /// `ResolvedInstruction` enum by resolving labels to instruction indices and
    /// function names to function indices.
    ///
    /// # Arguments
    ///
    /// * `constant_map` - A map from constants to their indices
    /// * `function_map` - A map from function names to their indices
    ///
    /// # Returns
    ///
    /// A vector of resolved instructions
    pub fn resolve_instructions(
        &self,
        constant_map: &std::collections::HashMap<Value, usize>,
        function_map: &std::collections::HashMap<String, usize>,
    ) -> Result<Vec<ResolvedInstruction>, String> {
        let mut resolved = Vec::with_capacity(self.instructions.len());
        
        for instruction in &self.instructions {
            let resolved_instruction = match instruction {
                Instruction::LD(reg, offset) => 
                    ResolvedInstruction::LD(*reg, *offset),
                    
                Instruction::LDI(reg, value) => {
                    let const_idx = constant_map.get(value)
                        .ok_or_else(|| format!("Constant not found in map: {:?}", value))?;
                    ResolvedInstruction::LDI(*reg, *const_idx)
                },
                
                Instruction::MOV(dest, src) => 
                    ResolvedInstruction::MOV(*dest, *src),
                    
                Instruction::ADD(dest, src1, src2) => 
                    ResolvedInstruction::ADD(*dest, *src1, *src2),
                    
                Instruction::SUB(dest, src1, src2) => 
                    ResolvedInstruction::SUB(*dest, *src1, *src2),
                    
                Instruction::MUL(dest, src1, src2) => 
                    ResolvedInstruction::MUL(*dest, *src1, *src2),
                    
                Instruction::DIV(dest, src1, src2) => 
                    ResolvedInstruction::DIV(*dest, *src1, *src2),
                    
                Instruction::MOD(dest, src1, src2) => 
                    ResolvedInstruction::MOD(*dest, *src1, *src2),
                    
                Instruction::AND(dest, src1, src2) => 
                    ResolvedInstruction::AND(*dest, *src1, *src2),
                    
                Instruction::OR(dest, src1, src2) => 
                    ResolvedInstruction::OR(*dest, *src1, *src2),
                    
                Instruction::XOR(dest, src1, src2) => 
                    ResolvedInstruction::XOR(*dest, *src1, *src2),
                    
                Instruction::NOT(dest, src) => 
                    ResolvedInstruction::NOT(*dest, *src),
                    
                Instruction::SHL(dest, src, amount) => 
                    ResolvedInstruction::SHL(*dest, *src, *amount),
                    
                Instruction::SHR(dest, src, amount) => 
                    ResolvedInstruction::SHR(*dest, *src, *amount),
                    
                Instruction::JMP(label) => {
                    let target = self.labels.get(label)
                        .ok_or_else(|| format!("Label not found: {}", label))?;
                    ResolvedInstruction::JMP(*target)
                },
                
                Instruction::JMPEQ(label) => {
                    let target = self.labels.get(label)
                        .ok_or_else(|| format!("Label not found: {}", label))?;
                    ResolvedInstruction::JMPEQ(*target)
                },
                
                Instruction::JMPNEQ(label) => {
                    let target = self.labels.get(label)
                        .ok_or_else(|| format!("Label not found: {}", label))?;
                    ResolvedInstruction::JMPNEQ(*target)
                },
                
                Instruction::JMPLT(label) => {
                    let target = self.labels.get(label)
                        .ok_or_else(|| format!("Label not found: {}", label))?;
                    ResolvedInstruction::JMPLT(*target)
                },
                
                Instruction::JMPGT(label) => {
                    let target = self.labels.get(label)
                        .ok_or_else(|| format!("Label not found: {}", label))?;
                    ResolvedInstruction::JMPGT(*target)
                },
                
                Instruction::CALL(function_name) => {
                    let function_idx = function_map.get(function_name)
                        .ok_or_else(|| format!("Function not found: {}", function_name))?;
                    ResolvedInstruction::CALL(*function_idx)
                },
                
                Instruction::RET(reg) => 
                    ResolvedInstruction::RET(*reg),
                    
                Instruction::PUSHARG(reg) => 
                    ResolvedInstruction::PUSHARG(*reg),
                    
                Instruction::CMP(reg1, reg2) => 
                    ResolvedInstruction::CMP(*reg1, *reg2),
            };
            
            resolved.push(resolved_instruction);
        }
        
        Ok(resolved)
    }
}
