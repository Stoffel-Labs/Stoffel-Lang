pub(crate) use stoffel_vm_types::core_types::Value;
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
    /// Fixed-point floating point number (represented as i64 internally for Eq/Hash)
    Float(i64),
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

#[repr(u8)]
pub enum ReducedOpcode {
    // LD r1 [sp+0]
    LD = 0x00,
    // LDI r1 10
    LDI = 0x01,
    // MOV r1 r2
    MOV = 0x02,
    // ADD r1, r2, r3
    ADD = 0x03,
    // SUB r1, r2, r3
    SUB = 0x04,
    // MUL r1, r2, r3
    MUL = 0x05,
    // DIV r1, r2, r3
    DIV = 0x06,
    // MOD r1, r2, r3
    MOD = 0x07,
    // AND r1, r2, r3
    AND = 0x08,
    // OR r1, r2, r3
    OR = 0x09,
    // XOR r1, r2, r3
    XOR = 0x0A,
    // NOT r1, r2
    NOT = 0x0B,
    // SHL <target>, <source>, <amount>
    // SHL r1, r2, 1
    SHL = 0x0C,
    // SHR <target>, <source>, <amount>
    // SHR r1, r2, 1
    SHR = 0x0D,
    // JMP <jump_to>
    JMP = 0x0E,
    // JMPEQ <jump_to>
    JMPEQ = 0x0F,
    // JMPNEQ <jump_to>
    JMPNEQ = 0x10,
    // CALL <function>
    CALL = 0x11,
    // RET r1
    RET = 0x12,
    // PUSHARG r1
    PUSHARG = 0x13,
    // CMP r1 r2
    CMP = 0x14,
    // JMPLT <jump_to>
    JMPLT = 0x15,
    // JMPGT <jump_to>
    JMPGT = 0x16,
}

/// Represents different kinds of operands for instructions.
#[derive(Debug, Clone, PartialEq)]
pub enum Operand {
    Register(usize),                   // A register (r0, r1, etc.)
    StackAddr(i32),                    // Stack pointer offset [sp+n]
    Immediate(Value),                  // An immediate value (constant)
    Label(String),                     // A jump label
}

/// Resolved instruction with numeric indices instead of strings
///
/// This is an optimized representation of instructions used during execution.
/// String identifiers (like function names and labels) are replaced with numeric indices,
/// allowing for faster execution without string lookups.
///
/// This representation is generated from the symbolic `Instruction` enum during function
/// registration and is used by the VM's execution engine.
#[derive(Debug, Clone, Copy)]
pub enum ResolvedInstruction {
    // Load value from stack to register
    LD(usize, i32),                      // LD r1, [sp+0]
    // Load immediate value to register
    LDI(usize, usize),                   // LDI r1, const_idx (register, constant index)
    // Move value from one register to another
    MOV(usize, usize),                   // MOV r1, r2
    // Arithmetic operations
    ADD(usize, usize, usize),            // ADD r1, r2, r3
    SUB(usize, usize, usize),            // SUB r1, r2, r3
    MUL(usize, usize, usize),            // MUL r1, r2, r3
    DIV(usize, usize, usize),            // DIV r1, r2, r3
    MOD(usize, usize, usize),            // MOD r1, r2, r3
    // Bitwise operations
    AND(usize, usize, usize),            // AND r1, r2, r3
    OR(usize, usize, usize),             // OR r1, r2, r3
    XOR(usize, usize, usize),            // XOR r1, r2, r3
    NOT(usize, usize),                   // NOT r1, r2
    SHL(usize, usize, usize),            // SHL r1, r2, r3
    SHR(usize, usize, usize),            // SHR r1, r2, r3
    // Control flow
    JMP(usize),                          // JMP to instruction index
    JMPEQ(usize),                        // JMPEQ to instruction index
    JMPNEQ(usize),                       // JMPNEQ to instruction index
    JMPLT(usize),                        // JMPLT to instruction index
    JMPGT(usize),                        // JMPGT to instruction index
    // Function handling
    CALL(usize),                         // CALL function index
    RET(usize),                          // RET r1
    PUSHARG(usize),                      // PUSHARG r1
    // Comparison
    CMP(usize, usize),                   // CMP r1, r2
}

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
