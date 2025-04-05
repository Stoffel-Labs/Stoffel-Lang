use std::fmt;

pub type Register = u8;
pub type ConstantIndex = u16;
pub type JumpOffset = i16;
pub type FunctionId = u32;

#[derive(Debug, Clone, PartialEq)]
pub enum Constant {
    Int(i64),
    Float(f64),
    String(String),
    Bool(bool),
    Nil,
}

#[derive(Debug, Clone, PartialEq)]
pub enum BytecodeInstruction {
    LoadConst { dest: Register, index: ConstantIndex },
    Move { dest: Register, src: Register },
    Add { dest: Register, lhs: Register, rhs: Register },
    Subtract { dest: Register, lhs: Register, rhs: Register },
    Multiply { dest: Register, lhs: Register, rhs: Register },
    Divide { dest: Register, lhs: Register, rhs: Register },
    Negate { dest: Register, src: Register },
    Not { dest: Register, src: Register },
    Equal { dest: Register, lhs: Register, rhs: Register },
    NotEqual { dest: Register, lhs: Register, rhs: Register },
    Greater { dest: Register, lhs: Register, rhs: Register },
    GreaterEqual { dest: Register, lhs: Register, rhs: Register },
    Less { dest: Register, lhs: Register, rhs: Register },
    LessEqual { dest: Register, lhs: Register, rhs: Register },
    Jump { offset: JumpOffset },
    JumpIfFalse { condition: Register, offset: JumpOffset },
    Call { dest: Register, function: FunctionId, args: Vec<Register> },
    Return { src: Register },
    GetGlobal { dest: Register, name_idx: ConstantIndex },
    SetGlobal { name_idx: ConstantIndex, src: Register },
    GetLocal { dest: Register, slot: u8 }, // Assuming locals are slot-based
    SetLocal { slot: u8, src: Register },
    MakeObject { dest: Register, type_idx: ConstantIndex },
    GetField { dest: Register, object: Register, field_idx: ConstantIndex },
    SetField { object: Register, field_idx: ConstantIndex, src: Register },
    Halt,
}

#[derive(Debug, Clone, Default)]
pub struct BytecodeChunk {
    pub instructions: Vec<BytecodeInstruction>,
    pub constants: Vec<Constant>,
    // Add line number mapping, function info, etc. as needed
}

impl BytecodeChunk {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn add_instruction(&mut self, instruction: BytecodeInstruction) -> usize {
        self.instructions.push(instruction);
        self.instructions.len() - 1
    }

    pub fn add_constant(&mut self, constant: Constant) -> ConstantIndex {
        // Avoid duplicates?
        self.constants.push(constant);
        (self.constants.len() - 1) as ConstantIndex
    }
}
