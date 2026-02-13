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

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    // ===================== Happy Path =====================

    #[test]
    fn new_chunk_is_empty() {
        let chunk = BytecodeChunk::new();
        assert!(chunk.instructions.is_empty());
        assert!(chunk.constants.is_empty());
        assert!(chunk.labels.is_empty());
    }

    #[test]
    fn add_instruction_returns_index_and_stores() {
        let mut chunk = BytecodeChunk::new();
        let idx0 = chunk.add_instruction(Instruction::LDI(0, Value::I64(42)));
        let idx1 = chunk.add_instruction(Instruction::ADD(2, 0, 1));
        assert_eq!(idx0, 0);
        assert_eq!(idx1, 1);
        assert_eq!(chunk.instructions.len(), 2);
    }

    #[test]
    fn add_constant_returns_index_and_stores() {
        let mut chunk = BytecodeChunk::new();
        let idx0 = chunk.add_constant(Constant::I64(10));
        let idx1 = chunk.add_constant(Constant::String("hello".into()));
        let idx2 = chunk.add_constant(Constant::Bool(true));
        assert_eq!(idx0, 0);
        assert_eq!(idx1, 1);
        assert_eq!(idx2, 2);
        assert_eq!(chunk.constants.len(), 3);
        assert_eq!(chunk.constants[0], Constant::I64(10));
        assert_eq!(chunk.constants[2], Constant::Bool(true));
    }

    #[test]
    fn add_label_records_current_position() {
        let mut chunk = BytecodeChunk::new();
        // Label before any instructions points to index 0
        let pos0 = chunk.add_label("start".into());
        assert_eq!(pos0, 0);

        chunk.add_instruction(Instruction::LDI(0, Value::I64(1)));
        chunk.add_instruction(Instruction::LDI(1, Value::I64(2)));

        // Label after 2 instructions points to index 2
        let pos2 = chunk.add_label("after_two".into());
        assert_eq!(pos2, 2);
        assert_eq!(chunk.labels["start"], 0);
        assert_eq!(chunk.labels["after_two"], 2);
    }

    #[test]
    fn compiled_program_default_has_empty_chunks() {
        let program = CompiledProgram::default();
        assert!(program.main_chunk.instructions.is_empty());
        assert!(program.function_chunks.is_empty());
    }

    #[test]
    fn compiled_program_with_function_chunks() {
        let mut program = CompiledProgram::default();
        let mut func_chunk = BytecodeChunk::new();
        func_chunk.add_instruction(Instruction::RET(0));
        program.function_chunks.insert("my_func".into(), func_chunk);
        assert_eq!(program.function_chunks.len(), 1);
        assert!(program.function_chunks.contains_key("my_func"));
    }

    #[test]
    fn resolve_instructions_arithmetic() {
        let mut chunk = BytecodeChunk::new();
        chunk.add_instruction(Instruction::ADD(0, 1, 2));
        chunk.add_instruction(Instruction::SUB(3, 0, 1));
        chunk.add_instruction(Instruction::MUL(4, 2, 3));
        chunk.add_instruction(Instruction::MOV(5, 4));
        chunk.add_instruction(Instruction::RET(5));

        let constant_map = HashMap::new();
        let function_map = HashMap::new();
        let resolved = chunk.resolve_instructions(&constant_map, &function_map).unwrap();
        assert_eq!(resolved.len(), 5);
        assert!(matches!(resolved[0], ResolvedInstruction::ADD(0, 1, 2)));
        assert!(matches!(resolved[1], ResolvedInstruction::SUB(3, 0, 1)));
        assert!(matches!(resolved[4], ResolvedInstruction::RET(5)));
    }

    #[test]
    fn resolve_instructions_with_ldi_and_constants() {
        let mut chunk = BytecodeChunk::new();
        chunk.add_instruction(Instruction::LDI(0, Value::I64(42)));
        chunk.add_instruction(Instruction::LDI(1, Value::Bool(true)));

        let mut constant_map: HashMap<Value, usize> = HashMap::new();
        constant_map.insert(Value::I64(42), 0);
        constant_map.insert(Value::Bool(true), 1);
        let function_map = HashMap::new();

        let resolved = chunk.resolve_instructions(&constant_map, &function_map).unwrap();
        assert!(matches!(resolved[0], ResolvedInstruction::LDI(0, 0)));
        assert!(matches!(resolved[1], ResolvedInstruction::LDI(1, 1)));
    }

    #[test]
    fn resolve_instructions_with_labels() {
        let mut chunk = BytecodeChunk::new();
        chunk.add_instruction(Instruction::LDI(0, Value::I64(1)));
        chunk.add_instruction(Instruction::CMP(0, 1));
        chunk.add_instruction(Instruction::JMPEQ("target".into()));
        chunk.add_instruction(Instruction::LDI(0, Value::I64(2)));
        chunk.add_label("target".into()); // Points to instruction index 4
        chunk.add_instruction(Instruction::RET(0));

        let mut constant_map: HashMap<Value, usize> = HashMap::new();
        constant_map.insert(Value::I64(1), 0);
        constant_map.insert(Value::I64(2), 1);
        let function_map = HashMap::new();

        let resolved = chunk.resolve_instructions(&constant_map, &function_map).unwrap();
        assert!(matches!(resolved[2], ResolvedInstruction::JMPEQ(4)));
    }

    #[test]
    fn resolve_instructions_with_call() {
        let mut chunk = BytecodeChunk::new();
        chunk.add_instruction(Instruction::PUSHARG(0));
        chunk.add_instruction(Instruction::CALL("foo".into()));

        let constant_map = HashMap::new();
        let mut function_map = HashMap::new();
        function_map.insert("foo".into(), 3);

        let resolved = chunk.resolve_instructions(&constant_map, &function_map).unwrap();
        assert!(matches!(resolved[0], ResolvedInstruction::PUSHARG(0)));
        assert!(matches!(resolved[1], ResolvedInstruction::CALL(3)));
    }

    // ===================== Semi-honest =====================

    #[test]
    fn empty_chunk_resolves_to_empty() {
        let chunk = BytecodeChunk::new();
        let resolved = chunk.resolve_instructions(&HashMap::new(), &HashMap::new()).unwrap();
        assert!(resolved.is_empty());
    }

    #[test]
    fn chunk_with_only_constants_no_instructions() {
        let mut chunk = BytecodeChunk::new();
        chunk.add_constant(Constant::I64(1));
        chunk.add_constant(Constant::Bool(false));
        assert_eq!(chunk.constants.len(), 2);
        assert!(chunk.instructions.is_empty());
    }

    #[test]
    fn multiple_labels_to_same_instruction() {
        let mut chunk = BytecodeChunk::new();
        chunk.add_instruction(Instruction::LDI(0, Value::I64(0)));
        // Both labels point to instruction index 1
        chunk.add_label("label_a".into());
        chunk.add_label("label_b".into());
        chunk.add_instruction(Instruction::RET(0));

        assert_eq!(chunk.labels["label_a"], 1);
        assert_eq!(chunk.labels["label_b"], 1);
    }

    #[test]
    fn large_constant_pool() {
        let mut chunk = BytecodeChunk::new();
        for i in 0..1000 {
            let idx = chunk.add_constant(Constant::I64(i));
            assert_eq!(idx, i as usize);
        }
        assert_eq!(chunk.constants.len(), 1000);
    }

    // ===================== Adversarial =====================

    #[test]
    fn resolve_fails_on_missing_label() {
        let mut chunk = BytecodeChunk::new();
        chunk.add_instruction(Instruction::JMP("nonexistent".into()));
        let result = chunk.resolve_instructions(&HashMap::new(), &HashMap::new());
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Label not found"));
    }

    #[test]
    fn resolve_fails_on_missing_function() {
        let mut chunk = BytecodeChunk::new();
        chunk.add_instruction(Instruction::CALL("unknown_func".into()));
        let result = chunk.resolve_instructions(&HashMap::new(), &HashMap::new());
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Function not found"));
    }

    #[test]
    fn resolve_fails_on_missing_constant_in_ldi() {
        let mut chunk = BytecodeChunk::new();
        chunk.add_instruction(Instruction::LDI(0, Value::I64(999)));
        // No constant_map entry for I64(999)
        let result = chunk.resolve_instructions(&HashMap::new(), &HashMap::new());
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Constant not found"));
    }

    #[test]
    fn duplicate_label_name_overwrites_silently() {
        // NOTE: add_label uses HashMap::insert which silently overwrites.
        // This test documents the current behavior (last-wins) rather than
        // asserting it's desirable. A future improvement could detect duplicates.
        let mut chunk = BytecodeChunk::new();
        chunk.add_instruction(Instruction::LDI(0, Value::I64(0)));
        chunk.add_label("dup".into()); // index 1
        chunk.add_instruction(Instruction::LDI(1, Value::I64(1)));
        chunk.add_label("dup".into()); // index 2, overwrites
        // Verify last-wins behavior (current implementation)
        assert_eq!(chunk.labels["dup"], 2);
        assert_eq!(chunk.labels.len(), 1, "Should have exactly one label entry");
    }
}
