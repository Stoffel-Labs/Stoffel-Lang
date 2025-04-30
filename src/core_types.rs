#[derive(Debug, Clone, PartialEq, Hash)]
pub enum Value {
    Int(i64),
    Float(u64),
    String(String),
    Bool(bool),
    Nil,
}

impl From<crate::bytecode::Constant> for Value {
    fn from(constant: crate::bytecode::Constant) -> Self {
        match constant {
            crate::bytecode::Constant::Int(i) => Value::Int(i),
            crate::bytecode::Constant::Float(f) => Value::Float(f),
            crate::bytecode::Constant::String(s) => Value::String(s),
            crate::bytecode::Constant::Bool(b) => Value::Bool(b),
            crate::bytecode::Constant::Nil => Value::Nil,
        }
    }
}
