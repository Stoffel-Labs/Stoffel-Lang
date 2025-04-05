use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq)]
pub enum Literal {
    Int(i64),
    Float(f64),
    String(String),
    Bool(bool),
    Nil,
}

#[derive(Debug, Clone, PartialEq)]
pub enum AstNode {
    Literal(Literal),
    Identifier(String),
    Assignment {
        target: Box<AstNode>,
        value: Box<AstNode>,
    },
    BinaryOperation {
        op: String,
        left: Box<AstNode>,
        right: Box<AstNode>,
    },
    UnaryOperation {
        op: String,
        operand: Box<AstNode>,
    },
    FunctionCall {
        function: Box<AstNode>,
        arguments: Vec<AstNode>,
    },
    FunctionDefinition {
        name: Option<String>,
        parameters: Vec<String>,
        body: Box<AstNode>,
    },
    IfExpression {
        condition: Box<AstNode>,
        then_branch: Box<AstNode>,
        else_branch: Option<Box<AstNode>>,
    },
    WhileLoop {
        condition: Box<AstNode>,
        body: Box<AstNode>,
    },
    Block(Vec<AstNode>),
    Return(Option<Box<AstNode>>),
    ObjectConstruction {
        type_name: String,
        fields: HashMap<String, AstNode>,
    },
    FieldAccess {
        object: Box<AstNode>,
        field_name: String,
    },
}

impl AstNode {
    pub fn is_expression(&self) -> bool {
        match self {
            AstNode::IfExpression { .. } => true,
            AstNode::Block(nodes) => nodes.last().map_or(false, |n| n.is_expression()),
            AstNode::Assignment { .. } => false, // Or true if assignments return values
            AstNode::WhileLoop { .. } => false, // Loops typically don't evaluate to a value
            AstNode::Return(_) => false,
            AstNode::FunctionDefinition { .. } => false,
            _ => true, // Literals, identifiers, calls, ops, etc. are expressions
        }
    }
}
