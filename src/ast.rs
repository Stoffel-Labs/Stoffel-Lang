use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq, Hash)]
pub enum Value {
    Int(i64),
    Float(u64),
    String(String),
    Bool(bool),
    Nil,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Parameter {
    pub name: String,
    pub type_annotation: Option<Box<AstNode>>,
    pub default_value: Option<Box<AstNode>>,
    pub is_secret: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FieldDefinition {
    pub name: String,
    pub type_annotation: Box<AstNode>,
    pub is_secret: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub struct EnumMember {
    pub name: String,
    pub value: Option<Box<AstNode>>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum AstNode {
    Literal(Value),
    Identifier(String),
    Assignment {
        target: Box<AstNode>,
        value: Box<AstNode>,
    },
    VariableDeclaration {
        name: String,
        type_annotation: Option<Box<AstNode>>,
        value: Option<Box<AstNode>>,
        is_mutable: bool,
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
    NamedArgument {
        name: String,
        value: Box<AstNode>,
    },
    FunctionDefinition {
        name: Option<String>,
        parameters: Vec<Parameter>,
        return_type: Option<Box<AstNode>>,
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
    Yield(Option<Box<AstNode>>),
    Break,
    Continue,
    FieldAccess {
        object: Box<AstNode>,
        field_name: String,
    },
    IndexAccess {
        base: Box<AstNode>,
        index: Box<AstNode>,
    },
    ListLiteral(Vec<AstNode>),
    TupleLiteral(Vec<AstNode>),
    SetLiteral(Vec<AstNode>),
    DictLiteral(Vec<(AstNode, AstNode)>),
    TypeAlias {
        name: String,
        target_type: Box<AstNode>,
    },
    ObjectDefinition {
        name: String,
        base_type: Option<Box<AstNode>>,
        fields: Vec<FieldDefinition>,
    },
    EnumDefinition {
        name: String,
        members: Vec<EnumMember>,
    },
    SecretType(Box<AstNode>),
    FunctionType {
        parameter_types: Vec<AstNode>,
        return_type: Box<AstNode>,
    },
    TupleType(Vec<AstNode>),
    ListType(Box<AstNode>),
    DictType {
        key_type: Box<AstNode>,
        value_type: Box<AstNode>,
    },
    ForLoop {
        variables: Vec<String>,
        iterable: Box<AstNode>,
        body: Box<AstNode>,
    },
    TryCatch {
        try_block: Box<AstNode>,
        catch_clauses: Vec<CatchClause>,
        finally_block: Option<Box<AstNode>>,
    },
    Import {
        module_path: Vec<String>,
        alias: Option<String>,
        imported_items: Option<Vec<String>>,
    },
    CommandCall {
        command: Box<AstNode>,
        arguments: Vec<AstNode>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct CatchClause {
    pub exception_type: Option<Box<AstNode>>,
    pub variable_name: Option<String>,
    pub body: Box<AstNode>,
}

impl AstNode {
    pub fn is_type_node(&self) -> bool {
        matches!(
            self,
            AstNode::Identifier(_)
                | AstNode::TypeAlias { .. }
                | AstNode::ObjectDefinition { .. }
                | AstNode::EnumDefinition { .. }
                | AstNode::FunctionType { .. }
                | AstNode::TupleType(_)
                | AstNode::SecretType(_)
                | AstNode::ListType(_)
                | AstNode::DictType { .. }
                | AstNode::FieldAccess { .. }
        )
    }

    pub fn is_expression(&self) -> bool {
        match self {
            AstNode::Literal(_) | AstNode::Identifier(_) => true,
            AstNode::BinaryOperation { .. } | AstNode::UnaryOperation { .. } => true,
            AstNode::FunctionCall { .. } | AstNode::CommandCall { .. } => true,
            AstNode::FieldAccess { .. } | AstNode::IndexAccess { .. } => true,
            AstNode::ListLiteral(_) | AstNode::TupleLiteral(_) => true,
            AstNode::SetLiteral(_) | AstNode::DictLiteral(_) => true,
            AstNode::IfExpression { .. } => true,
            AstNode::Block(nodes) => nodes.last().map_or(false, |n| n.is_expression()),
            AstNode::Assignment { .. } | AstNode::VariableDeclaration { .. } => false,
            AstNode::WhileLoop { .. } | AstNode::ForLoop { .. } => false,
            AstNode::Return(_) | AstNode::Yield(_) | AstNode::Break | AstNode::Continue => false,
            AstNode::FunctionDefinition { .. } | AstNode::TypeAlias { .. } => false,
            AstNode::Import { .. } => false,
            AstNode::ObjectDefinition { .. } | AstNode::EnumDefinition { .. } => false,
            AstNode::TryCatch { .. } => false,
            AstNode::NamedArgument { .. } => false,
            AstNode::FunctionType { .. } | AstNode::TupleType(_) | AstNode::ListType(_) | AstNode::DictType { .. } => false,
            &AstNode::SecretType(_) => todo!(), // TODO: figure out how we want to handle secret types
        }
    }
}
