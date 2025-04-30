use crate::errors::SourceLocation;
use crate::symbol_table::SymbolType;

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
pub enum Pragma {
    Simple(String, SourceLocation),
    KeyValue(String, Box<AstNode>, SourceLocation),
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
    Identifier(String, SourceLocation),
    Assignment {
        target: Box<AstNode>,
        value: Box<AstNode>,
        location: SourceLocation,
    },
    VariableDeclaration {
        name: String,
        type_annotation: Option<Box<AstNode>>,
        value: Option<Box<AstNode>>,
        is_mutable: bool,
        is_secret: bool,
        location: SourceLocation,
    },
    BinaryOperation {
        op: String,
        left: Box<AstNode>,
        right: Box<AstNode>,
        location: SourceLocation,
    },
    UnaryOperation {
        op: String,
        operand: Box<AstNode>,
        location: SourceLocation,
    },
    FunctionCall {
        function: Box<AstNode>,
        arguments: Vec<AstNode>,
        location: SourceLocation,
        resolved_return_type: Option<SymbolType>,
    },
    NamedArgument {
        name: String,
        value: Box<AstNode>,
        location: SourceLocation,
    },
    FunctionDefinition {
        name: Option<String>,
        parameters: Vec<Parameter>,
        return_type: Option<Box<AstNode>>,
        body: Box<AstNode>,
        is_secret: bool,
        pragmas: Vec<Pragma>,
        location: SourceLocation,
        node_id: usize,
    },
    IfExpression {
        condition: Box<AstNode>,
        then_branch: Box<AstNode>,
        else_branch: Option<Box<AstNode>>,
    },
    WhileLoop {
        condition: Box<AstNode>,
        body: Box<AstNode>,
        location: SourceLocation,
    },
    Block(Vec<AstNode>),
    Return(Option<Box<AstNode>>),
    Yield(Option<Box<AstNode>>),
    Break,
    Continue,
    FieldAccess {
        object: Box<AstNode>,
        field_name: String,
        location: SourceLocation,
    },
    IndexAccess {
        base: Box<AstNode>,
        index: Box<AstNode>,
        location: SourceLocation,
    },
    ListLiteral(Vec<AstNode>),
    TupleLiteral(Vec<AstNode>),
    SetLiteral(Vec<AstNode>),
    DictLiteral(Vec<(AstNode, AstNode)>),
    TypeAlias {
        name: String,
        target_type: Box<AstNode>,
        is_secret: bool,
        location: SourceLocation,
    },
    ObjectDefinition {
        name: String,
        base_type: Option<Box<AstNode>>,
        fields: Vec<FieldDefinition>,
        is_secret: bool,
        location: SourceLocation,
    },
    EnumDefinition {
        name: String,
        members: Vec<EnumMember>,
        is_secret: bool,
        location: SourceLocation,
    },
    SecretType(Box<AstNode>),
    FunctionType {
        parameter_types: Vec<AstNode>,
        return_type: Box<AstNode>,
        location: SourceLocation,
    },
    TupleType(Vec<AstNode>),
    ListType(Box<AstNode>),
    DictType {
        key_type: Box<AstNode>,
        value_type: Box<AstNode>,
        location: SourceLocation,
    },
    ForLoop {
        variables: Vec<String>,
        iterable: Box<AstNode>,
        body: Box<AstNode>,
        location: SourceLocation,
    },
    TryCatch {
        try_block: Box<AstNode>,
        catch_clauses: Vec<CatchClause>,
        finally_block: Option<Box<AstNode>>,
        location: SourceLocation,
    },
    Import {
        module_path: Vec<String>,
        alias: Option<String>,
        imported_items: Option<Vec<String>>,
        location: SourceLocation,
    },
    CommandCall {
        command: Box<AstNode>,
        arguments: Vec<AstNode>,
        location: SourceLocation,
        resolved_return_type: Option<SymbolType>,
    },
    DiscardStatement {
        expression: Box<AstNode>,
        location: SourceLocation,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct CatchClause {
    pub exception_type: Option<Box<AstNode>>,
    pub variable_name: Option<String>,
    pub body: Box<AstNode>,
    pub location: SourceLocation,
}

impl AstNode {
    pub fn is_type_node(&self) -> bool {
        matches!(
            self,
            AstNode::Identifier(_, _)
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
            AstNode::Literal(_) | AstNode::Identifier(_, _) => true,
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
            AstNode::DiscardStatement { .. } => false,
            &AstNode::SecretType(_) => todo!(),
        }
    }

    pub fn location(&self) -> SourceLocation {
        match self {
            AstNode::Identifier(_, loc) => loc.clone(),
            AstNode::Assignment { location: loc, .. } => loc.clone(),
            AstNode::VariableDeclaration { location: loc, .. } => loc.clone(),
            AstNode::BinaryOperation { location: loc, .. } => loc.clone(),
            AstNode::UnaryOperation { location: loc, .. } => loc.clone(),
            AstNode::FunctionCall { location: loc, .. } => loc.clone(),
            AstNode::NamedArgument { location: loc, .. } => loc.clone(),
            AstNode::FunctionDefinition { location: loc, .. } => loc.clone(),
            AstNode::WhileLoop { location: loc, .. } => loc.clone(),
            AstNode::FieldAccess { location: loc, .. } => loc.clone(),
            AstNode::IndexAccess { location: loc, .. } => loc.clone(),
            AstNode::TypeAlias { location: loc, .. } => loc.clone(),
            AstNode::ObjectDefinition { location: loc, .. } => loc.clone(),
            AstNode::EnumDefinition { location: loc, .. } => loc.clone(),
            AstNode::FunctionType { location: loc, .. } => loc.clone(),
            AstNode::DictType { location: loc, .. } => loc.clone(),
            AstNode::ForLoop { location: loc, .. } => loc.clone(),
            AstNode::TryCatch { location: loc, .. } => loc.clone(),
            AstNode::Import { location: loc, .. } => loc.clone(),
            AstNode::CommandCall { location: loc, .. } => loc.clone(),
            AstNode::DiscardStatement { location: loc, .. } => loc.clone(),
            AstNode::Literal(_) => SourceLocation::default(),
            _ => SourceLocation::default(),
        }
    }
}
