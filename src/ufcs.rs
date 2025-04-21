use crate::ast::AstNode;

pub fn transform_ufcs(node: AstNode) -> AstNode {
    match node {
        AstNode::FunctionCall { function, arguments } => {
            // Example: Transform obj.method(arg1, arg2)
            if let AstNode::FieldAccess { object, field_name } = *function {
                 // Convert to MethodCall(object, method_name, args) or
                 // FunctionCall(Identifier(method_name), [object] + args)
                 // depending on canonical representation.
                 // Let's choose the latter for simplicity here.
                let mut new_args = vec![*object];
                new_args.extend(arguments.into_iter().map(transform_ufcs));
                return AstNode::FunctionCall {
                    function: Box::new(AstNode::Identifier(field_name)),
                    arguments: new_args,
                };
            }
            // Recursively transform arguments and the function expression itself if needed
            AstNode::FunctionCall {
                function: Box::new(transform_ufcs(*function)),
                arguments: arguments.into_iter().map(transform_ufcs).collect(),
            }
        }
        AstNode::Assignment { target, value } => AstNode::Assignment {
            target: Box::new(transform_ufcs(*target)),
            value: Box::new(transform_ufcs(*value)),
        },
        AstNode::BinaryOperation { op, left, right } => AstNode::BinaryOperation {
            op,
            left: Box::new(transform_ufcs(*left)),
            right: Box::new(transform_ufcs(*right)),
        },
        AstNode::UnaryOperation { op, operand } => AstNode::UnaryOperation {
            op,
            operand: Box::new(transform_ufcs(*operand)),
        },
        AstNode::FunctionDefinition { name, parameters, return_type, body, return_type_is_secret } => AstNode::FunctionDefinition {
            name,
            parameters,
            body: Box::new(transform_ufcs(*body)),
        },
        AstNode::IfExpression { condition, then_branch, else_branch } => AstNode::IfExpression {
            condition: Box::new(transform_ufcs(*condition)),
            then_branch: Box::new(transform_ufcs(*then_branch)),
            else_branch: else_branch.map(|b| Box::new(transform_ufcs(*b))),
        },
        AstNode::WhileLoop { condition, body } => AstNode::WhileLoop {
            condition: Box::new(transform_ufcs(*condition)),
            body: Box::new(transform_ufcs(*body)),
        },
        AstNode::Block(nodes) => AstNode::Block(
            nodes.into_iter().map(transform_ufcs).collect()
        ),
        AstNode::Return(value) => AstNode::Return(
            value.map(|v| Box::new(transform_ufcs(*v)))
        ),
        AstNode::ObjectConstruction { type_name, fields } => AstNode::ObjectConstruction {
            type_name,
            fields: fields.into_iter().map(|(k, v)| (k, transform_ufcs(v))).collect(),
        },
        AstNode::FieldAccess { object, field_name } => AstNode::FieldAccess {
            object: Box::new(transform_ufcs(*object)),
            field_name,
        },
        // Literals and Identifiers don't need transformation
        AstNode::Literal(_) | AstNode::Identifier(_) => node,
    }
}
