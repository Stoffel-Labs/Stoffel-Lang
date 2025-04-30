use crate::ast::AstNode;

/// Transforms the AST to support Uniform Function Call Syntax (UFCS)
/// This allows for multiple calling styles:
/// 1. Traditional method call: obj.method(arg1, arg2)
/// 2. Function call with object as first argument: method(obj, arg1, arg2)
/// 3. Command-style call: obj method arg1 arg2 (without parentheses)
/// 4. Infix operator style: arg1.op(arg2) equivalent to op(arg1, arg2)
pub fn transform_ufcs(node: AstNode) -> AstNode {
    match node {
        AstNode::FunctionCall { function, arguments, location, resolved_return_type } => {
            // Style 1: Transform obj.method(arg1, arg2) into method(obj, arg1, arg2)
            if let AstNode::FieldAccess { object, field_name, location: fa_location } = *function {
                // Convert to MethodCall(object, method_name, args) or
                // Let's choose the latter for simplicity here.
                let mut new_args = vec![*object];
                new_args.extend(arguments.into_iter().map(transform_ufcs));
                return AstNode::FunctionCall {
                    function: Box::new(AstNode::Identifier(field_name, location)),
                    arguments: new_args,
                    location: fa_location,
                    resolved_return_type
                };
            }
            // Recursively transform arguments and the function expression itself
            AstNode::FunctionCall {
                function: Box::new(transform_ufcs(*function)),
                arguments: arguments.into_iter().map(transform_ufcs).collect(),
                location,
                resolved_return_type
            }
        },
        // Style 3: Transform command-style calls: obj method arg1 arg2
        AstNode::CommandCall { command, arguments, location, resolved_return_type } => {
            // If the command is an identifier, transform to a regular function call
            // with the first argument as the object
            if !arguments.is_empty() {
                let first_arg = transform_ufcs(arguments[0].clone());
                let remaining_args = arguments.into_iter()
                    .skip(1)
                    .map(transform_ufcs)
                    .collect::<Vec<_>>();

                let mut new_args = vec![first_arg];
                new_args.extend(remaining_args);

                return AstNode::FunctionCall {
                    function: Box::new(transform_ufcs(*command)),
                    arguments: new_args,
                    location,
                    resolved_return_type, // Pass the resolved type along
                };
            }
            // If no arguments, just transform the command part
            AstNode::CommandCall {
                command: Box::new(transform_ufcs(*command)),
                arguments: arguments.into_iter().map(transform_ufcs).collect(),
                location, resolved_return_type // Keep type even if no args
            }
        }
        AstNode::FieldAccess { object, field_name, location } => {
            // Style 4: Transform infix operator calls: a.op(b) into op(a, b)
            // Check if this field access is followed by a function call (handled in FunctionCall case)
            // Otherwise, leave it as is
            AstNode::FieldAccess {
                object: Box::new(transform_ufcs(*object)),
                field_name,
                location,
            }
        },
        _ => node,
    }
}
