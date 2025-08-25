use crate::ast::{AstNode, Pragma, Value};
use crate::errors::{CompilerError, ErrorReporter};
use crate::symbol_table::{SymbolDeclarationError, SymbolInfo, SymbolKind, SymbolTable, SymbolType};

/// Performs semantic analysis (symbol checking, type checking) on the AST.
pub struct SemanticAnalyzer<'a> {
    symbol_table: SymbolTable,
    error_reporter: &'a mut ErrorReporter,
    current_function_return_type: Option<SymbolType>, // Track expected return type
    filename: &'a str,
}

impl<'a> SemanticAnalyzer<'a> {
    pub fn new(error_reporter: &'a mut ErrorReporter, filename: &'a str) -> Self {
        SemanticAnalyzer {
            symbol_table: SymbolTable::new(),
            error_reporter,
            current_function_return_type: None,
            filename,
        }
    }

    fn int_literal_value(node: &AstNode) -> Option<i128> {
        if let AstNode::Literal(Value::Int(i)) = node { Some(*i as i128) } else { None }
    }

    fn check_integer_compat(&mut self, src_node: Option<&AstNode>, src_type: &SymbolType, dst_type: &SymbolType, location: crate::errors::SourceLocation) -> Result<(), ()> {
        // Only enforce special rules if destination is integer
        if dst_type.is_integer() {
            // 1) Literal fits check
            if let Some(val) = src_node.and_then(Self::int_literal_value) {
                if !dst_type.fits_literal_i128(val) {
                    let min = dst_type.min_value_i128().unwrap();
                    let max = dst_type.max_value_i128().unwrap();
                    self.error_reporter.add_error(CompilerError::type_error(
                        format!("Integer literal {} does not fit in '{}' (allowed range {}..={})", val, declared_type_to_string(dst_type), min, max),
                        location,
                    ));
                    return Err(());
                }
                return Ok(());
            }
            // 2) Type-to-type compatibility
            if src_type.is_integer() {
                if src_type.underlying_type() == dst_type.underlying_type() {
                    return Ok(());
                }
                if src_type.can_widen_to(dst_type) {
                    return Ok(());
                }
                self.error_reporter.add_error(CompilerError::type_error(
                    format!("Cannot implicitly convert from '{}' to '{}'", declared_type_to_string(src_type), declared_type_to_string(dst_type)),
                    location,
                ));
                return Err(());
            }
        }
        // Fallback: require underlying types to match
        if src_type.underlying_type() != dst_type.underlying_type() && *dst_type != SymbolType::Unknown && *src_type != SymbolType::Unknown {
            self.error_reporter.add_error(CompilerError::type_error(
                format!("Type mismatch. Expected '{}', found '{}'", declared_type_to_string(dst_type), declared_type_to_string(src_type)),
                location,
            ));
            return Err(());
        }
        Ok(())
    }

    /// Performs semantic analysis (declaration and resolution passes).
    /// Returns the potentially annotated AST or errors.
    pub fn analyze(&mut self, node: AstNode) -> Result<AstNode, ()> {
        // Perform the combined analysis traversal
        let (analyzed_node, _node_type) = self.analyze_node(node)?;
        if !self.symbol_table.errors.is_empty() {
             for (error, location) in &self.symbol_table.errors {
                 match error {
                     SymbolDeclarationError::AlreadyDeclared { name, original_location } => {
                         self.error_reporter.add_error(
                             CompilerError::semantic_error(
                                 format!("Symbol '{}' already declared in this scope", name),
                                 location.clone(), // Location of the second declaration attempt
                             ).with_hint(format!("Original declaration was here: {}", original_location))
                         );
                     }
                     // Handle other symbol table errors if added later
                 }
             }
             return Err(()); // Stop if declaration errors occurred
        }

        if self.error_reporter.has_errors() {
            Err(())
        } else {
            Ok(analyzed_node) // Return the analyzed node
        }
    }

    fn populate_symbols(&mut self, node: &AstNode) -> Result<(), ()> {
        match node {
            AstNode::Block(statements) => {
                // Blocks can sometimes introduce scopes, but let's handle that
                // explicitly in constructs like functions or loops if needed.
                // For a simple block, just traverse statements.
                for stmt in statements {
                    self.populate_symbols(stmt)?;
                }
            }
            AstNode::VariableDeclaration { name, type_annotation, value, is_mutable, is_secret, location } => {
                // Determine type (infer if necessary, check consistency)
                // This is simplified; proper type inference is complex.
                let mut declared_type = type_annotation
                    .as_ref()
                    .map(|tn| SymbolType::from_ast(tn))
                    .unwrap_or(SymbolType::Unknown);

                // TODO: Infer type from 'value' if type_annotation is None
                // TODO: Check if inferred type matches annotation if both exist

                // Handle 'secret' keyword on the type annotation itself
                let final_type = if declared_type.is_secret() || *is_secret { // Determine the final type
                    SymbolType::Secret(Box::new(declared_type.underlying_type().clone()))
                } else {
                    declared_type // Use the original declared_type (no need to clone yet)
                };

                // Calculate secrecy *before* moving final_type
                let calculated_is_secret = final_type.is_secret();

                let info = SymbolInfo {
                    name: name.clone(),
                    kind: SymbolKind::Variable { is_mutable: *is_mutable },
                    symbol_type: final_type, // final_type is moved here
                    is_secret: *is_secret || calculated_is_secret, // Use the pre-calculated flag
                    defined_at: location.clone(),
                };
                self.symbol_table.declare_symbol(info);
            },
            AstNode::FunctionDefinition { name, parameters, return_type, body, is_secret, pragmas, location, node_id } => {
                let func_name = name.as_ref().cloned().unwrap_or_else(|| {
                    // TODO: Handle anonymous functions if needed
                    format!("<anonymous_{}:{}>", location.line, location.column)
                });

                // Determine parameter types and return type for the symbol table entry
                let param_types: Vec<SymbolType> = parameters
                    .iter()
                    .map(|p| {
                        p.type_annotation
                            .as_ref()
                            .map(|tn| SymbolType::from_ast(tn))
                            .unwrap_or(SymbolType::Unknown) // Infer or error later if needed
                    })
                    .collect();

                let ret_type = return_type
                    .as_ref()
                    .map(|rt| SymbolType::from_ast(rt))
                    .unwrap_or(SymbolType::Void); // Default return type is Void

                // Handle 'secret proc' and secret return type annotation
                let final_return_type = if ret_type.is_secret() || *is_secret {
                     SymbolType::Secret(Box::new(ret_type.underlying_type().clone()))
                } else {
                    ret_type
                };

                let mut is_builtin = false;
                for pragma in pragmas {
                    if let Pragma::Simple(pragma_name, _) = pragma {
                        if pragma_name == "builtin" {
                            is_builtin = true;
                            break;
                        }
                    }
                }

                let info = SymbolInfo {
                    name: func_name.clone(),
                    kind: SymbolKind::Function {
                        parameters: param_types.clone(), // Store types for call checking
                        return_type: final_return_type.clone(),
                    },
                    symbol_type: final_return_type.clone(), // Type of the symbol is its return type
                    is_secret: *is_secret || final_return_type.is_secret(),
                    defined_at: location.clone(),
                };

                // Declare the function symbol ONLY if it's NOT a builtin
                if !is_builtin {
                    self.symbol_table.declare_symbol(info);
                }

                // --- Analyze function body in a new scope ---
                if !is_builtin { // Also skip body analysis for builtins
                    let original_scope_id = self.symbol_table.current_scope_id(); // Should be outer scope
                    self.symbol_table.enter_scope();
                    // Declare parameters within the function's scope
                    for (param, param_type) in parameters.iter().zip(param_types.iter()) {
                         let param_info = SymbolInfo {
                             name: param.name.clone(),
                             kind: SymbolKind::Variable { is_mutable: false }, // Params are immutable bindings
                             symbol_type: param_type.clone(),
                             is_secret: param_type.is_secret(), // Secrecy from type annotation
                             defined_at: param.type_annotation.as_ref().map_or_else(|| location.clone(), |n| n.location()), // Approx location
                         };
                         self.symbol_table.declare_symbol(param_info);
                    }

                    // Recursively populate symbols within the function body
                    self.populate_symbols(body)?;

                    self.symbol_table.exit_scope();
                }
            }
            AstNode::IfExpression { condition, then_branch, else_branch } => {
                self.populate_symbols(condition)?;
                self.populate_symbols(then_branch)?;
                if let Some(eb) = else_branch {
                    self.populate_symbols(eb)?;
                }
            }
            AstNode::WhileLoop { condition, body, .. } => {
                self.populate_symbols(condition)?;
                self.populate_symbols(body)?;
            }
            AstNode::ForLoop { variables, iterable, body, location: _ } => {
                // For-loops introduce a new scope for loop variables
                // 1. Traverse the iterable expression
                self.populate_symbols(iterable)?;
                // 2. Enter loop scope and declare loop variables (typed as int for now)
                self.symbol_table.enter_scope();
                for var_name in variables {
                    let info = SymbolInfo {
                        name: var_name.clone(),
                        kind: SymbolKind::Variable { is_mutable: false },
                        symbol_type: SymbolType::Int64,
                        is_secret: false,
                        defined_at: node.location(),
                    };
                    self.symbol_table.declare_symbol(info);
                }
                // 3. Traverse the loop body
                self.populate_symbols(body)?;
                // 4. Exit loop scope
                self.symbol_table.exit_scope();
            }
            AstNode::Assignment { target, value, .. } => {
                // Assignments don't declare new symbols, but we need to traverse
                // in case the value expression contains declarations (e.g., lambda)
                self.populate_symbols(target)?; // Target might be complex (field access)
                self.populate_symbols(value)?;
            }
            AstNode::Return { value: Some(expr), .. } => self.populate_symbols(expr)?,
            AstNode::DiscardStatement { expression, .. } => self.populate_symbols(expression)?,
            AstNode::FunctionCall { function, arguments, .. } => {
                self.populate_symbols(function)?;
                for arg in arguments {
                    self.populate_symbols(arg)?;
                }
            }
             AstNode::BinaryOperation { left, right, .. } => {
                 self.populate_symbols(left)?;
                 self.populate_symbols(right)?;
             }
             AstNode::UnaryOperation { operand, .. } => {
                 self.populate_symbols(operand)?;
             }
             AstNode::FieldAccess { object, .. } => {
                 self.populate_symbols(object)?;
             }
            // Other nodes that might contain declarations (Types, Imports, etc.)
            // AstNode::TypeAlias { .. } => { /* Declare type name */ }
            // AstNode::ObjectDefinition { .. } => { /* Declare type name, enter scope for fields */ }
            // AstNode::EnumDefinition { .. } => { /* Declare type name and enum members */ }
            // AstNode::Import { .. } => { /* Add imported symbols */ }

            // Leaf nodes and expressions that don't declare things
            AstNode::Literal(_) | AstNode::Identifier(_, _) | AstNode::Return { value: None, .. } => {}
            // Add other node types as needed
            _ => {
                 // Optionally print a warning for unhandled node types during population
                 // eprintln!("Warning: Unhandled AST node type in populate_symbols: {:?}", node.kind());
            }
        }
        Ok(())
    }

    /// Recursively analyzes a node, handling symbol declaration, resolution, and type checking.
    /// Returns the (potentially modified) node and its determined type.
    fn analyze_node(&mut self, node: AstNode) -> Result<(AstNode, SymbolType), ()> {
        match node {
            // --- Leaf Nodes ---
            AstNode::Literal(value) => Ok((AstNode::Literal(value.clone()), match value {
                Value::Int(_) => SymbolType::Int64,
                Value::Float(_) => SymbolType::Float,
                Value::String(_) => SymbolType::String,
                Value::Bool(_) => SymbolType::Bool,
                Value::Nil => SymbolType::Nil,
            })), 
            AstNode::Identifier(name, location) => {
                if let Some(info) = self.symbol_table.lookup_symbol(name.as_str()) {
                    // TODO: Mark symbol as used (for warnings)
                    // Return the type stored in the symbol table
                    Ok((AstNode::Identifier(name.clone(), location.clone()), info.symbol_type.clone()))
                } else {
                    self.error_reporter.add_error(
                        CompilerError::semantic_error(
                            format!("Use of undeclared identifier '{}'", name),
                            location.clone(),
                        )
                        // TODO: Add suggestion using crate::suggestions::suggest_identifier
                    );
                    Err(())
                }
            }

            // --- Declarations and Statements ---
            AstNode::Assignment { target, value, location } => {
                // Analyze target and value to get types
                let (checked_target, target_type) = self.analyze_node(*target)?;
                let (checked_value, value_type) = self.analyze_node(*value)?;

                // Only support simple identifier targets for type checking for now
                let loc = location.clone();
                if let AstNode::Identifier(_, _) = checked_target {
                    // Enforce integer compatibility (includes literal range check)
                    if self.check_integer_compat(Some(&checked_value), &value_type, &target_type, loc.clone()).is_err() {
                        return Err(());
                    }
                    Ok((AstNode::Assignment {
                        target: Box::new(checked_target),
                        value: Box::new(checked_value),
                        location: location,
                    }, SymbolType::Void))
                } else {
                    // For non-identifier targets, keep previous basic behavior (no type enforcement yet)
                    Ok((AstNode::Assignment {
                        target: Box::new(checked_target),
                        value: Box::new(checked_value),
                        location: location,
                    }, SymbolType::Void))
                }
            }

            AstNode::VariableDeclaration { name, type_annotation, value, is_mutable, is_secret, location } => {
                // 1. Analyze the value expression first (if it exists)
                let mut checked_value_node = None;
                let value_type = if let Some(val_expr) = value {
                    let (checked_val, val_type) = self.analyze_node(*val_expr)?;
                    checked_value_node = Some(Box::new(checked_val));
                    val_type
                } else {
                    SymbolType::Unknown // No value provided
                };

                // 2. Determine the declared type (from annotation or inferred from value)
                let declared_type = type_annotation
                    .as_ref()
                    .map(|tn| SymbolType::from_ast(tn))
                    .unwrap_or_else(|| value_type.clone()); // Infer if no annotation

                // 3. Check for type consistency (with integer width/range rules)
                if type_annotation.is_some() && value_type != SymbolType::Unknown {
                    if self.check_integer_compat(checked_value_node.as_deref(), &value_type, &declared_type, location.clone()).is_err() {
                        return Err(());
                    }
                }

                // 4. Handle 'secret' keyword and type secrecy
                let final_type = if declared_type.is_secret() || is_secret {
                    SymbolType::Secret(Box::new(declared_type.underlying_type().clone()))
                } else {
                    declared_type
                };
                let calculated_is_secret = final_type.is_secret();

                // 5. Declare the symbol in the current scope
                let info = SymbolInfo {
                    name: name.clone(),
                    kind: SymbolKind::Variable { is_mutable: is_mutable },
                    symbol_type: final_type,
                    is_secret: is_secret || calculated_is_secret,
                    defined_at: location.clone(),
                };
                self.symbol_table.declare_symbol(info); // Errors are collected internally

                // 6. Reconstruct the node with the checked value
                let reconstructed_node = AstNode::VariableDeclaration {
                    name,
                    type_annotation, // Keep original annotation node
                    value: checked_value_node,
                    is_mutable,
                    is_secret,
                    location,
                };
                Ok((reconstructed_node, SymbolType::Void)) // Declaration is a statement
            }

            AstNode::FunctionDefinition { name, parameters, return_type, body, is_secret, pragmas, location, node_id } => {
                let func_name = name.as_ref().cloned().unwrap_or_else(|| {
                    format!("<anonymous_{}:{}>", location.line, location.column)
                });

                // 1. Determine parameter and return types for symbol table entry
                let param_types: Vec<SymbolType> = parameters
                    .iter()
                    .map(|p| {
                        p.type_annotation
                            .as_ref()
                            .map(|tn| SymbolType::from_ast(tn))
                            .unwrap_or(SymbolType::Unknown)
                    })
                    .collect();

                let ret_type_annotation = return_type
                    .as_ref()
                    .map(|rt| SymbolType::from_ast(rt))
                    .unwrap_or(SymbolType::Void);

                // Handle 'secret proc' and secret return type annotation
                let final_return_type = if ret_type_annotation.is_secret() || is_secret {
                     SymbolType::Secret(Box::new(ret_type_annotation.underlying_type().clone()))
                } else {
                    ret_type_annotation
                };

                // Check for pragmas like 'builtin'
                let mut is_builtin = false;
                for pragma in &pragmas {
                    if let Pragma::Simple(pragma_name, _) = pragma {
                        if pragma_name == "builtin" { is_builtin = true; break; }
                    }
                }

                // 2. Declare the function symbol in the *current* (outer) scope
                //    (Unless it's a builtin, builtins are pre-declared)
                if !is_builtin {
                    let info = SymbolInfo {
                        name: func_name.clone(),
                        kind: SymbolKind::Function {
                            parameters: param_types.clone(),
                            return_type: final_return_type.clone(),
                        },
                        symbol_type: final_return_type.clone(), // Type of symbol is its return type
                        is_secret: is_secret || final_return_type.is_secret(),
                        defined_at: location.clone(),
                    };
                    self.symbol_table.declare_symbol(info);
                }

                // 3. Analyze function body in a new scope (if not builtin)
                let checked_body = if !is_builtin {
                    self.symbol_table.enter_scope();
                    let previous_return_type = self.current_function_return_type.replace(final_return_type.clone());

                    // Declare parameters within the function's scope
                    for (param, param_type) in parameters.iter().zip(param_types.iter()) {
                         let param_info = SymbolInfo {
                             name: param.name.clone(),
                             kind: SymbolKind::Variable { is_mutable: false }, // Params are immutable
                             symbol_type: param_type.clone(),
                             is_secret: param_type.is_secret(),
                             defined_at: param.type_annotation.as_ref().map_or_else(|| location.clone(), |n| n.location()),
                         };
                         self.symbol_table.declare_symbol(param_info);
                    }

                    // Recursively analyze the body
                    let (checked_body_node, _body_type) = self.analyze_node(*body)?;
                    // TODO: Check if all code paths return the correct type (more complex analysis)

                    self.current_function_return_type = previous_return_type;
                    self.symbol_table.exit_scope();
                    Box::new(checked_body_node)
                } else {
                    body // Keep original body for builtins (it's not analyzed)
                };

                // 4. Reconstruct the node
                let reconstructed_node = AstNode::FunctionDefinition {
                    name, parameters, return_type, body: checked_body, is_secret, pragmas, location, node_id
                };
                Ok((reconstructed_node, SymbolType::Void)) // Definition is a statement
            }

            // --- Expressions and Control Flow ---
            AstNode::IfExpression { condition, then_branch, else_branch } => {
                // Analyze condition and enforce that branching on secret is not supported
                let (checked_condition, cond_type) = self.analyze_node(*condition)?;
                if cond_type.is_secret() {
                    self.error_reporter.add_error(CompilerError::semantic_error(
                        "Branching with secret values isn't supported yet (secret condition in 'if')",
                        checked_condition.location(),
                    ));
                    return Err(());
                }
                // Optional: ensure condition is bool (underlying type)
                if cond_type.underlying_type() != &SymbolType::Bool {
                    self.error_reporter.add_error(CompilerError::type_error(
                        "If-condition must be of type 'bool'",
                        checked_condition.location(),
                    ));
                    return Err(());
                }

                // Analyze branches
                let (checked_then, _then_ty) = self.analyze_node(*then_branch)?;
                let checked_else = if let Some(eb) = else_branch {
                    let (c_eb, _else_ty) = self.analyze_node(*eb)?;
                    Some(Box::new(c_eb))
                } else { None };

                Ok((AstNode::IfExpression {
                    condition: Box::new(checked_condition),
                    then_branch: Box::new(checked_then),
                    else_branch: checked_else,
                }, SymbolType::Unknown))
            }
            AstNode::WhileLoop { condition, body, location } => {
                // Analyze condition and error if it's secret
                let (checked_condition, cond_type) = self.analyze_node(*condition)?;
                if cond_type.is_secret() {
                    self.error_reporter.add_error(CompilerError::semantic_error(
                        "Branching with secret values isn't supported yet (secret condition in 'while')",
                        checked_condition.location(),
                    ));
                    return Err(());
                }
                if cond_type.underlying_type() != &SymbolType::Bool {
                    self.error_reporter.add_error(CompilerError::type_error(
                        "While-condition must be of type 'bool'",
                        checked_condition.location(),
                    ));
                    return Err(());
                }
                let (checked_body, _body_ty) = self.analyze_node(*body)?;
                Ok((AstNode::WhileLoop { condition: Box::new(checked_condition), body: Box::new(checked_body), location }, SymbolType::Void))
            }
            AstNode::Block(statements) => {
                // Blocks don't create scopes by default in this design.
                // Scopes are handled by functions, loops (if needed), etc.
                let mut checked_statements = Vec::new();
                let mut last_type = SymbolType::Void; // Default for empty block
                // Important: continue analyzing all statements even if some have errors
                for stmt in statements {
                    match self.analyze_node(stmt) {
                        Ok((checked_stmt, stmt_type)) => {
                            last_type = stmt_type; // Type of block is type of last successful statement
                            checked_statements.push(checked_stmt);
                        }
                        Err(()) => {
                            // Preserve the original statement to keep AST shape and continue
                            // We purposely do not update last_type here.
                            // Note: We cannot reconstruct the original `stmt` here because it's moved by match,
                            // so we push a placeholder no-op statement to maintain block length.
                            // If a proper NoOp node exists, prefer that; otherwise use an empty literal.
                            checked_statements.push(AstNode::Literal(Value::Nil));
                        }
                    }
                }
                Ok((AstNode::Block(checked_statements), last_type))
            }

            AstNode::ForLoop { variables, iterable, body, location } => {
                // Support only single variable numeric ranges for now: for i in a .. b
                if variables.len() != 1 {
                    self.error_reporter.add_error(CompilerError::semantic_error(
                        "For-loop with multiple variables not supported yet",
                        location.clone(),
                    ));
                    return Err(());
                }
                // Analyze iterable
                let (checked_iterable, _iter_type) = self.analyze_node(*iterable)?;
                // Check it is a range binary op
                match &checked_iterable {
                    AstNode::BinaryOperation { op, left: _, right: _, location: op_loc } if op == ".." => {
                        // ok
                    }
                    _ => {
                        self.error_reporter.add_error(CompilerError::semantic_error(
                            "Unsupported for-loop iterable; expected 'a .. b' range",
                            checked_iterable.location(),
                        ));
                        return Err(());
                    }
                }
                // Enter loop scope and declare the loop variable as int (clear)
                self.symbol_table.enter_scope();
                let var_name = variables[0].clone();
                let var_info = SymbolInfo {
                    name: var_name.clone(),
                    kind: SymbolKind::Variable { is_mutable: false },
                    symbol_type: SymbolType::Int64,
                    is_secret: false,
                    defined_at: location.clone(),
                };
                self.symbol_table.declare_symbol(var_info);

                // Analyze body within scope
                let (checked_body, _body_type) = self.analyze_node(*body)?;

                // Exit loop scope
                self.symbol_table.exit_scope();

                Ok((AstNode::ForLoop {
                    variables: vec![var_name],
                    iterable: Box::new(checked_iterable),
                    body: Box::new(checked_body),
                    location,
                }, SymbolType::Void))
            }

            AstNode::Return { value: ref maybe_expr, location: ref ret_loc } => {
                 let (checked_expr_node, return_value_type) = match maybe_expr {
                     Some(expr) => {
                         let (checked_expr, expr_type) = self.analyze_node(*expr.clone())?;
                         (Some(Box::new(checked_expr)), expr_type)
                     }
                     None => (None, SymbolType::Void),
                 };

                 let expected_ret = self.current_function_return_type.clone();
                 match expected_ret {
                     Some(expected) => {
                         // Integer-aware compatibility (includes literal range check)
                         let loc = node.location();
                         if self.check_integer_compat(checked_expr_node.as_deref(), &return_value_type, &expected, loc).is_err() {
                             return Err(());
                         }
                         // TODO: Check secrecy compatibility (cannot return clear from secret context, etc.)
                     }
                     None => {
                         self.error_reporter.add_error(CompilerError::semantic_error(
                             "'return' statement outside of function",
                             node.location(),
                         ));
                         return Err(());
                     }
                 }
                 Ok((AstNode::Return { value: checked_expr_node, location: ret_loc.clone() }, SymbolType::Void)) // Return is a statement
             }

            AstNode::FunctionCall { function, arguments, location, resolved_return_type: _ } => { // Ignore existing resolved_return_type
                // 1. Analyze the function expression itself (usually an identifier)
                let (checked_function_node, function_expr_type) = self.analyze_node(*function)?;

                // 2. Analyze arguments
                let mut checked_arguments = Vec::with_capacity(arguments.len());
                let mut argument_types = Vec::with_capacity(arguments.len());
                for arg_node in arguments {
                    let (checked_arg, arg_type) = self.analyze_node(arg_node)?;
                    checked_arguments.push(checked_arg);
                    argument_types.push(arg_type);
                }

                // 3. Determine the actual function symbol and its type
                let (function_name, function_info) = match &checked_function_node {
                    AstNode::Identifier(name, loc) => {
                        if let Some(info) = self.symbol_table.lookup_symbol(name) {
                            (name.clone(), info.clone()) // Clone info for use
                        } else {
                            self.error_reporter.add_error(CompilerError::semantic_error(
                                format!("Use of undeclared function '{}'", name),
                                loc.clone(),
                            ));
                            return Err(());
                        }
                    }
                    // TODO: Handle other callable types (e.g., function pointers, methods)
                    _ => {
                        self.error_reporter.add_error(CompilerError::type_error(
                            "Expression is not callable",
                            checked_function_node.location(),
                        ));
                        return Err(());
                    }
                };

                // 4. Check if the symbol is actually a function and validate arguments
                let (expected_param_types, return_type) = match &function_info.kind {
                    SymbolKind::Function { parameters, return_type } | SymbolKind::BuiltinFunction { parameters, return_type } => {
                        // TODO: Implement proper argument count and type checking
                        // if parameters.len() != argument_types.len() { ... error ... }
                        // for (expected, actual) in parameters.iter().zip(argument_types.iter()) { ... check type ... }
                        (parameters.clone(), return_type.clone())
                    }
                    _ => {
                        self.error_reporter.add_error(CompilerError::type_error(
                            format!("'{}' is not a function", function_name),
                            checked_function_node.location(),
                        ));
                        return Err(());
                    }
                };

                // 5. Validate arguments using integer compatibility rules
                for (idx, (expected_ty, actual_ty)) in expected_param_types.iter().zip(argument_types.iter()).enumerate() {
                    let mut arg_loc = checked_arguments[idx].location();
                    if arg_loc.line == 0 { arg_loc = location.clone(); }
                    if self.check_integer_compat(Some(&checked_arguments[idx]), actual_ty, expected_ty, arg_loc).is_err() {
                        return Err(());
                    }
                }

                // 6. Reconstruct the node with checked parts and resolved return type
                let reconstructed_node = AstNode::FunctionCall {
                    function: Box::new(checked_function_node),
                    arguments: checked_arguments,
                    location,
                    resolved_return_type: Some(return_type.clone()), // Store the resolved type
                };

                Ok((reconstructed_node, return_type)) // Type of the call is the function's return type
            }

            AstNode::CommandCall { command, arguments, location, resolved_return_type } => {
                // 1. Analyze the command expression (usually an identifier)
                let (checked_command_node, command_expr_type) = self.analyze_node(*command)?;

                // 2. Analyze arguments
                let mut checked_arguments = Vec::with_capacity(arguments.len());
                let mut argument_types = Vec::with_capacity(arguments.len());
                for arg_node in arguments {
                    let (checked_arg, arg_type) = self.analyze_node(arg_node)?;
                    checked_arguments.push(checked_arg);
                    argument_types.push(arg_type);
                }

                // 3. Determine the actual function symbol and its type from the command
                let (function_name, function_info) = match &checked_command_node {
                    AstNode::Identifier(name, loc) => {
                        if let Some(info) = self.symbol_table.lookup_symbol(name) {
                            (name.clone(), info.clone())
                        } else {
                            self.error_reporter.add_error(CompilerError::semantic_error(
                                format!("Use of undeclared function '{}' in command call", name),
                                loc.clone(),
                            ));
                            return Err(());
                        }
                    }
                    _ => {
                        self.error_reporter.add_error(CompilerError::type_error(
                            "Command expression is not callable",
                            checked_command_node.location(),
                        ));
                        return Err(());
                    }
                };

                // 4. Check if the symbol is a function and validate arguments (similar to FunctionCall)
                let (expected_param_types, return_type) = match &function_info.kind {
                     SymbolKind::Function { parameters, return_type } | SymbolKind::BuiltinFunction { parameters, return_type } => {
                        // TODO: Implement proper argument count/type checking for command calls (UFCS context)
                        (parameters.clone(), return_type.clone())
                    }
                    _ => {
                        self.error_reporter.add_error(CompilerError::type_error(
                            format!("'{}' is not a function (used in command call)", function_name),
                            checked_command_node.location(),
                        ));
                        return Err(());
                    }
                };

                // 5. Validate arguments using integer compatibility rules (same as function calls)
                for (idx, (expected_ty, actual_ty)) in expected_param_types.iter().zip(argument_types.iter()).enumerate() {
                    let arg_loc = checked_arguments[idx].location();
                    if self.check_integer_compat(Some(&checked_arguments[idx]), actual_ty, expected_ty, arg_loc).is_err() {
                        return Err(());
                    }
                }

                // 6. Reconstruct the node with checked parts and resolved return type
                let reconstructed_node = AstNode::CommandCall {
                    command: Box::new(checked_command_node),
                    arguments: checked_arguments,
                    location,
                    resolved_return_type: Some(return_type.clone()), // Store the resolved type
                };
                Ok((reconstructed_node, return_type)) // Type of the call is the function's return type
            }

            // Fallback for unhandled nodes
            _ => {
                // For now, just return the node as is with Unknown type.
                Ok((node, SymbolType::Unknown))
            }
        }
    }

    // --- Helper Functions ---

}

// Helper to get a string representation of a SymbolType for error messages
// TODO: Move this into SymbolType impl or a dedicated formatter module
fn declared_type_to_string(sym_type: &SymbolType) -> String {
    match sym_type {
        // Signed integers
        SymbolType::Int64 => "int64".to_string(),
        SymbolType::Int32 => "int32".to_string(),
        SymbolType::Int16 => "int16".to_string(),
        SymbolType::Int8 => "int8".to_string(),
        // Unsigned integers
        SymbolType::UInt64 => "uint64".to_string(),
        SymbolType::UInt32 => "uint32".to_string(),
        SymbolType::UInt16 => "uint16".to_string(),
        SymbolType::UInt8 => "uint8".to_string(),
        SymbolType::Float => "float".to_string(),
        SymbolType::String => "string".to_string(),
        SymbolType::Bool => "bool".to_string(),
        SymbolType::Nil => "nil".to_string(),
        SymbolType::Void => "void".to_string(),
        SymbolType::Secret(inner) => format!("secret {}", declared_type_to_string(inner)),
        SymbolType::TypeName(name) => name.clone(),
        SymbolType::Unknown => "<unknown>".to_string(),
    }
}

/// Public entry point for semantic analysis
pub fn analyze(
    ast: AstNode,
    error_reporter: &mut ErrorReporter,
    filename: &str,
) -> Result<AstNode, ()> {
    let mut analyzer = SemanticAnalyzer::new(error_reporter, filename);
    analyzer.analyze(ast)
}
