use crate::ast::AstNode;
use crate::errors::SourceLocation;
use std::collections::HashMap;

/// Represents the kind of a symbol (variable, function, type, etc.)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SymbolKind {
    Variable { is_mutable: bool },
    Function { parameters: Vec<SymbolType>, return_type: SymbolType }, // Simplified for now
    Type,
    BuiltinFunction { parameters: Vec<SymbolType>, return_type: SymbolType },
    Module,
    // Add more kinds as needed (e.g., EnumMember, Field)
}

/// Represents the type of a symbol (primitive or user-defined)
/// TODO: This needs to be more sophisticated to handle generics, objects, etc.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SymbolType {
    Int,
    Float,
    String,
    Bool,
    Nil,
    Void, // For functions returning nothing
    Secret(Box<SymbolType>),
    TypeName(String), // For user-defined types
    Unknown, // Placeholder during analysis
    // Add complex types: Array, Tuple, Object, FunctionSignature, etc.
}

impl SymbolType {
    /// Checks if the type is secret.
    pub fn is_secret(&self) -> bool {
        matches!(self, SymbolType::Secret(_))
    }

    /// Gets the underlying type if secret.
    pub fn underlying_type(&self) -> &SymbolType {
        match self {
            SymbolType::Secret(t) => t.underlying_type(),
            _ => self,
        }
    }

    /// Creates a SymbolType from an AST node representing a type annotation.
    /// This is a simplified version.
    pub fn from_ast(node: &AstNode) -> Self {
        match node {
            AstNode::Identifier(name, _) => match name.as_str() {
                "int" => SymbolType::Int,
                "float" => SymbolType::Float,
                "string" => SymbolType::String,
                "bool" => SymbolType::Bool,
                "void" => SymbolType::Void, // Assuming 'void' keyword exists or is inferred
                "nil" => SymbolType::Nil,
                _ => SymbolType::TypeName(name.clone()),
            },
            AstNode::SecretType(inner_node) => {
                SymbolType::Secret(Box::new(SymbolType::from_ast(inner_node)))
            }
            // TODO: Handle ListType, TupleType, FunctionType, etc.
            _ => SymbolType::Unknown, // Cannot determine type from this node
        }
    }
}

/// Information stored for each symbol in the table.
#[derive(Debug, Clone)]
pub struct SymbolInfo {
    pub name: String,
    pub kind: SymbolKind,
    pub symbol_type: SymbolType, // Resolved type
    pub is_secret: bool, // Can be derived from symbol_type, but useful for quick checks.
    pub defined_at: SourceLocation,
    // pub scope_level: usize, // Could be useful for debugging
    // pub used: bool, // For unused variable warnings
}

/// Error type for symbol declaration issues within a scope.
#[derive(Debug, Clone)]
pub enum SymbolDeclarationError {
    AlreadyDeclared {
        name: String,
        original_location: SourceLocation, // Location of the first declaration
    },
}

/// Represents a single scope (e.g., global, function, block).
#[derive(Debug, Clone, Default)]
pub struct Scope {
    symbols: HashMap<String, SymbolInfo>,
    parent_scope_id: Option<usize>, // ID of the enclosing scope
    scope_id: usize,
    // pub children_scope_ids: Vec<usize>, // For debugging/visualization
}

impl Scope {
    fn new(scope_id: usize, parent_scope_id: Option<usize>) -> Self {
        Scope {
            symbols: HashMap::new(),
            parent_scope_id,
            scope_id,
            // children_scope_ids: Vec::new(),
        }
    }

    /// Declares a symbol in this scope. Returns error if already declared.
    fn declare(&mut self, info: SymbolInfo) -> Result<(), SymbolDeclarationError> {
        if let Some(existing_info) = self.symbols.get(&info.name) {
            Err(SymbolDeclarationError::AlreadyDeclared {
                name: info.name.clone(),
                original_location: existing_info.defined_at.clone(),
            })
        } else {
            // Store the new symbol
            self.symbols.insert(info.name.clone(), info);
            Ok(())
        }
    }

    /// Looks up a symbol only in this specific scope.
    fn lookup_local(&self, name: &str) -> Option<&SymbolInfo> {
        self.symbols.get(name)
    }
}

/// The main Symbol Table structure, managing multiple scopes.
#[derive(Debug)]
pub struct SymbolTable {
    scopes: Vec<Scope>,         // Stores all scopes
    current_scope_id: usize,    // ID of the currently active scope
    next_scope_id: usize,       // Counter for assigning unique scope IDs
    pub errors: Vec<(SymbolDeclarationError, SourceLocation)>, // Store error and location of the failed declaration
}

impl SymbolTable {
    pub fn new() -> Self {
        let mut table = SymbolTable {
            scopes: Vec::new(),
            current_scope_id: 0,
            next_scope_id: 1, // 0 is global scope
            errors: Vec::new(),
        };
        // Create the global scope (ID 0)
        table.scopes.push(Scope::new(0, None));
        table.add_builtins();
        table
    }

    /// Adds built-in functions and types to the global scope.
    fn add_builtins(&mut self) {
        let global_scope = &mut self.scopes[0]; // Global scope is always at index 0

        // Example: print function
        let print_info = SymbolInfo {
            name: "print".to_string(),
            kind: SymbolKind::BuiltinFunction {
                parameters: vec![SymbolType::String],
                return_type: SymbolType::Void,
            },
            symbol_type: SymbolType::Void, // Type of the function itself (its return type here)
            is_secret: false,
            defined_at: SourceLocation::default(), // Mark as built-in location
        };
        if let Err(e) = global_scope.declare(print_info) {
             self.errors.push((e, SourceLocation::default())); // Use default location for internal errors
        }

        // Add built-in types (int, string, bool, float, nil, void)
        for type_name in ["int", "string", "bool", "float", "nil", "void"] {
             let type_info = SymbolInfo {
                 name: type_name.to_string(),
                 kind: SymbolKind::Type,
                 symbol_type: SymbolType::Unknown, // Type of a type is itself? Or a meta-type?
                 is_secret: false,
                 defined_at: SourceLocation::default(),
             };
             if let Err(e) = global_scope.declare(type_info) {
                 self.errors.push((e, SourceLocation::default()));
             }
        }

        // Add more built-ins: len, assert, etc.
    }

    /// Enters a new scope nested within the current one.
    pub fn enter_scope(&mut self) {
        let new_scope_id = self.next_scope_id;
        self.next_scope_id += 1;
        let new_scope = Scope::new(new_scope_id, Some(self.current_scope_id));
        self.scopes.push(new_scope);
        // Update parent's children list (if needed for debugging)
        // if let Some(parent_scope) = self.scopes.get_mut(self.current_scope_id) {
        //     parent_scope.children_scope_ids.push(new_scope_id);
        // }
        self.current_scope_id = new_scope_id;
    }

    /// Exits the current scope and returns to the parent scope.
    /// Panics if trying to exit the global scope.
    pub fn exit_scope(&mut self) {
        let current_scope = self.scopes.get(self.current_scope_id)
            .expect("Internal error: Current scope ID invalid");
        self.current_scope_id = current_scope.parent_scope_id
            .expect("Cannot exit the global scope");
    }

    /// Sets the current scope ID. Used for switching contexts during analysis.
    /// Panics if the provided ID is invalid.
    pub fn set_current_scope(&mut self, scope_id: usize) {
        if scope_id >= self.scopes.len() {
            panic!("Internal error: Attempted to set invalid scope ID {}", scope_id);
        }
        self.current_scope_id = scope_id;
    }

    /// Declares a symbol in the current scope.
    pub fn declare_symbol(&mut self, info: SymbolInfo) {
        let current_scope = self.scopes.get_mut(self.current_scope_id)
            .expect("Internal error: Current scope ID invalid during declaration");
        let location = info.defined_at.clone(); // Get location before moving info
        if let Err(e) = current_scope.declare(info) {
            self.errors.push((e, location)); // Store error and location of failed declaration
        }
    }

    /// Looks up a symbol starting from the current scope and walking up the chain.
    pub fn lookup_symbol(&self, name: &str) -> Option<&SymbolInfo> {
        let mut scope_id_to_check = Some(self.current_scope_id);
        while let Some(id) = scope_id_to_check {
            let scope = self.scopes.get(id)
                .expect("Internal error: Invalid scope ID during lookup");
            if let Some(info) = scope.lookup_local(name) {
                return Some(info);
            }
            scope_id_to_check = scope.parent_scope_id;
        }
        None // Not found in any scope
    }

    /// Gets the current scope's ID.
    pub fn current_scope_id(&self) -> usize {
        self.current_scope_id
    }
}
