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
    // Signed integers
    Int64,
    Int32,
    Int16,
    Int8,
    // Unsigned integers
    UInt64,
    UInt32,
    UInt16,
    UInt8,
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

    /// Returns true if this is any integer type (signed or unsigned).
    pub fn is_integer(&self) -> bool {
        matches!(self.underlying_type(),
            SymbolType::Int64 | SymbolType::Int32 | SymbolType::Int16 | SymbolType::Int8 |
            SymbolType::UInt64 | SymbolType::UInt32 | SymbolType::UInt16 | SymbolType::UInt8)
    }

    /// Returns true if integer and signed; false if integer and unsigned; otherwise false.
    pub fn is_signed(&self) -> bool {
        match self.underlying_type() {
            SymbolType::Int64 | SymbolType::Int32 | SymbolType::Int16 | SymbolType::Int8 => true,
            SymbolType::UInt64 | SymbolType::UInt32 | SymbolType::UInt16 | SymbolType::UInt8 => false,
            _ => false,
        }
    }

    /// Returns bit width for integer types.
    pub fn bit_width(&self) -> Option<u8> {
        match self.underlying_type() {
            SymbolType::Int64 | SymbolType::UInt64 => Some(64),
            SymbolType::Int32 | SymbolType::UInt32 => Some(32),
            SymbolType::Int16 | SymbolType::UInt16 => Some(16),
            SymbolType::Int8  | SymbolType::UInt8  => Some(8),
            _ => None,
        }
    }

    /// Returns the inclusive min value for this integer type as i128.
    pub fn min_value_i128(&self) -> Option<i128> {
        if !self.is_integer() { return None; }
        let bits_u8 = self.bit_width().unwrap();
        let bits: u32 = bits_u8 as u32;
        if self.is_signed() {
            Some(-(1i128 << (bits - 1)))
        } else {
            Some(0)
        }
    }

    /// Returns the inclusive max value for this integer type as i128.
    pub fn max_value_i128(&self) -> Option<i128> {
        if !self.is_integer() { return None; }
        let bits_u8 = self.bit_width().unwrap();
        let bits: u32 = bits_u8 as u32;
        if self.is_signed() {
            Some((1i128 << (bits - 1)) - 1)
        } else {
            Some((1i128 << bits) - 1)
        }
    }

    /// Checks if a literal value fits within this integer type.
    pub fn fits_literal_i128(&self, value: i128) -> bool {
        match (self.min_value_i128(), self.max_value_i128()) {
            (Some(min), Some(max)) => value >= min && value <= max,
            _ => false,
        }
    }

    /// Returns true if converting any value of `self` to `target` is safe (implicit widening).
    /// Conservative: allows signed->signed widening, unsigned->unsigned widening,
    /// and unsigned->signed only if target bit width > source bit width.
    pub fn can_widen_to(&self, target: &SymbolType) -> bool {
        let src = self.underlying_type();
        let dst = target.underlying_type();
        if !src.is_integer() || !dst.is_integer() { return false; }
        let src_bits = src.bit_width().unwrap();
        let dst_bits = dst.bit_width().unwrap();
        match (src.is_signed(), dst.is_signed()) {
            (true, true) => src_bits <= dst_bits,
            (false, false) => src_bits <= dst_bits,
            (false, true) => src_bits < dst_bits, // e.g., u8 -> i16 (ok), u8 -> i8 (not safe for all values)
            (true, false) => false, // signed to unsigned not always safe
        }
    }

    /// Creates a SymbolType from an AST node representing a type annotation.
    /// This is a simplified version.
    pub fn from_ast(node: &AstNode) -> Self {
        match node {
            AstNode::Identifier(name, _) => match name.as_str() {
                // Signed ints (aliases)
                "i64" | "int64" => SymbolType::Int64,
                "i32" | "int32" => SymbolType::Int32,
                "i16" | "int16" => SymbolType::Int16,
                "i8"  | "int8"  => SymbolType::Int8,
                // Unsigned ints (aliases)
                "u64" | "uint64" => SymbolType::UInt64,
                "u32" | "uint32" => SymbolType::UInt32,
                "u16" | "uint16" => SymbolType::UInt16,
                "u8"  | "uint8"  => SymbolType::UInt8,
                // Other primitives
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

        // Add built-in types (integers, string, bool, float, nil, void)
        for type_name in [
            "int64", "int32", "int16", "int8",
            "uint64", "uint32", "uint16", "uint8",
            "string", "bool", "float", "nil", "void"
        ] {
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
