use crate::ast::AstNode;
use crate::errors::SourceLocation;
use std::collections::HashMap;
use std::fmt;

/// Represents the kind of a symbol (variable, function, type, etc.)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SymbolKind {
    Variable { is_mutable: bool },
    Function { parameters: Vec<SymbolType>, return_type: SymbolType }, // Simplified for now
    Type,
    BuiltinFunction { parameters: Vec<SymbolType>, return_type: SymbolType },
    Module,
    /// A builtin object type (like ClientStore) - the name refers to the BuiltinObjectInfo
    BuiltinObject { object_type_name: String },
    // Add more kinds as needed (e.g., EnumMember, Field)
}

/// Information about a method on a builtin object
#[derive(Debug, Clone)]
pub struct ObjectMethodInfo {
    /// Parameters for the method (excludes the implicit receiver/self)
    pub parameters: Vec<SymbolType>,
    /// Return type of the method
    pub return_type: SymbolType,
    /// The qualified name used in bytecode (e.g., "ClientStore.take_share")
    pub qualified_name: String,
}

/// Information about a builtin object type (like ClientStore)
#[derive(Debug, Clone)]
pub struct BuiltinObjectInfo {
    /// The name of the object type
    pub name: String,
    /// Methods available on this object type
    pub methods: HashMap<String, ObjectMethodInfo>,
}

/// Represents the type of a symbol (primitive or user-defined)
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
    // Collection types
    List(Box<SymbolType>),                    // List[T]
    Dict(Box<SymbolType>, Box<SymbolType>),   // Dict[K, V]
    Object(String),                            // Named object type
    Generic(String, Vec<SymbolType>),          // Generic type: Name[T1, T2, ...]
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

    /// Gets the element type for list types.
    pub fn element_type(&self) -> Option<&SymbolType> {
        match self.underlying_type() {
            SymbolType::List(elem) => Some(elem),
            _ => None,
        }
    }

    /// Checks if the type is indexable (list, string, dict).
    pub fn is_indexable(&self) -> bool {
        matches!(self.underlying_type(),
            SymbolType::List(_) | SymbolType::String | SymbolType::Dict(_, _))
    }

    /// Checks if the type is a collection (list or dict).
    pub fn is_collection(&self) -> bool {
        matches!(self.underlying_type(),
            SymbolType::List(_) | SymbolType::Dict(_, _))
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
                "i64" | "int64" | "int" => SymbolType::Int64,
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
            AstNode::ListType(element_type) => {
                SymbolType::List(Box::new(SymbolType::from_ast(element_type)))
            }
            AstNode::DictType { key_type, value_type, .. } => {
                SymbolType::Dict(
                    Box::new(SymbolType::from_ast(key_type)),
                    Box::new(SymbolType::from_ast(value_type))
                )
            }
            AstNode::GenericType { base_name, type_params, .. } => {
                let params: Vec<SymbolType> = type_params.iter().map(SymbolType::from_ast).collect();
                SymbolType::Generic(base_name.clone(), params)
            }
            _ => SymbolType::Unknown, // Cannot determine type from this node
        }
    }
}

impl fmt::Display for SymbolType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SymbolType::Int64 => write!(f, "int64"),
            SymbolType::Int32 => write!(f, "int32"),
            SymbolType::Int16 => write!(f, "int16"),
            SymbolType::Int8 => write!(f, "int8"),
            SymbolType::UInt64 => write!(f, "uint64"),
            SymbolType::UInt32 => write!(f, "uint32"),
            SymbolType::UInt16 => write!(f, "uint16"),
            SymbolType::UInt8 => write!(f, "uint8"),
            SymbolType::Float => write!(f, "float"),
            SymbolType::String => write!(f, "string"),
            SymbolType::Bool => write!(f, "bool"),
            SymbolType::Nil => write!(f, "nil"),
            SymbolType::Void => write!(f, "void"),
            SymbolType::Secret(inner) => write!(f, "secret {}", inner),
            SymbolType::TypeName(name) => write!(f, "{}", name),
            SymbolType::Unknown => write!(f, "<unknown>"),
            SymbolType::List(elem) => write!(f, "List[{}]", elem),
            SymbolType::Dict(key, val) => write!(f, "Dict[{}, {}]", key, val),
            SymbolType::Object(name) => write!(f, "{}", name),
            SymbolType::Generic(name, params) => {
                write!(f, "{}[", name)?;
                for (i, param) in params.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", param)?;
                }
                write!(f, "]")
            }
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
    /// Registry of builtin object types (like ClientStore)
    pub builtin_objects: HashMap<String, BuiltinObjectInfo>,
    /// Method-to-function suggestions for common method names that should be functions.
    /// Maps method name (e.g., "length") to suggestion string (e.g., "array_length(arr)").
    method_suggestions: HashMap<String, String>,
}

impl SymbolTable {
    pub fn new() -> Self {
        let mut table = SymbolTable {
            scopes: Vec::new(),
            current_scope_id: 0,
            next_scope_id: 1, // 0 is global scope
            errors: Vec::new(),
            builtin_objects: HashMap::new(),
            method_suggestions: HashMap::new(),
        };
        // Create the global scope (ID 0)
        table.scopes.push(Scope::new(0, None));
        table.add_builtins();
        table
    }

    /// Looks up a method suggestion for when users try to use method syntax.
    /// Returns a suggestion string if the method name has a known function equivalent.
    pub fn get_method_suggestion(&self, method_name: &str) -> Option<&String> {
        self.method_suggestions.get(method_name)
    }

    /// Looks up a builtin object type by name
    pub fn lookup_builtin_object(&self, name: &str) -> Option<&BuiltinObjectInfo> {
        self.builtin_objects.get(name)
    }

    /// Looks up a method on a builtin object type
    pub fn lookup_builtin_method(&self, object_name: &str, method_name: &str) -> Option<&ObjectMethodInfo> {
        self.builtin_objects.get(object_name)
            .and_then(|obj| obj.methods.get(method_name))
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

        // Add ClientStore as a builtin object with methods
        let mut client_store_methods = HashMap::new();
        client_store_methods.insert("take_share".to_string(), ObjectMethodInfo {
            parameters: vec![SymbolType::Int64, SymbolType::Int64],
            return_type: SymbolType::Secret(Box::new(SymbolType::Int64)),
            qualified_name: "ClientStore.take_share".to_string(),
        });
        client_store_methods.insert("take_share_fixed".to_string(), ObjectMethodInfo {
            parameters: vec![SymbolType::Int64, SymbolType::Int64],
            return_type: SymbolType::Secret(Box::new(SymbolType::Float)),
            qualified_name: "ClientStore.take_share_fixed".to_string(),
        });
        client_store_methods.insert("get_number_clients".to_string(), ObjectMethodInfo {
            parameters: vec![],
            return_type: SymbolType::Int64,
            qualified_name: "ClientStore.get_number_clients".to_string(),
        });

        // Register the builtin object
        self.builtin_objects.insert("ClientStore".to_string(), BuiltinObjectInfo {
            name: "ClientStore".to_string(),
            methods: client_store_methods,
        });

        // Add ClientStore as a global symbol (singleton instance)
        let client_store_info = SymbolInfo {
            name: "ClientStore".to_string(),
            kind: SymbolKind::BuiltinObject { object_type_name: "ClientStore".to_string() },
            symbol_type: SymbolType::Object("ClientStore".to_string()),
            is_secret: false,
            defined_at: SourceLocation::default(),
        };
        if let Err(e) = global_scope.declare(client_store_info) {
            self.errors.push((e, SourceLocation::default()));
        }

        // =====================================================================
        // Share - Secret share operations (matches VM mpc_builtins.rs)
        // =====================================================================
        let mut share_methods = HashMap::new();

        // Share.from_clear(value) -> Object (share object)
        share_methods.insert("from_clear".to_string(), ObjectMethodInfo {
            parameters: vec![SymbolType::Int64], // Also accepts Float, Bool at runtime
            return_type: SymbolType::Object("Share".to_string()),
            qualified_name: "Share.from_clear".to_string(),
        });

        // Share.from_clear_int(value, bit_length) -> Object
        share_methods.insert("from_clear_int".to_string(), ObjectMethodInfo {
            parameters: vec![SymbolType::Int64, SymbolType::Int64],
            return_type: SymbolType::Object("Share".to_string()),
            qualified_name: "Share.from_clear_int".to_string(),
        });

        // Share.from_clear_fixed(value, total_bits, frac_bits) -> Object
        share_methods.insert("from_clear_fixed".to_string(), ObjectMethodInfo {
            parameters: vec![SymbolType::Float, SymbolType::Int64, SymbolType::Int64],
            return_type: SymbolType::Object("Share".to_string()),
            qualified_name: "Share.from_clear_fixed".to_string(),
        });

        // Share.add(share1, share2) -> Object (local operation)
        share_methods.insert("add".to_string(), ObjectMethodInfo {
            parameters: vec![
                SymbolType::Object("Share".to_string()),
                SymbolType::Object("Share".to_string()),
            ],
            return_type: SymbolType::Object("Share".to_string()),
            qualified_name: "Share.add".to_string(),
        });

        // Share.sub(share1, share2) -> Object (local operation)
        share_methods.insert("sub".to_string(), ObjectMethodInfo {
            parameters: vec![
                SymbolType::Object("Share".to_string()),
                SymbolType::Object("Share".to_string()),
            ],
            return_type: SymbolType::Object("Share".to_string()),
            qualified_name: "Share.sub".to_string(),
        });

        // Share.neg(share) -> Object (local operation)
        share_methods.insert("neg".to_string(), ObjectMethodInfo {
            parameters: vec![SymbolType::Object("Share".to_string())],
            return_type: SymbolType::Object("Share".to_string()),
            qualified_name: "Share.neg".to_string(),
        });

        // Share.add_scalar(share, scalar) -> Object (local operation)
        share_methods.insert("add_scalar".to_string(), ObjectMethodInfo {
            parameters: vec![SymbolType::Object("Share".to_string()), SymbolType::Int64],
            return_type: SymbolType::Object("Share".to_string()),
            qualified_name: "Share.add_scalar".to_string(),
        });

        // Share.mul_scalar(share, scalar) -> Object (local operation)
        share_methods.insert("mul_scalar".to_string(), ObjectMethodInfo {
            parameters: vec![SymbolType::Object("Share".to_string()), SymbolType::Int64],
            return_type: SymbolType::Object("Share".to_string()),
            qualified_name: "Share.mul_scalar".to_string(),
        });

        // Share.mul(share1, share2) -> Object (network operation)
        share_methods.insert("mul".to_string(), ObjectMethodInfo {
            parameters: vec![
                SymbolType::Object("Share".to_string()),
                SymbolType::Object("Share".to_string()),
            ],
            return_type: SymbolType::Object("Share".to_string()),
            qualified_name: "Share.mul".to_string(),
        });

        // Share.open(share) -> int64/float (network operation)
        share_methods.insert("open".to_string(), ObjectMethodInfo {
            parameters: vec![SymbolType::Object("Share".to_string())],
            return_type: SymbolType::Int64, // Can also return Float depending on share type
            qualified_name: "Share.open".to_string(),
        });

        // Share.send_to_client(share, client_id) -> bool
        share_methods.insert("send_to_client".to_string(), ObjectMethodInfo {
            parameters: vec![SymbolType::Object("Share".to_string()), SymbolType::Int64],
            return_type: SymbolType::Bool,
            qualified_name: "Share.send_to_client".to_string(),
        });

        // Share.interpolate_local(shares_array) -> int64/float
        share_methods.insert("interpolate_local".to_string(), ObjectMethodInfo {
            parameters: vec![SymbolType::List(Box::new(SymbolType::Object("Share".to_string())))],
            return_type: SymbolType::Int64,
            qualified_name: "Share.interpolate_local".to_string(),
        });

        // Share.get_type(share) -> string
        share_methods.insert("get_type".to_string(), ObjectMethodInfo {
            parameters: vec![SymbolType::Object("Share".to_string())],
            return_type: SymbolType::String,
            qualified_name: "Share.get_type".to_string(),
        });

        // Share.get_party_id(share) -> int64
        share_methods.insert("get_party_id".to_string(), ObjectMethodInfo {
            parameters: vec![SymbolType::Object("Share".to_string())],
            return_type: SymbolType::Int64,
            qualified_name: "Share.get_party_id".to_string(),
        });

        // Share.batch_open(shares_array) -> List[int64/float]
        share_methods.insert("batch_open".to_string(), ObjectMethodInfo {
            parameters: vec![SymbolType::List(Box::new(SymbolType::Object("Share".to_string())))],
            return_type: SymbolType::List(Box::new(SymbolType::Unknown)), // Can be int64 or float
            qualified_name: "Share.batch_open".to_string(),
        });

        self.builtin_objects.insert("Share".to_string(), BuiltinObjectInfo {
            name: "Share".to_string(),
            methods: share_methods,
        });

        let share_info = SymbolInfo {
            name: "Share".to_string(),
            kind: SymbolKind::BuiltinObject { object_type_name: "Share".to_string() },
            symbol_type: SymbolType::Object("Share".to_string()),
            is_secret: false,
            defined_at: SourceLocation::default(),
        };
        if let Err(e) = global_scope.declare(share_info) {
            self.errors.push((e, SourceLocation::default()));
        }

        // =====================================================================
        // Mpc - MPC engine info (matches VM mpc_builtins.rs)
        // =====================================================================
        let mut mpc_methods = HashMap::new();

        // Mpc.party_id() -> int64
        mpc_methods.insert("party_id".to_string(), ObjectMethodInfo {
            parameters: vec![],
            return_type: SymbolType::Int64,
            qualified_name: "Mpc.party_id".to_string(),
        });

        // Mpc.n_parties() -> int64
        mpc_methods.insert("n_parties".to_string(), ObjectMethodInfo {
            parameters: vec![],
            return_type: SymbolType::Int64,
            qualified_name: "Mpc.n_parties".to_string(),
        });

        // Mpc.threshold() -> int64
        mpc_methods.insert("threshold".to_string(), ObjectMethodInfo {
            parameters: vec![],
            return_type: SymbolType::Int64,
            qualified_name: "Mpc.threshold".to_string(),
        });

        // Mpc.is_ready() -> bool
        mpc_methods.insert("is_ready".to_string(), ObjectMethodInfo {
            parameters: vec![],
            return_type: SymbolType::Bool,
            qualified_name: "Mpc.is_ready".to_string(),
        });

        // Mpc.instance_id() -> int64
        mpc_methods.insert("instance_id".to_string(), ObjectMethodInfo {
            parameters: vec![],
            return_type: SymbolType::Int64,
            qualified_name: "Mpc.instance_id".to_string(),
        });

        self.builtin_objects.insert("Mpc".to_string(), BuiltinObjectInfo {
            name: "Mpc".to_string(),
            methods: mpc_methods,
        });

        let mpc_info = SymbolInfo {
            name: "Mpc".to_string(),
            kind: SymbolKind::BuiltinObject { object_type_name: "Mpc".to_string() },
            symbol_type: SymbolType::Object("Mpc".to_string()),
            is_secret: false,
            defined_at: SourceLocation::default(),
        };
        if let Err(e) = global_scope.declare(mpc_info) {
            self.errors.push((e, SourceLocation::default()));
        }

        // =====================================================================
        // Rbc - Reliable Broadcast protocol (matches VM mpc_builtins.rs)
        // =====================================================================
        let mut rbc_methods = HashMap::new();

        // Rbc.broadcast(message: string) -> int64 (session_id)
        rbc_methods.insert("broadcast".to_string(), ObjectMethodInfo {
            parameters: vec![SymbolType::String],
            return_type: SymbolType::Int64,
            qualified_name: "Rbc.broadcast".to_string(),
        });

        // Rbc.receive(from_party: int64, timeout_ms: int64) -> string
        rbc_methods.insert("receive".to_string(), ObjectMethodInfo {
            parameters: vec![SymbolType::Int64, SymbolType::Int64],
            return_type: SymbolType::String,
            qualified_name: "Rbc.receive".to_string(),
        });

        // Rbc.receive_any(timeout_ms: int64) -> Object (with party_id and message fields)
        rbc_methods.insert("receive_any".to_string(), ObjectMethodInfo {
            parameters: vec![SymbolType::Int64],
            return_type: SymbolType::Object("RbcResult".to_string()),
            qualified_name: "Rbc.receive_any".to_string(),
        });

        self.builtin_objects.insert("Rbc".to_string(), BuiltinObjectInfo {
            name: "Rbc".to_string(),
            methods: rbc_methods,
        });

        let rbc_info = SymbolInfo {
            name: "Rbc".to_string(),
            kind: SymbolKind::BuiltinObject { object_type_name: "Rbc".to_string() },
            symbol_type: SymbolType::Object("Rbc".to_string()),
            is_secret: false,
            defined_at: SourceLocation::default(),
        };
        if let Err(e) = global_scope.declare(rbc_info) {
            self.errors.push((e, SourceLocation::default()));
        }

        // =====================================================================
        // Aba - Asynchronous Binary Agreement protocol (matches VM mpc_builtins.rs)
        // =====================================================================
        let mut aba_methods = HashMap::new();

        // Aba.propose(value: bool) -> int64 (session_id)
        aba_methods.insert("propose".to_string(), ObjectMethodInfo {
            parameters: vec![SymbolType::Bool],
            return_type: SymbolType::Int64,
            qualified_name: "Aba.propose".to_string(),
        });

        // Aba.result(session_id: int64, timeout_ms: int64) -> bool
        aba_methods.insert("result".to_string(), ObjectMethodInfo {
            parameters: vec![SymbolType::Int64, SymbolType::Int64],
            return_type: SymbolType::Bool,
            qualified_name: "Aba.result".to_string(),
        });

        // Aba.propose_and_wait(value: bool, timeout_ms: int64) -> bool
        aba_methods.insert("propose_and_wait".to_string(), ObjectMethodInfo {
            parameters: vec![SymbolType::Bool, SymbolType::Int64],
            return_type: SymbolType::Bool,
            qualified_name: "Aba.propose_and_wait".to_string(),
        });

        self.builtin_objects.insert("Aba".to_string(), BuiltinObjectInfo {
            name: "Aba".to_string(),
            methods: aba_methods,
        });

        let aba_info = SymbolInfo {
            name: "Aba".to_string(),
            kind: SymbolKind::BuiltinObject { object_type_name: "Aba".to_string() },
            symbol_type: SymbolType::Object("Aba".to_string()),
            is_secret: false,
            defined_at: SourceLocation::default(),
        };
        if let Err(e) = global_scope.declare(aba_info) {
            self.errors.push((e, SourceLocation::default()));
        }

        // =====================================================================
        // ConsensusValue - Consensus value protocol (matches VM mpc_builtins.rs)
        // =====================================================================
        let mut consensus_value_methods = HashMap::new();

        // ConsensusValue.propose(value: int64) -> Object (session) (stubbed in VM)
        consensus_value_methods.insert("propose".to_string(), ObjectMethodInfo {
            parameters: vec![SymbolType::Int64],
            return_type: SymbolType::Object("ConsensusValueSession".to_string()),
            qualified_name: "ConsensusValue.propose".to_string(),
        });

        // ConsensusValue.get(session, timeout_ms: int64) -> int64 (stubbed in VM)
        consensus_value_methods.insert("get".to_string(), ObjectMethodInfo {
            parameters: vec![SymbolType::Object("ConsensusValueSession".to_string()), SymbolType::Int64],
            return_type: SymbolType::Int64,
            qualified_name: "ConsensusValue.get".to_string(),
        });

        self.builtin_objects.insert("ConsensusValue".to_string(), BuiltinObjectInfo {
            name: "ConsensusValue".to_string(),
            methods: consensus_value_methods,
        });

        let consensus_value_info = SymbolInfo {
            name: "ConsensusValue".to_string(),
            kind: SymbolKind::BuiltinObject { object_type_name: "ConsensusValue".to_string() },
            symbol_type: SymbolType::Object("ConsensusValue".to_string()),
            is_secret: false,
            defined_at: SourceLocation::default(),
        };
        if let Err(e) = global_scope.declare(consensus_value_info) {
            self.errors.push((e, SourceLocation::default()));
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

        // Array/Object manipulation builtins (from VM foreign functions)
        let create_array_info = SymbolInfo {
            name: "create_array".to_string(),
            kind: SymbolKind::BuiltinFunction {
                parameters: vec![], // Optional capacity parameter
                return_type: SymbolType::List(Box::new(SymbolType::Unknown)),
            },
            symbol_type: SymbolType::List(Box::new(SymbolType::Unknown)),
            is_secret: false,
            defined_at: SourceLocation::default(),
        };
        if let Err(e) = global_scope.declare(create_array_info) {
            self.errors.push((e, SourceLocation::default()));
        }

        let create_object_info = SymbolInfo {
            name: "create_object".to_string(),
            kind: SymbolKind::BuiltinFunction {
                parameters: vec![],
                return_type: SymbolType::Object("Object".to_string()),
            },
            symbol_type: SymbolType::Object("Object".to_string()),
            is_secret: false,
            defined_at: SourceLocation::default(),
        };
        if let Err(e) = global_scope.declare(create_object_info) {
            self.errors.push((e, SourceLocation::default()));
        }

        let get_field_info = SymbolInfo {
            name: "get_field".to_string(),
            kind: SymbolKind::BuiltinFunction {
                parameters: vec![SymbolType::Unknown, SymbolType::Unknown],
                return_type: SymbolType::Unknown,
            },
            symbol_type: SymbolType::Unknown,
            is_secret: false,
            defined_at: SourceLocation::default(),
        };
        if let Err(e) = global_scope.declare(get_field_info) {
            self.errors.push((e, SourceLocation::default()));
        }

        let set_field_info = SymbolInfo {
            name: "set_field".to_string(),
            kind: SymbolKind::BuiltinFunction {
                parameters: vec![SymbolType::Unknown, SymbolType::Unknown, SymbolType::Unknown],
                return_type: SymbolType::Void,
            },
            symbol_type: SymbolType::Void,
            is_secret: false,
            defined_at: SourceLocation::default(),
        };
        if let Err(e) = global_scope.declare(set_field_info) {
            self.errors.push((e, SourceLocation::default()));
        }

        let array_push_info = SymbolInfo {
            name: "array_push".to_string(),
            kind: SymbolKind::BuiltinFunction {
                parameters: vec![SymbolType::List(Box::new(SymbolType::Unknown)), SymbolType::Unknown],
                return_type: SymbolType::Int64, // Returns new length
            },
            symbol_type: SymbolType::Int64,
            is_secret: false,
            defined_at: SourceLocation::default(),
        };
        if let Err(e) = global_scope.declare(array_push_info) {
            self.errors.push((e, SourceLocation::default()));
        }

        // Add 'append' as Pythonic alias for array_push (enables arr.append(value) via UFCS)
        let append_info = SymbolInfo {
            name: "append".to_string(),
            kind: SymbolKind::BuiltinFunction {
                parameters: vec![SymbolType::List(Box::new(SymbolType::Unknown)), SymbolType::Unknown],
                return_type: SymbolType::Int64, // Returns new length
            },
            symbol_type: SymbolType::Int64,
            is_secret: false,
            defined_at: SourceLocation::default(),
        };
        if let Err(e) = global_scope.declare(append_info) {
            self.errors.push((e, SourceLocation::default()));
        }

        // Add 'push' as another alias for array_push (enables arr.push(value) via UFCS)
        let push_info = SymbolInfo {
            name: "push".to_string(),
            kind: SymbolKind::BuiltinFunction {
                parameters: vec![SymbolType::List(Box::new(SymbolType::Unknown)), SymbolType::Unknown],
                return_type: SymbolType::Int64, // Returns new length
            },
            symbol_type: SymbolType::Int64,
            is_secret: false,
            defined_at: SourceLocation::default(),
        };
        if let Err(e) = global_scope.declare(push_info) {
            self.errors.push((e, SourceLocation::default()));
        }

        let array_length_info = SymbolInfo {
            name: "array_length".to_string(),
            kind: SymbolKind::BuiltinFunction {
                parameters: vec![SymbolType::List(Box::new(SymbolType::Unknown))],
                return_type: SymbolType::Int64,
            },
            symbol_type: SymbolType::Int64,
            is_secret: false,
            defined_at: SourceLocation::default(),
        };
        if let Err(e) = global_scope.declare(array_length_info) {
            self.errors.push((e, SourceLocation::default()));
        }

        // Add 'length' as Pythonic alias for array_length (enables arr.length() via UFCS)
        let length_info = SymbolInfo {
            name: "length".to_string(),
            kind: SymbolKind::BuiltinFunction {
                parameters: vec![SymbolType::List(Box::new(SymbolType::Unknown))],
                return_type: SymbolType::Int64,
            },
            symbol_type: SymbolType::Int64,
            is_secret: false,
            defined_at: SourceLocation::default(),
        };
        if let Err(e) = global_scope.declare(length_info) {
            self.errors.push((e, SourceLocation::default()));
        }

        // Add 'len' as another alias for array_length (enables arr.len() or len(arr) via UFCS)
        let len_info = SymbolInfo {
            name: "len".to_string(),
            kind: SymbolKind::BuiltinFunction {
                parameters: vec![SymbolType::List(Box::new(SymbolType::Unknown))],
                return_type: SymbolType::Int64,
            },
            symbol_type: SymbolType::Int64,
            is_secret: false,
            defined_at: SourceLocation::default(),
        };
        if let Err(e) = global_scope.declare(len_info) {
            self.errors.push((e, SourceLocation::default()));
        }

        // Note: Method-to-function suggestions are kept for methods that don't have
        // direct function aliases (like pop, get, set) or have different semantics
        self.method_suggestions.insert("pop".to_string(), "array_pop(arr)".to_string());
        self.method_suggestions.insert("get".to_string(), "arr[index]".to_string());
        self.method_suggestions.insert("set".to_string(), "arr[index] = value".to_string());
        self.method_suggestions.insert("reveal".to_string(), "assign to a clear (non-secret) variable to implicitly reveal".to_string());
        self.method_suggestions.insert("open".to_string(), "Share.open(value) or assign to clear variable".to_string());
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

    /// Returns all visible symbol names from current scope up the chain.
    /// Handles shadowing (inner scope symbols take precedence over outer).
    pub fn get_visible_symbol_names(&self) -> Vec<String> {
        let mut symbols = Vec::new();
        let mut seen = std::collections::HashSet::new();
        let mut scope_id = Some(self.current_scope_id);

        while let Some(id) = scope_id {
            let scope = &self.scopes[id];
            for (name, _) in &scope.symbols {
                if !seen.contains(name) {
                    seen.insert(name.clone());
                    symbols.push(name.clone());
                }
            }
            scope_id = scope.parent_scope_id;
        }
        symbols
    }

    /// Returns all callable symbol names (functions + builtins + object methods).
    pub fn get_callable_names(&self) -> Vec<String> {
        let mut names: Vec<String> = self.get_visible_symbol_names()
            .into_iter()
            .filter(|name| {
                self.lookup_symbol(name)
                    .map(|info| matches!(info.kind,
                        SymbolKind::Function { .. } | SymbolKind::BuiltinFunction { .. }))
                    .unwrap_or(false)
            })
            .collect();

        // Add builtin object methods as "Object.method"
        for (obj_name, obj_info) in &self.builtin_objects {
            for method_name in obj_info.methods.keys() {
                names.push(format!("{}.{}", obj_name, method_name));
            }
        }
        names
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::errors::SourceLocation;

    fn make_loc() -> SourceLocation {
        SourceLocation::default()
    }

    fn make_variable(name: &str, symbol_type: SymbolType) -> SymbolInfo {
        SymbolInfo {
            name: name.to_string(),
            kind: SymbolKind::Variable { is_mutable: false },
            symbol_type,
            is_secret: false,
            defined_at: make_loc(),
        }
    }

    fn make_function(name: &str, params: Vec<SymbolType>, return_type: SymbolType) -> SymbolInfo {
        SymbolInfo {
            name: name.to_string(),
            kind: SymbolKind::Function {
                parameters: params,
                return_type,
            },
            symbol_type: SymbolType::Void,
            is_secret: false,
            defined_at: make_loc(),
        }
    }

    // ===========================================
    // Tests for get_visible_symbol_names
    // ===========================================

    #[test]
    fn test_get_visible_symbols_empty_scope() {
        let table = SymbolTable::new();
        // New table has builtins but no user symbols at global scope
        let symbols = table.get_visible_symbol_names();
        // Should include builtin functions like "print", "create_array", etc.
        assert!(symbols.contains(&"print".to_string()));
        assert!(symbols.contains(&"create_array".to_string()));
    }

    #[test]
    fn test_get_visible_symbols_single_scope() {
        let mut table = SymbolTable::new();
        table.declare_symbol(make_variable("counter", SymbolType::Int64));
        table.declare_symbol(make_variable("total", SymbolType::Int64));

        let symbols = table.get_visible_symbol_names();
        assert!(symbols.contains(&"counter".to_string()));
        assert!(symbols.contains(&"total".to_string()));
    }

    #[test]
    fn test_get_visible_symbols_nested_scopes() {
        let mut table = SymbolTable::new();

        // Global scope
        table.declare_symbol(make_variable("global_var", SymbolType::Int64));

        // Enter function scope
        table.enter_scope();
        table.declare_symbol(make_variable("local_var", SymbolType::Int64));

        let symbols = table.get_visible_symbol_names();

        // Should see both global and local
        assert!(symbols.contains(&"global_var".to_string()));
        assert!(symbols.contains(&"local_var".to_string()));
    }

    #[test]
    fn test_get_visible_symbols_shadowing() {
        let mut table = SymbolTable::new();

        // Global scope - declare 'x'
        table.declare_symbol(make_variable("x", SymbolType::Int64));
        table.declare_symbol(make_variable("y", SymbolType::Int64));

        // Enter inner scope - shadow 'x'
        table.enter_scope();
        table.declare_symbol(make_variable("x", SymbolType::String)); // shadows outer x
        table.declare_symbol(make_variable("z", SymbolType::Int64));

        let symbols = table.get_visible_symbol_names();

        // Should see x, y, z (x only once due to shadowing)
        let x_count = symbols.iter().filter(|s| *s == "x").count();
        assert_eq!(x_count, 1, "Shadowed variable should appear only once");
        assert!(symbols.contains(&"y".to_string()));
        assert!(symbols.contains(&"z".to_string()));
    }

    #[test]
    fn test_get_visible_symbols_after_exit_scope() {
        let mut table = SymbolTable::new();

        table.declare_symbol(make_variable("global_var", SymbolType::Int64));

        table.enter_scope();
        table.declare_symbol(make_variable("local_var", SymbolType::Int64));
        table.exit_scope();

        let symbols = table.get_visible_symbol_names();

        // After exiting scope, local_var should not be visible
        assert!(symbols.contains(&"global_var".to_string()));
        assert!(!symbols.contains(&"local_var".to_string()));
    }

    // ===========================================
    // Tests for get_callable_names
    // ===========================================

    #[test]
    fn test_get_callable_names_includes_builtins() {
        let table = SymbolTable::new();
        let callables = table.get_callable_names();

        // Should include builtin functions
        assert!(callables.contains(&"print".to_string()));
        assert!(callables.contains(&"create_array".to_string()));
        assert!(callables.contains(&"array_push".to_string()));
        assert!(callables.contains(&"array_length".to_string()));
    }

    #[test]
    fn test_get_callable_names_includes_user_functions() {
        let mut table = SymbolTable::new();
        table.declare_symbol(make_function(
            "calculate",
            vec![SymbolType::Int64],
            SymbolType::Int64,
        ));
        table.declare_symbol(make_function(
            "process",
            vec![SymbolType::String],
            SymbolType::Void,
        ));

        let callables = table.get_callable_names();

        assert!(callables.contains(&"calculate".to_string()));
        assert!(callables.contains(&"process".to_string()));
    }

    #[test]
    fn test_get_callable_names_excludes_variables() {
        let mut table = SymbolTable::new();
        table.declare_symbol(make_variable("my_var", SymbolType::Int64));
        table.declare_symbol(make_function("my_func", vec![], SymbolType::Void));

        let callables = table.get_callable_names();

        assert!(!callables.contains(&"my_var".to_string()));
        assert!(callables.contains(&"my_func".to_string()));
    }

    #[test]
    fn test_get_callable_names_includes_builtin_object_methods() {
        let table = SymbolTable::new();
        let callables = table.get_callable_names();

        // Should include builtin object methods as "Object.method"
        assert!(callables.contains(&"Share.open".to_string()));
        assert!(callables.contains(&"Share.mul".to_string()));
        assert!(callables.contains(&"ClientStore.take_share".to_string()));
        assert!(callables.contains(&"Mpc.party_id".to_string()));
    }

    #[test]
    fn test_get_callable_names_nested_scope_functions() {
        let mut table = SymbolTable::new();

        // Global function
        table.declare_symbol(make_function("global_func", vec![], SymbolType::Void));

        // Enter scope and declare local function
        table.enter_scope();
        table.declare_symbol(make_function("local_func", vec![], SymbolType::Void));

        let callables = table.get_callable_names();

        // Should see both
        assert!(callables.contains(&"global_func".to_string()));
        assert!(callables.contains(&"local_func".to_string()));
    }

    // ===========================================
    // Tests for builtin objects
    // ===========================================

    #[test]
    fn test_builtin_objects_registered() {
        let table = SymbolTable::new();

        // All builtin objects should be registered
        assert!(table.builtin_objects.contains_key("ClientStore"));
        assert!(table.builtin_objects.contains_key("Share"));
        assert!(table.builtin_objects.contains_key("Mpc"));
        assert!(table.builtin_objects.contains_key("Rbc"));
        assert!(table.builtin_objects.contains_key("Aba"));
        assert!(table.builtin_objects.contains_key("ConsensusValue"));
    }

    #[test]
    fn test_builtin_objects_as_symbols() {
        let table = SymbolTable::new();

        // Builtin objects should be declared as symbols in global scope
        let client_store = table.lookup_symbol("ClientStore");
        assert!(client_store.is_some());
        let info = client_store.unwrap();
        assert!(matches!(info.kind, SymbolKind::BuiltinObject { .. }));
        assert_eq!(info.symbol_type, SymbolType::Object("ClientStore".to_string()));

        let share = table.lookup_symbol("Share");
        assert!(share.is_some());
        assert!(matches!(share.unwrap().kind, SymbolKind::BuiltinObject { .. }));

        let mpc = table.lookup_symbol("Mpc");
        assert!(mpc.is_some());
        assert!(matches!(mpc.unwrap().kind, SymbolKind::BuiltinObject { .. }));
    }

    #[test]
    fn test_lookup_builtin_object() {
        let table = SymbolTable::new();

        let client_store = table.lookup_builtin_object("ClientStore");
        assert!(client_store.is_some());
        let obj_info = client_store.unwrap();
        assert!(!obj_info.methods.is_empty());

        // Non-existent object should return None
        assert!(table.lookup_builtin_object("NonExistent").is_none());
    }

    // ===========================================
    // Tests for builtin object methods
    // ===========================================

    #[test]
    fn test_lookup_builtin_method_client_store() {
        let table = SymbolTable::new();

        // Test take_share method
        let take_share = table.lookup_builtin_method("ClientStore", "take_share");
        assert!(take_share.is_some());
        let method = take_share.unwrap();
        assert_eq!(method.parameters.len(), 2);
        assert_eq!(method.parameters[0], SymbolType::Int64);
        assert_eq!(method.parameters[1], SymbolType::Int64);
        assert_eq!(method.return_type, SymbolType::Secret(Box::new(SymbolType::Int64)));
        assert_eq!(method.qualified_name, "ClientStore.take_share");

        // Test take_share_fixed method
        let take_share_fixed = table.lookup_builtin_method("ClientStore", "take_share_fixed");
        assert!(take_share_fixed.is_some());
        let method = take_share_fixed.unwrap();
        assert_eq!(method.return_type, SymbolType::Secret(Box::new(SymbolType::Float)));

        // Test get_number_clients method
        let get_number_clients = table.lookup_builtin_method("ClientStore", "get_number_clients");
        assert!(get_number_clients.is_some());
        let method = get_number_clients.unwrap();
        assert!(method.parameters.is_empty());
        assert_eq!(method.return_type, SymbolType::Int64);
    }

    #[test]
    fn test_lookup_builtin_method_share() {
        let table = SymbolTable::new();

        // Test from_clear method
        let from_clear = table.lookup_builtin_method("Share", "from_clear");
        assert!(from_clear.is_some());
        let method = from_clear.unwrap();
        assert_eq!(method.parameters.len(), 1);
        assert_eq!(method.return_type, SymbolType::Object("Share".to_string()));

        // Test add method (two Share arguments)
        let add = table.lookup_builtin_method("Share", "add");
        assert!(add.is_some());
        let method = add.unwrap();
        assert_eq!(method.parameters.len(), 2);
        assert_eq!(method.parameters[0], SymbolType::Object("Share".to_string()));
        assert_eq!(method.parameters[1], SymbolType::Object("Share".to_string()));
        assert_eq!(method.return_type, SymbolType::Object("Share".to_string()));

        // Test mul method (network operation)
        let mul = table.lookup_builtin_method("Share", "mul");
        assert!(mul.is_some());
        assert_eq!(mul.unwrap().qualified_name, "Share.mul");

        // Test open method
        let open = table.lookup_builtin_method("Share", "open");
        assert!(open.is_some());
        let method = open.unwrap();
        assert_eq!(method.parameters.len(), 1);
        assert_eq!(method.return_type, SymbolType::Int64);
    }

    #[test]
    fn test_lookup_builtin_method_mpc() {
        let table = SymbolTable::new();

        // Test party_id method
        let party_id = table.lookup_builtin_method("Mpc", "party_id");
        assert!(party_id.is_some());
        let method = party_id.unwrap();
        assert!(method.parameters.is_empty());
        assert_eq!(method.return_type, SymbolType::Int64);

        // Test n_parties method
        let n_parties = table.lookup_builtin_method("Mpc", "n_parties");
        assert!(n_parties.is_some());

        // Test threshold method
        let threshold = table.lookup_builtin_method("Mpc", "threshold");
        assert!(threshold.is_some());

        // Test is_ready method
        let is_ready = table.lookup_builtin_method("Mpc", "is_ready");
        assert!(is_ready.is_some());
        assert_eq!(is_ready.unwrap().return_type, SymbolType::Bool);
    }

    #[test]
    fn test_lookup_builtin_method_rbc() {
        let table = SymbolTable::new();

        // Test broadcast method
        let broadcast = table.lookup_builtin_method("Rbc", "broadcast");
        assert!(broadcast.is_some());
        let method = broadcast.unwrap();
        assert_eq!(method.parameters.len(), 1);
        assert_eq!(method.parameters[0], SymbolType::String);
        assert_eq!(method.return_type, SymbolType::Int64);

        // Test receive method
        let receive = table.lookup_builtin_method("Rbc", "receive");
        assert!(receive.is_some());
        let method = receive.unwrap();
        assert_eq!(method.parameters.len(), 2);
        assert_eq!(method.return_type, SymbolType::String);
    }

    #[test]
    fn test_lookup_builtin_method_aba() {
        let table = SymbolTable::new();

        // Test propose method
        let propose = table.lookup_builtin_method("Aba", "propose");
        assert!(propose.is_some());
        let method = propose.unwrap();
        assert_eq!(method.parameters.len(), 1);
        assert_eq!(method.parameters[0], SymbolType::Bool);
        assert_eq!(method.return_type, SymbolType::Int64);

        // Test result method
        let result = table.lookup_builtin_method("Aba", "result");
        assert!(result.is_some());
        let method = result.unwrap();
        assert_eq!(method.return_type, SymbolType::Bool);

        // Test propose_and_wait method
        let propose_and_wait = table.lookup_builtin_method("Aba", "propose_and_wait");
        assert!(propose_and_wait.is_some());
    }

    #[test]
    fn test_lookup_builtin_method_consensus_value() {
        let table = SymbolTable::new();

        // Test propose method
        let propose = table.lookup_builtin_method("ConsensusValue", "propose");
        assert!(propose.is_some());
        let method = propose.unwrap();
        assert_eq!(method.parameters.len(), 1);
        assert_eq!(method.return_type, SymbolType::Object("ConsensusValueSession".to_string()));

        // Test get method
        let get = table.lookup_builtin_method("ConsensusValue", "get");
        assert!(get.is_some());
        let method = get.unwrap();
        assert_eq!(method.parameters.len(), 2);
        assert_eq!(method.return_type, SymbolType::Int64);
    }

    #[test]
    fn test_lookup_nonexistent_method() {
        let table = SymbolTable::new();

        // Non-existent method on existing object
        assert!(table.lookup_builtin_method("ClientStore", "nonexistent").is_none());

        // Method on non-existent object
        assert!(table.lookup_builtin_method("NonExistent", "method").is_none());
    }

    // ===========================================
    // Tests for SymbolType::Object
    // ===========================================

    #[test]
    fn test_symbol_type_object_equality() {
        let obj1 = SymbolType::Object("Share".to_string());
        let obj2 = SymbolType::Object("Share".to_string());
        let obj3 = SymbolType::Object("ClientStore".to_string());

        assert_eq!(obj1, obj2);
        assert_ne!(obj1, obj3);
    }

    #[test]
    fn test_symbol_type_object_in_secret() {
        let secret_share = SymbolType::Secret(Box::new(SymbolType::Object("Share".to_string())));

        assert!(secret_share.is_secret());
        assert_eq!(
            *secret_share.underlying_type(),
            SymbolType::Object("Share".to_string())
        );
    }

    #[test]
    fn test_symbol_type_object_not_integer() {
        let obj = SymbolType::Object("Share".to_string());
        assert!(!obj.is_integer());
        assert!(!obj.is_signed());
        assert!(obj.bit_width().is_none());
    }

    // ===========================================
    // Tests for SymbolKind::BuiltinObject
    // ===========================================

    #[test]
    fn test_symbol_kind_builtin_object() {
        let table = SymbolTable::new();

        let share_symbol = table.lookup_symbol("Share").unwrap();
        match &share_symbol.kind {
            SymbolKind::BuiltinObject { object_type_name } => {
                assert_eq!(object_type_name, "Share");
            }
            _ => panic!("Expected BuiltinObject kind"),
        }
    }

    #[test]
    fn test_builtin_object_not_callable_directly() {
        let table = SymbolTable::new();
        let callables = table.get_callable_names();

        // Builtin objects themselves should not be in callable names
        // (only their methods should be)
        assert!(!callables.contains(&"ClientStore".to_string()));
        assert!(!callables.contains(&"Share".to_string()));
        assert!(!callables.contains(&"Mpc".to_string()));
    }

    // ===========================================
    // Tests for object method count and listing
    // ===========================================

    #[test]
    fn test_share_has_all_methods() {
        let table = SymbolTable::new();
        let share = table.lookup_builtin_object("Share").unwrap();

        // Share should have these methods
        let expected_methods = [
            "from_clear", "from_clear_int", "from_clear_fixed",
            "add", "sub", "neg", "add_scalar", "mul_scalar", "mul",
            "open", "send_to_client", "interpolate_local",
            "get_type", "get_party_id", "batch_open"
        ];

        for method_name in expected_methods {
            assert!(
                share.methods.contains_key(method_name),
                "Share should have method '{}'", method_name
            );
        }
    }

    #[test]
    fn test_client_store_has_all_methods() {
        let table = SymbolTable::new();
        let client_store = table.lookup_builtin_object("ClientStore").unwrap();

        let expected_methods = ["take_share", "take_share_fixed", "get_number_clients"];

        for method_name in expected_methods {
            assert!(
                client_store.methods.contains_key(method_name),
                "ClientStore should have method '{}'", method_name
            );
        }
        assert_eq!(client_store.methods.len(), 3);
    }

    #[test]
    fn test_mpc_has_all_methods() {
        let table = SymbolTable::new();
        let mpc = table.lookup_builtin_object("Mpc").unwrap();

        let expected_methods = ["party_id", "n_parties", "threshold", "is_ready", "instance_id"];

        for method_name in expected_methods {
            assert!(
                mpc.methods.contains_key(method_name),
                "Mpc should have method '{}'", method_name
            );
        }
        assert_eq!(mpc.methods.len(), 5);
    }

    // ===========================================
    // Tests for method suggestions related to objects
    // ===========================================

    #[test]
    fn test_method_suggestion_open() {
        let table = SymbolTable::new();

        // "open" should suggest Share.open
        let suggestion = table.get_method_suggestion("open");
        assert!(suggestion.is_some());
        assert!(suggestion.unwrap().contains("Share.open"));
    }

    #[test]
    fn test_method_suggestion_reveal() {
        let table = SymbolTable::new();

        // "reveal" should suggest using clear variables
        let suggestion = table.get_method_suggestion("reveal");
        assert!(suggestion.is_some());
        assert!(suggestion.unwrap().contains("clear"));
    }

    // ===========================================
    // Tests for object variables
    // ===========================================

    #[test]
    fn test_declare_object_typed_variable() {
        let mut table = SymbolTable::new();

        let share_var = SymbolInfo {
            name: "my_share".to_string(),
            kind: SymbolKind::Variable { is_mutable: false },
            symbol_type: SymbolType::Object("Share".to_string()),
            is_secret: false,
            defined_at: make_loc(),
        };
        table.declare_symbol(share_var);

        let looked_up = table.lookup_symbol("my_share");
        assert!(looked_up.is_some());
        assert_eq!(looked_up.unwrap().symbol_type, SymbolType::Object("Share".to_string()));
    }

    #[test]
    fn test_declare_secret_object_variable() {
        let mut table = SymbolTable::new();

        let secret_share_var = SymbolInfo {
            name: "secret_share".to_string(),
            kind: SymbolKind::Variable { is_mutable: true },
            symbol_type: SymbolType::Secret(Box::new(SymbolType::Object("Share".to_string()))),
            is_secret: true,
            defined_at: make_loc(),
        };
        table.declare_symbol(secret_share_var);

        let looked_up = table.lookup_symbol("secret_share").unwrap();
        assert!(looked_up.is_secret);
        assert!(looked_up.symbol_type.is_secret());
    }

    // ===========================================
    // Tests for List of objects
    // ===========================================

    #[test]
    fn test_list_of_objects_type() {
        let list_of_shares = SymbolType::List(Box::new(SymbolType::Object("Share".to_string())));

        // Check interpolate_local accepts list of shares
        let table = SymbolTable::new();
        let interpolate = table.lookup_builtin_method("Share", "interpolate_local").unwrap();

        assert_eq!(interpolate.parameters.len(), 1);
        assert_eq!(
            interpolate.parameters[0],
            SymbolType::List(Box::new(SymbolType::Object("Share".to_string())))
        );
    }

    #[test]
    fn test_batch_open_returns_list() {
        let table = SymbolTable::new();
        let batch_open = table.lookup_builtin_method("Share", "batch_open").unwrap();

        // batch_open should return a list
        match &batch_open.return_type {
            SymbolType::List(_) => (),
            _ => panic!("batch_open should return a List type"),
        }
    }
}
