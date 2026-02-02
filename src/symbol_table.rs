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
    List(Box<SymbolType>),                    // list[T]
    Dict(Box<SymbolType>, Box<SymbolType>),   // dict[K, V]
    Object(String),                            // Named object type
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
    /// Registry of builtin object types (like ClientStore)
    pub builtin_objects: HashMap<String, BuiltinObjectInfo>,
}

impl SymbolTable {
    pub fn new() -> Self {
        let mut table = SymbolTable {
            scopes: Vec::new(),
            current_scope_id: 0,
            next_scope_id: 1, // 0 is global scope
            errors: Vec::new(),
            builtin_objects: HashMap::new(),
        };
        // Create the global scope (ID 0)
        table.scopes.push(Scope::new(0, None));
        table.add_builtins();
        table
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
        // Public input retrieval (non-secret)
        client_store_methods.insert("take_bytes".to_string(), ObjectMethodInfo {
            parameters: vec![SymbolType::Int64],
            return_type: SymbolType::String, // bytes represented as string until native bytes type
            qualified_name: "ClientStore.take_bytes".to_string(),
        });
        client_store_methods.insert("take_int".to_string(), ObjectMethodInfo {
            parameters: vec![SymbolType::Int64],
            return_type: SymbolType::Int64,
            qualified_name: "ClientStore.take_int".to_string(),
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

        // Share.batch_open(shares_array) -> list[int64/float]
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

        // Add more built-ins: len, assert, etc.

        // =====================================================================
        // VM Cryptographic Builtins - Ristretto Elliptic Curve Operations
        // =====================================================================

        // Ristretto_add(string, string) -> string
        let ristretto_add_info = SymbolInfo {
            name: "Ristretto_add".to_string(),
            kind: SymbolKind::BuiltinFunction {
                parameters: vec![SymbolType::String, SymbolType::String],
                return_type: SymbolType::String,
            },
            symbol_type: SymbolType::String,
            is_secret: false,
            defined_at: SourceLocation::default(),
        };
        if let Err(e) = global_scope.declare(ristretto_add_info) {
            self.errors.push((e, SourceLocation::default()));
        }

        // Ristretto_sub(string, string) -> string
        let ristretto_sub_info = SymbolInfo {
            name: "Ristretto_sub".to_string(),
            kind: SymbolKind::BuiltinFunction {
                parameters: vec![SymbolType::String, SymbolType::String],
                return_type: SymbolType::String,
            },
            symbol_type: SymbolType::String,
            is_secret: false,
            defined_at: SourceLocation::default(),
        };
        if let Err(e) = global_scope.declare(ristretto_sub_info) {
            self.errors.push((e, SourceLocation::default()));
        }

        // Ristretto_mul(string, string) -> string
        let ristretto_mul_info = SymbolInfo {
            name: "Ristretto_mul".to_string(),
            kind: SymbolKind::BuiltinFunction {
                parameters: vec![SymbolType::String, SymbolType::String],
                return_type: SymbolType::String,
            },
            symbol_type: SymbolType::String,
            is_secret: false,
            defined_at: SourceLocation::default(),
        };
        if let Err(e) = global_scope.declare(ristretto_mul_info) {
            self.errors.push((e, SourceLocation::default()));
        }

        // Ristretto_mul_int(string, int64) -> string
        let ristretto_mul_int_info = SymbolInfo {
            name: "Ristretto_mul_int".to_string(),
            kind: SymbolKind::BuiltinFunction {
                parameters: vec![SymbolType::String, SymbolType::Int64],
                return_type: SymbolType::String,
            },
            symbol_type: SymbolType::String,
            is_secret: false,
            defined_at: SourceLocation::default(),
        };
        if let Err(e) = global_scope.declare(ristretto_mul_int_info) {
            self.errors.push((e, SourceLocation::default()));
        }

        // Ristretto_identity() -> string
        let ristretto_identity_info = SymbolInfo {
            name: "Ristretto_identity".to_string(),
            kind: SymbolKind::BuiltinFunction {
                parameters: vec![],
                return_type: SymbolType::String,
            },
            symbol_type: SymbolType::String,
            is_secret: false,
            defined_at: SourceLocation::default(),
        };
        if let Err(e) = global_scope.declare(ristretto_identity_info) {
            self.errors.push((e, SourceLocation::default()));
        }

        // Ristretto_discrete_log(string, int64) -> int64
        let ristretto_discrete_log_info = SymbolInfo {
            name: "Ristretto_discrete_log".to_string(),
            kind: SymbolKind::BuiltinFunction {
                parameters: vec![SymbolType::String, SymbolType::Int64],
                return_type: SymbolType::Int64,
            },
            symbol_type: SymbolType::Int64,
            is_secret: false,
            defined_at: SourceLocation::default(),
        };
        if let Err(e) = global_scope.declare(ristretto_discrete_log_info) {
            self.errors.push((e, SourceLocation::default()));
        }

        // =====================================================================
        // VM Cryptographic Builtins - Scalar Operations
        // =====================================================================

        // Scalar_lagrange_simple(int64, int64) -> string
        let scalar_lagrange_simple_info = SymbolInfo {
            name: "Scalar_lagrange_simple".to_string(),
            kind: SymbolKind::BuiltinFunction {
                parameters: vec![SymbolType::Int64, SymbolType::Int64],
                return_type: SymbolType::String,
            },
            symbol_type: SymbolType::String,
            is_secret: false,
            defined_at: SourceLocation::default(),
        };
        if let Err(e) = global_scope.declare(scalar_lagrange_simple_info) {
            self.errors.push((e, SourceLocation::default()));
        }

        // =====================================================================
        // VM Utility Builtins - Byte/Binary Operations
        // =====================================================================

        // int_to_bytes(int64) -> string
        let int_to_bytes_info = SymbolInfo {
            name: "int_to_bytes".to_string(),
            kind: SymbolKind::BuiltinFunction {
                parameters: vec![SymbolType::Int64],
                return_type: SymbolType::String,
            },
            symbol_type: SymbolType::String,
            is_secret: false,
            defined_at: SourceLocation::default(),
        };
        if let Err(e) = global_scope.declare(int_to_bytes_info) {
            self.errors.push((e, SourceLocation::default()));
        }

        // bytes_to_int(string) -> int64
        let bytes_to_int_info = SymbolInfo {
            name: "bytes_to_int".to_string(),
            kind: SymbolKind::BuiltinFunction {
                parameters: vec![SymbolType::String],
                return_type: SymbolType::Int64,
            },
            symbol_type: SymbolType::Int64,
            is_secret: false,
            defined_at: SourceLocation::default(),
        };
        if let Err(e) = global_scope.declare(bytes_to_int_info) {
            self.errors.push((e, SourceLocation::default()));
        }

        // concat_bytes(string, string) -> string
        let concat_bytes_info = SymbolInfo {
            name: "concat_bytes".to_string(),
            kind: SymbolKind::BuiltinFunction {
                parameters: vec![SymbolType::String, SymbolType::String],
                return_type: SymbolType::String,
            },
            symbol_type: SymbolType::String,
            is_secret: false,
            defined_at: SourceLocation::default(),
        };
        if let Err(e) = global_scope.declare(concat_bytes_info) {
            self.errors.push((e, SourceLocation::default()));
        }

        // bytes_slice(string, int64, int64) -> string
        let bytes_slice_info = SymbolInfo {
            name: "bytes_slice".to_string(),
            kind: SymbolKind::BuiltinFunction {
                parameters: vec![SymbolType::String, SymbolType::Int64, SymbolType::Int64],
                return_type: SymbolType::String,
            },
            symbol_type: SymbolType::String,
            is_secret: false,
            defined_at: SourceLocation::default(),
        };
        if let Err(e) = global_scope.declare(bytes_slice_info) {
            self.errors.push((e, SourceLocation::default()));
        }

        // hash_sha256(string) -> string
        let hash_sha256_info = SymbolInfo {
            name: "hash_sha256".to_string(),
            kind: SymbolKind::BuiltinFunction {
                parameters: vec![SymbolType::String],
                return_type: SymbolType::String,
            },
            symbol_type: SymbolType::String,
            is_secret: false,
            defined_at: SourceLocation::default(),
        };
        if let Err(e) = global_scope.declare(hash_sha256_info) {
            self.errors.push((e, SourceLocation::default()));
        }
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
}
