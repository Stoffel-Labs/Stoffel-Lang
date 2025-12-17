//! Stoffel-Lang Compiler Library
//!
//! This library provides the core compilation functionality for the Stoffel programming language.
//! It can be used as a standalone compiler or integrated into other tools.

pub mod ast;
pub mod core_types;
pub mod bytecode;
pub mod codegen;
pub mod compiler;
pub mod lexer;
pub mod errors;
pub mod ffi;
pub mod parser;
pub mod symbol_table;
pub mod semantic;
pub mod suggestions;
pub mod ufcs;
pub mod register_allocator;
pub mod binary_converter;
pub mod optimizations;

// Re-export the main compiler functions and types for easy access
pub use compiler::{compile, CompilerOptions};
pub use errors::{CompilerError, ErrorReporter};
pub use bytecode::{CompiledProgram, Constant};
pub use binary_converter::{convert_to_binary, save_to_file};

/// Get the compiler version
pub fn version() -> &'static str {
    env!("CARGO_PKG_VERSION")
}