use crate::bytecode::CompiledProgram;
use crate::codegen;
use crate::errors::{CompilerError, ErrorReporter};
use crate::lexer;
use crate::parser;
use crate::semantic;
use crate::ufcs;

/// Options to configure the compilation process.
#[derive(Debug, Clone, Default)]
pub struct CompilerOptions {
    /// Enable or disable optimization passes.
    pub optimize: bool,
    /// Set the optimization level (0-3).
    pub optimization_level: u8,
    /// Print intermediate representations (Tokens, AST) for debugging.
    pub print_ir: bool,
    // Add more options as needed: output_path, target_platform, etc.
}

/// Compiles the given source code string.
///
/// This function orchestrates the different phases of the compiler:
/// Lexing, Parsing, AST Transformations (like UFCS), Semantic Analysis, and Code Generation.
///
/// # Arguments
///
/// * `source` - The source code to compile.
/// * `filename` - The name of the source file (used for error reporting).
/// * `options` - Configuration for the compilation process.
///
/// # Returns
///
/// * `Ok(CompiledProgram)` - If compilation is successful.
/// * `Err(Vec<CompilerError>)` - If any errors occur during compilation.
pub fn compile(
    source: &str,
    filename: &str,
    options: &CompilerOptions,
) -> Result<CompiledProgram, Vec<CompilerError>> {
    let mut error_reporter = ErrorReporter::new();

    // 1. Lexing
    let tokens = match lexer::tokenize(source, filename) {
        Ok(t) => t,
        Err(e) => {
            error_reporter.add_error(e);
            // Cannot proceed without tokens
            return Err(error_reporter.get_all().into_iter().cloned().collect());
        }
    };
    if options.print_ir {
        println!("--- Tokens ---");
        println!("{:?}", tokens);
        println!("--------------");
    }

    // 2. Parsing
    let ast_root = match parser::parse(&tokens, filename) {
        Ok(ast) => ast,
        Err(e) => {
            error_reporter.add_error(e);
            // Stop if parsing fails fundamentally.
            // If we want resilience, parser needs to return partial AST + errors.
            return Err(error_reporter.get_all().into_iter().cloned().collect());
        }
    };
    if options.print_ir {
        println!("--- Initial AST ---");
        println!("{:#?}", ast_root);
        println!("-------------------");
    }

    // 3. UFCS Transformation (AST Pass)
    let transformed_ast = ufcs::transform_ufcs(ast_root);
    if options.print_ir {
        println!("--- Transformed AST (UFCS) ---");
        println!("{:#?}", transformed_ast);
        println!("------------------------------");
    }

    // 4. Semantic Analysis (Symbol Table, Type Checking)
    let analyzed_ast = match semantic::analyze(transformed_ast, &mut error_reporter, filename) {
        Ok(ast) => ast,
        Err(_) => {
            // Errors were already added to the reporter by the analyzer
            // Stop compilation if semantic errors occurred
            return Err(error_reporter.get_all().into_iter().cloned().collect());
        }
    };
    if options.print_ir {
        println!("--- Analyzed AST (Semantic Check) ---");
        println!("{:#?}", analyzed_ast);
        println!("-------------------------------------");
    }

    // 5. Code Generation
    let compiled_program = match codegen::generate_bytecode(&analyzed_ast) {
        Ok(program) => program,
        Err(e) => {
            error_reporter.add_error(e);
            // Stop if codegen fails
            return Err(error_reporter.get_all().into_iter().cloned().collect());
        }
    };

    if error_reporter.has_errors() {
        Err(error_reporter.get_all().into_iter().cloned().collect())
    } else {
        Ok(compiled_program)
    }
}
