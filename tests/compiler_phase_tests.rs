//! Integration tests that run the full compiler phases
//!
//! These tests exercise the lexer, parser, UFCS transformer, and semantic analyzer
//! as a unit, testing real code snippets rather than manually constructed ASTs.

use stoffellang::compiler::{compile, CompilerOptions};
use stoffellang::lexer::tokenize;
use stoffellang::parser::parse;
use stoffellang::semantic::analyze;
use stoffellang::ufcs::transform_ufcs;
use stoffellang::errors::ErrorReporter;

// ===========================================
// Helper functions
// ===========================================

fn default_options() -> CompilerOptions {
    CompilerOptions {
        optimize: false,
        optimization_level: 0,
        print_ir: false,
    }
}

/// Runs lexer + parser and returns success/failure
fn parse_source(source: &str) -> Result<(), String> {
    let tokens = tokenize(source, "test.stfl").map_err(|e| e.message)?;
    parse(&tokens, "test.stfl").map_err(|e| e.message)?;
    Ok(())
}

/// Runs full semantic analysis pipeline and returns success/failure
fn analyze_source(source: &str) -> Result<(), Vec<String>> {
    let tokens = tokenize(source, "test.stfl").map_err(|e| vec![e.message])?;
    let ast = parse(&tokens, "test.stfl").map_err(|e| vec![e.message])?;
    let transformed = transform_ufcs(ast);
    let mut reporter = ErrorReporter::new();
    analyze(transformed, &mut reporter, "test.stfl")
        .map_err(|_| reporter.get_all().iter().map(|e| e.message.clone()).collect::<Vec<_>>())?;
    Ok(())
}

/// Runs full compilation and returns success/failure
fn compile_source(source: &str) -> Result<(), Vec<String>> {
    compile(source, "test.stfl", &default_options())
        .map(|_| ())
        .map_err(|errors| errors.iter().map(|e| e.message.clone()).collect())
}

/// Checks if compilation produces an error containing the given substring
fn expect_error_containing(source: &str, expected_substring: &str) -> bool {
    match compile(source, "test.stfl", &default_options()) {
        Ok(_) => false,
        Err(errors) => errors.iter().any(|e| e.message.contains(expected_substring)),
    }
}

// ===========================================
// Lexer Phase Tests
// ===========================================

#[test]
fn test_lexer_valid_identifiers() {
    let source = "var myVar = 42\nvar _private = 1\nvar camelCase = 2";
    assert!(parse_source(source).is_ok());
}

#[test]
fn test_lexer_valid_literals() {
    let source = r#"
var a = 42
var b = 3.14
var c = "hello"
var d = true
var e = false
"#;
    assert!(parse_source(source).is_ok());
}

#[test]
fn test_lexer_valid_operators() {
    let source = r#"
var a = 1 + 2
var b = 3 - 4
var c = 5 * 6
var d = 7 / 8
var e = 9 % 10
var f = a == b
var g = a != b
var h = a < b
var i = a > b
var j = a <= b
var k = a >= b
"#;
    assert!(parse_source(source).is_ok());
}

#[test]
fn test_lexer_hex_literals() {
    let source = "var x = 0xFF\nvar y = 0x1A2B";
    assert!(parse_source(source).is_ok());
}

#[test]
fn test_lexer_binary_literals() {
    let source = "var x = 0b1010\nvar y = 0b11110000";
    assert!(parse_source(source).is_ok());
}

// ===========================================
// Parser Phase Tests - Object Syntax
// ===========================================

#[test]
fn test_parser_field_access() {
    let source = "var x = obj.field";
    assert!(parse_source(source).is_ok());
}

#[test]
fn test_parser_method_call() {
    let source = "var x = obj.method(1, 2)";
    assert!(parse_source(source).is_ok());
}

#[test]
fn test_parser_chained_method_calls() {
    let source = "var x = a.first().second().third()";
    assert!(parse_source(source).is_ok());
}

#[test]
fn test_parser_builtin_object_calls() {
    let source = r#"
var share = ClientStore.take_share(0, 0)
var id = Mpc.party_id()
var n = Mpc.n_parties()
"#;
    assert!(parse_source(source).is_ok());
}

#[test]
fn test_parser_field_access_in_expressions() {
    let source = "var sum = a.x + b.y * c.z";
    assert!(parse_source(source).is_ok());
}

#[test]
fn test_parser_index_and_field_combined() {
    let source = r#"
var x = arr[0].field
var y = obj.array[1]
"#;
    assert!(parse_source(source).is_ok());
}

// ===========================================
// Parser Phase Tests - Functions
// ===========================================

#[test]
fn test_parser_function_definition() {
    let source = r#"
def add(a: int64, b: int64) -> int64:
  return a + b
"#;
    assert!(parse_source(source).is_ok());
}

#[test]
fn test_parser_function_no_return_type() {
    let source = r#"
def greet(name: string):
  print(name)
"#;
    assert!(parse_source(source).is_ok());
}

#[test]
fn test_parser_function_no_params() {
    let source = r#"
def get_value() -> int64:
  return 42
"#;
    assert!(parse_source(source).is_ok());
}

#[test]
fn test_parser_secret_function() {
    let source = r#"
secret def compute(x: secret int64) -> secret int64:
  return x * 2
"#;
    assert!(parse_source(source).is_ok());
}

// ===========================================
// Parser Phase Tests - Control Flow
// ===========================================

#[test]
fn test_parser_if_statement() {
    let source = r#"
if x > 0:
  print("positive")
"#;
    assert!(parse_source(source).is_ok());
}

#[test]
fn test_parser_if_else() {
    let source = r#"
if x > 0:
  print("positive")
else:
  print("non-positive")
"#;
    assert!(parse_source(source).is_ok());
}

#[test]
fn test_parser_if_elif_else() {
    let source = r#"
if x > 0:
  print("positive")
elif x < 0:
  print("negative")
else:
  print("zero")
"#;
    assert!(parse_source(source).is_ok());
}

#[test]
fn test_parser_while_loop() {
    let source = r#"
while x > 0:
  x = x - 1
"#;
    assert!(parse_source(source).is_ok());
}

#[test]
fn test_parser_for_loop() {
    // For loop syntax requires a range with ".." operator (no spaces around it)
    let source = r#"
for i in 0..10:
  print(i)
"#;
    assert!(parse_source(source).is_ok());
}

#[test]
fn test_parser_for_loop_list_iteration() {
    // For loop can iterate over a list variable
    let source = r#"
var items = [1, 2, 3]
for item in items:
  print(item)
"#;
    assert!(parse_source(source).is_ok());
}

#[test]
fn test_parser_for_loop_list_literal() {
    // For loop can iterate directly over a list literal
    let source = r#"
for x in [10, 20, 30]:
  print(x)
"#;
    assert!(parse_source(source).is_ok());
}

// ===========================================
// Parser Phase Tests - Declarations
// ===========================================

#[test]
fn test_parser_variable_declaration() {
    let source = "var x = 42";
    assert!(parse_source(source).is_ok());
}

#[test]
fn test_parser_typed_variable() {
    let source = "var x: int64 = 42";
    assert!(parse_source(source).is_ok());
}

#[test]
fn test_parser_secret_variable() {
    let source = "secret var x = 42";
    assert!(parse_source(source).is_ok());
}

#[test]
fn test_parser_secret_typed_variable() {
    let source = "secret var x: int64 = 42";
    assert!(parse_source(source).is_ok());
}

#[test]
fn test_parser_array_literal() {
    let source = "var arr = [1, 2, 3, 4, 5]";
    assert!(parse_source(source).is_ok());
}

// ===========================================
// Semantic Analysis Tests - Valid Programs
// ===========================================

#[test]
fn test_semantic_simple_program() {
    let source = r#"
var x = 10
var y = 20
var z = x + y
"#;
    assert!(analyze_source(source).is_ok());
}

#[test]
fn test_semantic_function_call() {
    let source = r#"
def double(n: int64) -> int64:
  return n * 2

var result = double(21)
"#;
    assert!(analyze_source(source).is_ok());
}

#[test]
fn test_semantic_builtin_print() {
    // print is a statement, test in proper context
    let source = r#"
var msg = "Hello, World!"
print(msg)
"#;
    assert!(analyze_source(source).is_ok());
}

#[test]
fn test_semantic_array_operations() {
    // create_array takes no required parameters
    let source = r#"
var arr = create_array()
discard array_push(arr, 1)
var len = array_length(arr)
"#;
    assert!(analyze_source(source).is_ok());
}

#[test]
fn test_semantic_nested_function_calls() {
    let source = r#"
def inner(x: int64) -> int64:
  return x + 1

def outer(x: int64) -> int64:
  return inner(x) * 2

var result = outer(5)
"#;
    assert!(analyze_source(source).is_ok());
}

// ===========================================
// Semantic Analysis Tests - Object Methods
// ===========================================

#[test]
fn test_semantic_client_store_take_share() {
    let source = r#"
secret var share = ClientStore.take_share(0, 0)
"#;
    assert!(analyze_source(source).is_ok());
}

#[test]
fn test_semantic_mpc_methods() {
    let source = r#"
var party = Mpc.party_id()
var total = Mpc.n_parties()
var thresh = Mpc.threshold()
"#;
    assert!(analyze_source(source).is_ok());
}

#[test]
fn test_semantic_share_operations() {
    let source = r#"
var s1 = Share.from_clear(10)
var s2 = Share.from_clear(20)
var sum = Share.add(s1, s2)
"#;
    assert!(analyze_source(source).is_ok());
}

// ===========================================
// Semantic Analysis Tests - Error Detection
// ===========================================

#[test]
fn test_semantic_error_undefined_variable() {
    let source = "var x = undefined_var + 1";
    assert!(expect_error_containing(source, "undefined_var"));
}

#[test]
fn test_semantic_error_undefined_function() {
    let source = "var x = undefined_function(42)";
    assert!(expect_error_containing(source, "undefined_function"));
}

#[test]
fn test_semantic_error_duplicate_variable() {
    let source = r#"
var x = 10
var x = 20
"#;
    let result = analyze_source(source);
    assert!(result.is_err(), "Should detect duplicate variable");
}

#[test]
fn test_semantic_error_wrong_argument_count() {
    let source = r#"
def foo(a: int64, b: int64) -> int64:
  return a + b

var x = foo(1)
"#;
    assert!(expect_error_containing(source, "argument"));
}

// ===========================================
// Semantic Analysis Tests - Type Checking
// ===========================================

#[test]
fn test_semantic_secret_assignment_valid() {
    let source = r#"
secret var share: int64 = ClientStore.take_share(0, 0)
"#;
    assert!(analyze_source(source).is_ok());
}

#[test]
fn test_semantic_secret_in_function() {
    let source = r#"
secret def process(s: secret int64) -> secret int64:
  return s * 2
"#;
    assert!(analyze_source(source).is_ok());
}

// ===========================================
// Semantic Phase Tests - List Iteration
// ===========================================

#[test]
fn test_semantic_for_loop_list_iteration() {
    let source = r#"
var items: List[int64] = [1, 2, 3]
var sum = 0
for item in items:
  sum = sum + item
"#;
    assert!(analyze_source(source).is_ok());
}

#[test]
fn test_semantic_for_loop_list_literal() {
    let source = r#"
var total = 0
for x in [10, 20, 30]:
  total = total + x
"#;
    assert!(analyze_source(source).is_ok());
}

#[test]
fn test_semantic_for_loop_element_type_inferred() {
    // The loop variable should have the same type as list elements
    let source = r#"
var numbers: List[int64] = [1, 2, 3]
var total = 0
for n in numbers:
  total = total + n
"#;
    assert!(analyze_source(source).is_ok());
}

#[test]
fn test_semantic_for_loop_range_still_works() {
    // Ensure range-based iteration still works
    let source = r#"
var sum = 0
for i in 0..10:
  sum = sum + i
"#;
    assert!(analyze_source(source).is_ok());
}

#[test]
fn test_semantic_error_iterate_non_iterable() {
    // Cannot iterate over a non-iterable type
    let source = r#"
var x = 42
for item in x:
  print(item)
"#;
    assert!(analyze_source(source).is_err());
}

// ===========================================
// Semantic Phase Tests - String Iteration
// ===========================================

#[test]
fn test_semantic_for_loop_string_iteration() {
    // Iterate over characters in a string
    let source = r#"
var text = "hello"
for ch in text:
  print(ch)
"#;
    assert!(analyze_source(source).is_ok());
}

#[test]
fn test_semantic_for_loop_string_literal() {
    // Iterate directly over a string literal
    let source = r#"
for ch in "world":
  print(ch)
"#;
    assert!(analyze_source(source).is_ok());
}

#[test]
fn test_semantic_for_loop_string_element_is_string() {
    // The loop variable should be a string (character)
    // so we can concatenate it with another string
    let source = r#"
var text = "abc"
var result = ""
for ch in text:
  result = result + ch
"#;
    assert!(analyze_source(source).is_ok());
}

// ===========================================
// Full Compilation Tests - Valid Programs
// ===========================================

#[test]
fn test_compile_hello_world() {
    let source = r#"
print("Hello, World!")
"#;
    assert!(compile_source(source).is_ok());
}

#[test]
fn test_compile_arithmetic() {
    let source = r#"
var a = 10
var b = 20
var sum = a + b
var diff = a - b
var prod = a * b
var quot = b / a
print(sum)
"#;
    assert!(compile_source(source).is_ok());
}

#[test]
fn test_compile_function_definition_and_call() {
    let source = r#"
def double(n: int64) -> int64:
  return n * 2

var result = double(5)
"#;
    assert!(compile_source(source).is_ok());
}

#[test]
fn test_compile_conditionals() {
    let source = r#"
var x = 10
if x > 5:
  print("big")
else:
  print("small")
"#;
    assert!(compile_source(source).is_ok());
}

#[test]
fn test_compile_loops() {
    let source = r#"
var i = 0
while i < 10:
  i = i + 1
"#;
    assert!(compile_source(source).is_ok());
}

#[test]
fn test_compile_arrays() {
    let source = r#"
var arr = create_array()
discard array_push(arr, 10)
discard array_push(arr, 20)
var first = arr[0]
"#;
    assert!(compile_source(source).is_ok());
}

#[test]
fn test_compile_for_loop_list_iteration() {
    let source = r#"
var items: List[int64] = [1, 2, 3, 4, 5]
var total = 0
for item in items:
  total = total + item
"#;
    assert!(compile_source(source).is_ok());
}

#[test]
fn test_compile_for_loop_list_literal() {
    let source = r#"
var sum = 0
for x in [10, 20, 30]:
  sum = sum + x
"#;
    assert!(compile_source(source).is_ok());
}

#[test]
fn test_compile_for_loop_range() {
    let source = r#"
var sum = 0
for i in 0..5:
  sum = sum + i
"#;
    assert!(compile_source(source).is_ok());
}

#[test]
fn test_compile_for_loop_nested_with_list() {
    let source = r#"
var matrix: List[int64] = [1, 2, 3]
var total = 0
for i in 0..3:
  for val in matrix:
    total = total + val
"#;
    assert!(compile_source(source).is_ok());
}

#[test]
fn test_compile_for_loop_string_iteration() {
    let source = r#"
var text = "hello"
for ch in text:
  print(ch)
"#;
    assert!(compile_source(source).is_ok());
}

#[test]
fn test_compile_for_loop_string_literal() {
    let source = r#"
for ch in "world":
  print(ch)
"#;
    assert!(compile_source(source).is_ok());
}

#[test]
fn test_compile_for_loop_string_concatenation() {
    let source = r#"
var text = "abc"
var result = ""
for ch in text:
  result = result + ch
"#;
    assert!(compile_source(source).is_ok());
}

// ===========================================
// Full Compilation Tests - Builtin Objects
// ===========================================

#[test]
fn test_compile_client_store() {
    let source = r#"
secret var share = ClientStore.take_share(0, 0)
"#;
    assert!(compile_source(source).is_ok());
}

#[test]
fn test_compile_mpc_operations() {
    let source = r#"
var my_id = Mpc.party_id()
var parties = Mpc.n_parties()
if my_id == 0:
  print("I am the leader")
"#;
    assert!(compile_source(source).is_ok());
}

#[test]
fn test_compile_share_creation() {
    let source = r#"
var s = Share.from_clear(42)
"#;
    assert!(compile_source(source).is_ok());
}

// ===========================================
// Full Compilation Tests - Complex Programs
// ===========================================

#[test]
fn test_compile_nested_conditionals() {
    let source = r#"
var x = 10
var y = 20
if x > 5:
  if y > 15:
    print("both big")
  else:
    print("x big, y small")
else:
  print("x small")
"#;
    assert!(compile_source(source).is_ok());
}

#[test]
fn test_compile_multiple_functions() {
    let source = r#"
def add(a: int64, b: int64) -> int64:
  return a + b

def multiply(a: int64, b: int64) -> int64:
  return a * b

var sum = add(3, 4)
var prod = multiply(sum, 2)
"#;
    assert!(compile_source(source).is_ok());
}

#[test]
fn test_compile_recursive_function() {
    let source = r#"
def fib(n: int64) -> int64:
  if n <= 1:
    return n
  return fib(n - 1) + fib(n - 2)

var result = fib(10)
"#;
    assert!(compile_source(source).is_ok());
}

// ===========================================
// Syntax Error Tests
// ===========================================

#[test]
fn test_syntax_error_unclosed_paren() {
    let source = "var x = (1 + 2";
    assert!(compile_source(source).is_err());
}

#[test]
fn test_syntax_error_missing_expression() {
    let source = "var x =";
    assert!(compile_source(source).is_err());
}

#[test]
fn test_syntax_error_invalid_field_access() {
    let source = "var x = obj.";
    assert!(compile_source(source).is_err());
}

// ===========================================
// Edge Cases
// ===========================================

#[test]
fn test_empty_program() {
    let source = "";
    assert!(compile_source(source).is_ok());
}

#[test]
fn test_only_comments() {
    let source = r#"
# This is a comment
# Another comment
"#;
    assert!(compile_source(source).is_ok());
}

#[test]
fn test_deeply_nested_expressions() {
    let source = "var x = ((((1 + 2) * 3) - 4) / 5)";
    assert!(compile_source(source).is_ok());
}

#[test]
fn test_long_identifier() {
    let source = "var this_is_a_very_long_variable_name_that_should_still_work = 42";
    assert!(compile_source(source).is_ok());
}

// ===========================================
// UFCS Transformation Tests
// ===========================================

#[test]
fn test_ufcs_builtin_object_preserved() {
    let source = "secret var s = ClientStore.take_share(0, 0)";
    assert!(compile_source(source).is_ok());
}

#[test]
fn test_ufcs_share_methods() {
    let source = r#"
var s1 = Share.from_clear(10)
var s2 = Share.from_clear(20)
var result = Share.add(s1, s2)
"#;
    assert!(compile_source(source).is_ok());
}

// ===========================================
// Import Syntax Tests (Parser Only)
// ===========================================

#[test]
fn test_import_syntax() {
    let source = "import foo.bar";
    assert!(parse_source(source).is_ok());
}

#[test]
fn test_import_with_alias() {
    let source = "import foo.bar as baz";
    assert!(parse_source(source).is_ok());
}

#[test]
fn test_multiple_imports() {
    let source = r#"
import module1
import module2.submodule
import module3 as m3
"#;
    assert!(parse_source(source).is_ok());
}
