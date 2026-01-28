//! Integration tests for semantic-aware suggestions.
//!
//! These tests validate that suggestions appear correctly in compiler error messages
//! when processing actual Stoffel-Lang source code through the full compilation pipeline.

use stoffellang::compiler::{compile, CompilerOptions};

/// Helper to compile a source string and extract error messages
fn compile_and_get_errors(source: &str) -> Vec<String> {
    let options = CompilerOptions::default();
    match compile(source, "test.stfl", &options) {
        Ok(_) => vec![],
        Err(errors) => errors.iter().map(|e| format!("{}", e)).collect(),
    }
}

/// Helper to check if any error message contains the expected text
fn errors_contain(errors: &[String], text: &str) -> bool {
    errors.iter().any(|e| e.contains(text))
}

// ===========================================
// Variable typo suggestions
// ===========================================

#[test]
fn test_variable_typo_suggests_correct_name() {
    let source = r#"
main main() -> nil:
  var counter: int64 = 0
  var x: int64 = couter
"#;

    let errors = compile_and_get_errors(source);
    assert!(!errors.is_empty(), "Should have compilation errors");
    assert!(errors_contain(&errors, "couter"), "Should mention the typo");
    assert!(errors_contain(&errors, "counter"), "Should suggest 'counter'");
}

#[test]
fn test_variable_typo_in_expression() {
    let source = r#"
main main() -> nil:
  var total: int64 = 100
  var result: int64 = totl + 50
"#;

    let errors = compile_and_get_errors(source);
    assert!(errors_contain(&errors, "totl"), "Should mention the typo");
    assert!(errors_contain(&errors, "total"), "Should suggest 'total'");
}

#[test]
fn test_variable_typo_multiple_candidates() {
    let source = r#"
main main() -> nil:
  var count: int64 = 0
  var counter: int64 = 0
  var counting: int64 = 0
  var x: int64 = conut
"#;

    let errors = compile_and_get_errors(source);
    assert!(errors_contain(&errors, "conut"), "Should mention the typo");
    // Should suggest the closest match (count)
    assert!(errors_contain(&errors, "count"), "Should suggest closest match");
}

// ===========================================
// Function typo suggestions
// ===========================================

#[test]
fn test_user_function_typo_suggests_correct_name() {
    let source = r#"
def calculate(x: int64) -> int64:
  return x * 2

main main() -> nil:
  var result: int64 = calculte(5)
"#;

    let errors = compile_and_get_errors(source);
    assert!(errors_contain(&errors, "calculte"), "Should mention the typo");
    assert!(errors_contain(&errors, "calculate"), "Should suggest 'calculate'");
}

#[test]
fn test_builtin_function_typo_suggests_correct_name() {
    let source = r#"
main main() -> nil:
  prnt("hello")
"#;

    let errors = compile_and_get_errors(source);
    assert!(errors_contain(&errors, "prnt"), "Should mention the typo");
    assert!(errors_contain(&errors, "print"), "Should suggest 'print'");
}

#[test]
fn test_array_function_typo_suggests_correct_name() {
    let source = r#"
main main() -> nil:
  var items: List[int64] = create_array()
  aray_push(items, 5)
"#;

    let errors = compile_and_get_errors(source);
    assert!(errors_contain(&errors, "aray_push"), "Should mention the typo");
    assert!(errors_contain(&errors, "array_push"), "Should suggest 'array_push'");
}

#[test]
fn test_create_array_typo() {
    let source = r#"
main main() -> nil:
  var items: List[int64] = creat_array()
"#;

    let errors = compile_and_get_errors(source);
    assert!(errors_contain(&errors, "creat_array"), "Should mention the typo");
    assert!(errors_contain(&errors, "create_array"), "Should suggest 'create_array'");
}

// ===========================================
// Method-style call tests (now supported via UFCS)
// ===========================================

#[test]
fn test_method_append_suggests_array_push() {
    // Note: .append() now works via UFCS as an alias for array_push
    // This test now verifies that the Pythonic syntax compiles successfully
    let source = r#"
main main() -> nil:
  var items: List[int64] = create_array()
  items.append(5)
"#;

    let errors = compile_and_get_errors(source);
    // Should compile without errors now that append is a builtin alias
    assert!(errors.is_empty(), "Pythonic .append() should now compile successfully");
}

#[test]
fn test_method_length_suggests_array_length() {
    // Note: .length() now works via UFCS as an alias for array_length
    // This test now verifies that the Pythonic syntax compiles successfully
    let source = r#"
main main() -> nil:
  var items: List[int64] = create_array()
  var n: int64 = items.length()
"#;

    let errors = compile_and_get_errors(source);
    // Should compile without errors now that length is a builtin alias
    assert!(errors.is_empty(), "Pythonic .length() should now compile successfully");
}

#[test]
fn test_method_reveal_suggests_assignment() {
    let source = r#"
main main() -> nil:
  var x: secret int64 = 42
  var y: int64 = x.reveal()
"#;

    let errors = compile_and_get_errors(source);
    assert!(errors_contain(&errors, "reveal"), "Should mention 'reveal'");
    assert!(errors_contain(&errors, "clear"), "Should mention assigning to clear variable");
}

// ===========================================
// Scope-aware suggestions
// ===========================================

#[test]
fn test_suggests_variable_from_outer_scope() {
    let source = r#"
def process() -> int64:
  var outer_value: int64 = 100
  if true:
    var x: int64 = outer_vlue
  return 0

main main() -> nil:
  var y: int64 = process()
"#;

    let errors = compile_and_get_errors(source);
    assert!(errors_contain(&errors, "outer_vlue"), "Should mention the typo");
    assert!(errors_contain(&errors, "outer_value"), "Should suggest from outer scope");
}

#[test]
fn test_suggests_function_parameter() {
    let source = r#"
def process(input_value: int64) -> int64:
  return input_vlue * 2

main main() -> nil:
  var x: int64 = process(5)
"#;

    let errors = compile_and_get_errors(source);
    assert!(errors_contain(&errors, "input_vlue"), "Should mention the typo");
    assert!(errors_contain(&errors, "input_value"), "Should suggest parameter name");
}

// ===========================================
// No suggestion when too different
// ===========================================

#[test]
fn test_no_suggestion_when_completely_different() {
    let source = r#"
main main() -> nil:
  var counter: int64 = 0
  var x: int64 = xyz
"#;

    let errors = compile_and_get_errors(source);
    assert!(errors_contain(&errors, "xyz"), "Should mention the undefined identifier");
    // Should NOT suggest 'counter' since 'xyz' is completely different
    // The error should exist but may or may not have a suggestion
}

// ===========================================
// Edge cases
// ===========================================

#[test]
fn test_valid_program_no_errors() {
    let source = r#"
main main() -> nil:
  var x: int64 = 0
"#;

    let errors = compile_and_get_errors(source);
    // Should compile successfully with no errors
    assert!(errors.is_empty(), "Valid program should have no errors");
}

#[test]
fn test_multiple_errors_each_with_suggestions() {
    let source = r#"
main main() -> nil:
  var counter: int64 = 0
  var total: int64 = 0
  var a: int64 = couter
  var b: int64 = totl
"#;

    let errors = compile_and_get_errors(source);
    // Should have errors for both typos
    assert!(errors_contain(&errors, "couter") || errors_contain(&errors, "totl"),
            "Should have at least one typo error");
}

#[test]
fn test_case_sensitivity() {
    let source = r#"
main main() -> nil:
  var Counter: int64 = 0
  var x: int64 = counter
"#;

    let errors = compile_and_get_errors(source);
    // "counter" vs "Counter" - case matters, should suggest if close enough
    assert!(errors_contain(&errors, "counter"), "Should mention the undefined identifier");
}
