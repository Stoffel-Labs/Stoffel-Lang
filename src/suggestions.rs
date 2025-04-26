use edit_distance::edit_distance;
use std::collections::HashMap;

pub fn suggest_identifier(misspelled: &str, valid_identifiers: &[String]) -> Option<String> {
    if valid_identifiers.is_empty() {
        return None;
    }

    let mut best_match = &valid_identifiers[0];
    let mut min_distance = edit_distance(misspelled, &valid_identifiers[0]);

    for identifier in valid_identifiers.iter().skip(1) {
        let distance = edit_distance(misspelled, identifier);
        if distance < min_distance {
            min_distance = distance;
            best_match = identifier;
        }
    }

    let threshold = (misspelled.len() as f64 * 0.4).max(2.0) as usize;
    if min_distance <= threshold {
        Some(best_match.clone())
    } else {
        None
    }
}

pub fn suggest_keyword(misspelled: &str) -> Option<String> {
    let keywords = vec![
        "let", "var", "proc", "type", "object", "enum", "if", "else", "elif",
        "while", "for", "in", "return", "yield", "break", "continue", "true",
        "false", "nil", "secret", "and", "or", "not", "is", "as", "import", "from"
    ];

    let valid_keywords: Vec<String> = keywords.iter().map(|k| k.to_string()).collect();
    suggest_identifier(misspelled, &valid_keywords)
}

pub fn suggest_syntax_fix(error_message: &str) -> Option<String> {
    let suggestions = HashMap::from([
        ("unterminated string literal", "Add a closing double quote (\") to complete the string"),
        ("unexpected character", "Remove or replace the invalid character"),
        ("expected expression", "Try adding a value, variable name, or function call"),
        ("expected identifier", "Use a valid variable or function name"),
        ("expected type", "Specify a type like 'int', 'string', or a custom type"),
        ("inconsistent dedentation", "Make sure all indentation levels are consistent"),
        ("tabs are not allowed", "Use spaces for indentation instead of tabs"),
    ]);

    for (pattern, suggestion) in suggestions {
        if error_message.to_lowercase().contains(&pattern.to_lowercase()) {
            return Some(suggestion.to_string());
        }
    }

    None
}
