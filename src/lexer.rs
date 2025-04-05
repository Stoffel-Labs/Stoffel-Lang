use std::fmt;

#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    Identifier(String),
    Keyword(String),
    Operator(String),
    IntLiteral(i64),
    FloatLiteral(f64),
    StringLiteral(String),
    BoolLiteral(bool),
    NilLiteral,
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Comma,
    Dot,
    Colon,
    Assign,
    Semicolon,
    Newline,
    Indent,
    Dedent,
    Eof,
}

#[derive(Debug, Clone, PartialEq)]
pub struct LexerError {
    pub message: String,
    pub line: usize,
    pub column: usize,
}

impl fmt::Display for LexerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Lexer Error at {}:{}: {}", self.line, self.column, self.message)
    }
}

impl std::error::Error for LexerError {}

pub fn tokenize(source: &str) -> Result<Vec<Token>, LexerError> {
    // Placeholder implementation
    println!("Lexing source: {}", source);
    Ok(vec![Token::Eof])
}
