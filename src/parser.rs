use crate::ast::{AstNode, Parameter, FieldDefinition, EnumMember, Value};
use crate::errors::{CompilerError, SourceLocation, CompilerResult};
use std::fmt;
use std::iter::Peekable;
use std::slice::Iter;
use std::collections::VecDeque;

use crate::lexer::Token;

struct Parser<'a> {
    tokens: Peekable<Iter<'a, Token>>,
    current_token: Option<&'a Token>, // Store the current token for easier access
    filename: String,
    current_line: usize,
    current_column: usize,
}

impl<'a> Parser<'a> {
    fn new(tokens: &'a [Token], filename: &str) -> Self {
        let mut iter = tokens.iter().peekable();
        let current = iter.next();
        Parser { 
            tokens: iter, 
            current_token: current,
            filename: filename.to_string(),
            current_line: 1,
            current_column: 1,
        }
    }

    // Consumes the current token and advances to the next one.
    fn advance(&mut self) -> Option<&'a Token> {
        let consumed = self.current_token;
        self.current_token = self.tokens.next();
        consumed
    }

    // Peeks at the next token without consuming the current one.
    fn peek(&mut self) -> Option<&&'a Token> {
        self.tokens.peek()
    }

    // Checks if the current token matches the expected kind.
    fn check(&self, kind: &Token) -> bool {
        match self.current_token {
            Some(t) => std::mem::discriminant(t) == std::mem::discriminant(kind),
            None => false,
        }
    }

     // Checks if the current token is a specific keyword.
    fn check_keyword(&self, keyword: &str) -> bool {
        matches!(self.current_token, Some(Token::Keyword(k)) if k == keyword)
    }

    // Consumes the current token if it matches the expected kind, otherwise returns an error.
    fn consume(&mut self, expected: &Token, error_message: &str) -> CompilerResult<&'a Token> {
        if self.check(expected) {
            Ok(self.advance().unwrap()) // Safe unwrap because check succeeded
        } else {
            let expected_str = match expected {
                Token::Identifier(_) => "identifier".to_string(),
                Token::Keyword(k) => format!("keyword '{}'", k),
                Token::Operator(op) => format!("operator '{}'", op),
                _ => format!("{:?}", expected),
            };
            
            let found_str = match self.current_token {
                Some(token) => format!("{:?}", token),
                None => "end of file".to_string(),
            };
            
            let location = SourceLocation { file: self.filename.clone(), line: self.current_line, column: self.current_column };
            Err(CompilerError::syntax_error(format!("{} Expected {}, found {}", error_message, expected_str, found_str), location)
                .with_hint(format!("Try adding {} here", expected_str)))
        }
    }

     // Consumes the current token if it's a specific keyword, otherwise returns an error.
    fn consume_keyword(&mut self, keyword: &str, error_message: &str) -> CompilerResult<&'a Token> {
        if self.check_keyword(keyword) {
             Ok(self.advance().unwrap()) // Safe unwrap because check succeeded
        } else {
             let found_str = match self.current_token {
                 Some(token) => format!("{:?}", token),
                 None => "end of file".to_string(),
             };
             
             let location = SourceLocation { file: self.filename.clone(), line: self.current_line, column: self.current_column };
             Err(CompilerError::syntax_error(
                 format!("{} Expected keyword '{}', found {}", error_message, keyword, found_str), 
                 location
             ).with_hint(format!("Try using the '{}' keyword here", keyword)))
        }
    }

    // --- Parsing Functions ---

    // Parses a full program (sequence of statements/declarations)
    fn parse_program(&mut self) -> CompilerResult<AstNode> {
        let mut statements = Vec::new();
        while !self.check(&Token::Eof) && !self.check(&Token::Dedent) { // Stop at EOF or Dedent
            statements.push(self.parse_statement_or_declaration()?);
            // Skip optional newlines between statements
            while self.check(&Token::Newline) {
                self.advance();
            }
        }
        // If only one statement, return it directly, otherwise wrap in a block
        if statements.len() == 1 {
             Ok(statements.pop().unwrap())
        } else {
             Ok(AstNode::Block(statements))
        }
    }

    // Parses either a statement or a declaration
    fn parse_statement_or_declaration(&mut self) -> CompilerResult<AstNode> {
        // Look ahead to determine if it's a declaration (let, var, proc, type, etc.)
        match self.current_token {
            Some(Token::Keyword(k)) => match k.as_str() {
                "let" | "var" => self.parse_variable_declaration_impl(false), // Not secret by default
                "proc" => self.parse_function_definition(),
                "type" | "object" | "enum" => self.parse_type_definition(),
                "if" => self.parse_if_statement_or_expression(), // Needs refinement
                "while" => self.parse_while_loop(),
                "for" => self.parse_for_loop(),
                "return" => self.parse_return_statement(),
                // Add other statement keywords (break, continue, yield, import, etc.)
                _ => self.parse_expression_statement(), // Assume expression if keyword doesn't start a known statement/decl
            },
            Some(Token::Identifier(_)) => self.parse_expression_statement(), // Could be assignment or function call
            // Add cases for other statement starters if necessary
            _ => {
                let found_str = match self.current_token {
                    Some(token) => format!("{:?}", token),
                    None => "end of file".to_string(),
                };
                
                let location = SourceLocation { file: self.filename.clone(), line: self.current_line, column: self.current_column };
                Err(CompilerError::syntax_error(format!("Unexpected token at start of statement/declaration: {}", found_str), location))
            }
        }
    }

    fn parse_variable_declaration_impl(&mut self, is_secret: bool) -> CompilerResult<AstNode> {
        let is_mutable = self.check_keyword("var");
        self.advance(); // Consume 'let' or 'var'

        let name_token = self.consume(&Token::Identifier("".to_string()), "Expected variable name")?;
        let name = match name_token {
            Token::Identifier(n) => n.clone(),
            _ => unreachable!(), // consume ensures it's an identifier
        };

        let mut type_is_secret = false;
        let mut type_annotation = None;
        if self.check(&Token::Colon) {
            self.advance(); // Consume ':'
            // Check for 'secret' modifying the type
            if self.check_keyword("secret") {
                self.advance(); // Consume 'secret'
                type_is_secret = true;
            }
            type_annotation = Some(Box::new(self.parse_type_annotation()?));

        }

        let mut value = None;
        if self.check(&Token::Assign) {
            self.advance(); // Consume '='
            value = Some(Box::new(self.parse_expression()?));
        } else if type_annotation.is_none() {
             let location = SourceLocation { 
                 file: self.filename.clone(), 
                 line: self.current_line, 
                 column: self.current_column 
             };
             return Err(CompilerError::syntax_error("Variable declaration needs either a type annotation or an initial value", location)
                 .with_hint("Add a type annotation with ':' or initialize with '='"));
        }

        // Expect newline or EOF after declaration
        if !self.check(&Token::Newline) && !self.check(&Token::Eof) && !self.check(&Token::Dedent) {
             // Allow declarations followed by ';' in theory, but Pythonic style prefers newline
             // return Err(CompilerError { message: format!("Expected newline or EOF after variable declaration, found {:?}", self.current_token) });
        }

        Ok(AstNode::VariableDeclaration {
            name,
            type_annotation,
            value,
            is_mutable,
        })
    }

    // Parses type annotations (e.g., int, string, MyObject, list[int], secret int)
    // IMPORTANT: This function *only* parses the type name/structure itself.
    // The 'secret' keyword must be consumed *before* calling this function.
    fn parse_type_annotation(&mut self) -> CompilerResult<AstNode> {
         match self.current_token {
            Some(Token::Identifier(name)) => {
                let base_name = name.clone();
                self.advance(); // Consume identifier
                // TODO: Handle generics like list[int]
                // TODO: Handle qualified names like module.Type
                Ok(AstNode::Identifier(base_name))
            }
            // TODO: Add cases for ListType, TupleType, DictType, FunctionType literals
            _ => {
                let found_str = match self.current_token {
                    Some(token) => format!("{:?}", token),
                    None => "end of file".to_string(),
                };
                
                let location = SourceLocation { file: self.filename.clone(), line: self.current_line, column: self.current_column };
                Err(CompilerError::syntax_error(format!("Expected type name identifier, found {}", found_str), location))
            }
        }
    }

    // Placeholder for expression parsing (needs operator precedence, etc.)
    fn parse_expression(&mut self) -> CompilerResult<AstNode> {
        // Very basic implementation: parse literals or identifiers for now
        match self.current_token {
            Some(Token::IntLiteral(i)) => { self.advance(); Ok(AstNode::Literal(Value::Int(*i))) }
            Some(Token::FloatLiteral(f)) => { self.advance(); Ok(AstNode::Literal(Value::Float(*f))) }
            Some(Token::StringLiteral(s)) => { self.advance(); Ok(AstNode::Literal(Value::String(s.clone()))) }
            Some(Token::BoolLiteral(b)) => { self.advance(); Ok(AstNode::Literal(Value::Bool(*b))) }
            Some(Token::NilLiteral) => { self.advance(); Ok(AstNode::Literal(Value::Nil)) }
            Some(Token::Identifier(name)) => { self.advance(); Ok(AstNode::Identifier(name.clone())) }
            // TODO: Add function calls, binary ops, unary ops, field access, etc.
            _ => {
                let found_str = match self.current_token {
                    Some(token) => format!("{:?}", token),
                    None => "end of file".to_string(),
                };
                
                let location = SourceLocation { file: self.filename.clone(), line: self.current_line, column: self.current_column };
                Err(CompilerError::syntax_error(format!("Expected expression, found {}", found_str), location)
                    .with_hint("An expression can be a literal, identifier, or function call"))
            }
        }
    }

    // Placeholder for expression statements (e.g., assignments, function calls)
    fn parse_expression_statement(&mut self) -> CompilerResult<AstNode> {
        let expr = self.parse_expression()?;
        // Could be assignment: expr = value
        if self.check(&Token::Assign) {
            self.advance(); // Consume '='
            let value = self.parse_expression()?;
            // Expect newline or EOF
             if !self.check(&Token::Newline) && !self.check(&Token::Eof) && !self.check(&Token::Dedent) {
                 // return Err(CompilerError { message: format!("Expected newline or EOF after assignment, found {:?}", self.current_token) });
             }
            Ok(AstNode::Assignment { target: Box::new(expr), value: Box::new(value) })
        } else {
            // Assume it's just an expression used as a statement (e.g., function call)
            // Expect newline or EOF
             if !self.check(&Token::Newline) && !self.check(&Token::Eof) && !self.check(&Token::Dedent) {
                 // return Err(CompilerError { message: format!("Expected newline or EOF after expression statement, found {:?}", self.current_token) });
             }
            Ok(expr) // Or wrap in DiscardStmt? For now, just the expression.
        }
    }

    // --- Placeholders for other parsing functions ---

    fn parse_function_definition(&mut self) -> CompilerResult<AstNode> {
         let location = SourceLocation { file: self.filename.clone(), line: self.current_line, column: self.current_column };
         Err(CompilerError::syntax_error("Function definition parsing not implemented", location))
    }

    fn parse_type_definition(&mut self) -> CompilerResult<AstNode> {
         let location = SourceLocation { file: self.filename.clone(), line: self.current_line, column: self.current_column };
         Err(CompilerError::syntax_error("Type definition parsing not implemented", location))
         // Remember to check for 'secret' before 'object', 'enum', or the target type in 'type alias ='
    }

    fn parse_if_statement_or_expression(&mut self) -> CompilerResult<AstNode> {
         let location = SourceLocation { file: self.filename.clone(), line: self.current_line, column: self.current_column };
         Err(CompilerError::syntax_error("If statement/expression parsing not implemented", location))
    }

    fn parse_while_loop(&mut self) -> CompilerResult<AstNode> {
         let location = SourceLocation { file: self.filename.clone(), line: self.current_line, column: self.current_column };
         Err(CompilerError::syntax_error("While loop parsing not implemented", location))
    }

    fn parse_for_loop(&mut self) -> CompilerResult<AstNode> {
         let location = SourceLocation { file: self.filename.clone(), line: self.current_line, column: self.current_column };
         Err(CompilerError::syntax_error("For loop parsing not implemented", location))
    }

    fn parse_return_statement(&mut self) -> CompilerResult<AstNode> {
         let location = SourceLocation { file: self.filename.clone(), line: self.current_line, column: self.current_column };
         Err(CompilerError::syntax_error("Return statement parsing not implemented", location))
    }
}

pub fn parse(tokens: &[Token], filename: &str) -> CompilerResult<AstNode> {
    let mut parser = Parser::new(tokens, filename);
    // The top-level parsing function (e.g., parse_program or parse_module)
    let root_node = parser.parse_program()?;

    // Check if all tokens were consumed (except EOF)
    if !parser.check(&Token::Eof) {
        let found_str = match parser.current_token {
            Some(token) => format!("{:?}", token),
            None => "end of file".to_string(),
        };
        
        let location = SourceLocation { file: parser.filename, line: parser.current_line, column: parser.current_column };
        Err(CompilerError::syntax_error(format!("Unexpected token after parsing finished: {}", found_str), location))
    } else {
        Ok(root_node)
    }
}
