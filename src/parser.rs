use crate::ast::{AstNode, Parameter, Pragma, Value};
use crate::errors::{CompilerError, CompilerResult, SourceLocation};
use std::iter::Peekable;
use std::mem;
use std::slice::Iter;

use crate::lexer::{TokenInfo, TokenKind};

struct Parser<'a> {
    tokens: Peekable<Iter<'a, TokenInfo>>,
    current_token_info: Option<&'a TokenInfo>, // Store the current token info
    filename: String,
    last_location: SourceLocation,
    node_id_counter: usize, // Counter for assigning unique node IDs
}

impl<'a> Parser<'a> {
    fn new(tokens: &'a [TokenInfo], filename: &str) -> Self {
        let mut iter = tokens.iter().peekable();
        let current = iter.next();
        Parser { 
            tokens: iter, 
            current_token_info: current,
            filename: filename.to_string(),
            last_location: SourceLocation { file: filename.to_string(), line: 1, column: 1 },
            node_id_counter: 0, // Initialize counter
        }
    }

    // Consumes the current token and advances to the next one.
    // Returns the *consumed* token's info.
    fn advance(&mut self) -> Option<&'a TokenInfo> {
        let consumed = self.current_token_info;
        if let Some(info) = consumed {
            self.last_location = info.location.clone(); // Update last location
        }
        self.current_token_info = self.tokens.next();
        consumed
    }

    // Peeks at the next token without consuming the current one.
    fn peek(&mut self) -> Option<&&'a TokenInfo> {
        self.tokens.peek()
    }

    // Checks if the current token matches the expected kind.
    fn check(&self, kind: &TokenKind) -> bool {
        match self.current_token_info {
            Some(info) => mem::discriminant(&info.kind) == mem::discriminant(kind),
            None => false,
        }
    }

     // Checks if the current token is a specific keyword.
    fn check_keyword(&self, keyword: &str) -> bool {
        matches!(self.current_token_info, Some(TokenInfo { kind: TokenKind::Keyword(k), .. }) if k == keyword)
    }

    // --- Core token consumption helpers ---
    // Consumes the current token if it matches the expected kind, otherwise returns an error.
    fn consume(&mut self, expected: &TokenKind, error_message: &str) -> CompilerResult<&'a TokenInfo> {
        if self.check(expected) {
            Ok(self.advance().unwrap()) // Safe unwrap because check succeeded
        } else {
            let expected_str = match expected {
                TokenKind::Identifier(_) => "identifier".to_string(),
                TokenKind::Keyword(k) => format!("keyword '{}'", k),
                TokenKind::Operator(op) => format!("operator '{}'", op),
                _ => format!("{:?}", expected),
            };
            
            let (found_str, location) = match self.current_token_info {
                Some(token) => (format!("{:?}", token), token.location.clone()),
                None => ("end of file".to_string(), self.last_location.clone()),
            };
            
            Err(CompilerError::syntax_error(format!("{} Expected {}, found {}", error_message, expected_str, found_str), location)
                .with_hint(format!("Try adding {} here", expected_str)))
        }
    }

     // Consumes the current token if it's a specific keyword, otherwise returns an error.
    fn consume_keyword(&mut self, keyword: &str, error_message: &str) -> CompilerResult<&'a TokenInfo> {
        if self.check_keyword(keyword) {
             Ok(self.advance().unwrap()) // Safe unwrap because check succeeded
        } else {
             let (found_str, location) = match self.current_token_info {
                 Some(token) => (format!("{:?}", token), token.location.clone()),
                 None => ("end of file".to_string(), self.last_location.clone()),
             };
             
             Err(CompilerError::syntax_error(
                 format!("{} Expected keyword '{}', found {}", error_message, keyword, found_str), 
                 location
             ).with_hint(format!("Try using the '{}' keyword here", keyword)))
        }
    }

    // Helper to get the next unique node ID
    fn next_node_id(&mut self) -> usize {
        let id = self.node_id_counter;
        self.node_id_counter += 1;
        id
    }

    // Helper to parse an indented block of statements
    fn parse_indented_block(&mut self) -> CompilerResult<AstNode> {
        // Allow multiple newlines before the indented block starts
        self.consume(&TokenKind::Newline, "Expected newline after ':' before indented block")?;
        while self.check(&TokenKind::Newline) {
            self.advance(); // Skip extra blank lines
        }
        self.consume(&TokenKind::Indent, "Expected indentation for block")?;

        let mut statements = Vec::new();
        while !self.check(&TokenKind::Dedent) && !self.check(&TokenKind::Eof) {
            statements.push(self.parse_statement_or_declaration()?);
            // Skip optional newlines within the block
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
        }

        self.consume(&TokenKind::Dedent, "Expected dedentation to end block")?;

        Ok(AstNode::Block(statements))
    }

    // --- Parsing Functions ---

    // Parses a full program (sequence of statements/declarations)
    fn parse_program(&mut self) -> CompilerResult<AstNode> {
        // --- Skip leading newlines ---
        while self.check(&TokenKind::Newline) {
            self.advance();
        }
        // ---------------------------
        let mut statements = Vec::new();
        while !self.check(&TokenKind::Eof) && !self.check(&TokenKind::Dedent) { // Stop at EOF or Dedent
            statements.push(self.parse_statement_or_declaration()?);
            // Skip optional newlines between statements
            while self.check(&TokenKind::Newline) {
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
        match &self.current_token_info {
            Some(TokenInfo { kind: TokenKind::Keyword(k), .. }) => match k.as_str() {
                "var" => self.parse_variable_declaration(false), // Not secret by default
                "proc" => self.parse_function_definition(false),
                "main" => self.parse_main_definition(), // special entry syntax
                "type" | "object" | "enum" => self.parse_type_definition(),
                "secret" => self.parse_secret_declaration(),
                "if" => self.parse_if_statement_or_expression(),
                "while" => self.parse_while_loop(),
                "for" => self.parse_for_loop(),
                "return" => self.parse_return_statement(),
                "discard" => self.parse_discard_statement(),
                // Add other statement keywords (break, continue, yield, import, etc.)
                _ => self.parse_expression_statement(), // Assume expression if keyword doesn't start a known statement/decl
            },
            // Special-case legacy 'let' at statement start to give a helpful error
            Some(TokenInfo { kind: TokenKind::Identifier(id), location }) if id == "let" => {
                Err(CompilerError::syntax_error("The 'let' keyword is no longer supported", location.clone())
                    .with_hint("Use 'var' for variable declarations (e.g., 'var x = ...')"))
            }
            Some(TokenInfo { kind: TokenKind::Identifier(_), .. }) => self.parse_expression_statement(),
            // Add cases for other statement starters
            _ => {
                let (found_str, location) = match self.current_token_info {
                    Some(token) => (format!("{:?}", token), token.location.clone()),
                    None => ("end of file".to_string(), self.last_location.clone()),
                };

                Err(CompilerError::syntax_error(format!("Unexpected token at start of statement/declaration: {}", found_str), location))
            }
        }
    }

    // Handles declarations starting with 'secret'
    fn parse_secret_declaration(&mut self) -> CompilerResult<AstNode> {
        self.consume_keyword("secret", "Expected 'secret'")?;
        // Check what follows 'secret'
        match &self.current_token_info {
            Some(TokenInfo { kind: TokenKind::Keyword(k), .. }) => match k.as_str() {
                "proc" => self.parse_function_definition(true), // Pass is_secret=true
                "var" => self.parse_variable_declaration(true), // Pass is_secret=true
                "type" | "object" | "enum" => self.parse_type_definition_impl(true), // Pass is_secret=true
                _ => Err(CompilerError::syntax_error(format!("Unexpected keyword '{}' after 'secret'", k), self.get_location())),
            },
            // Explicitly catch 'secret let'
            Some(TokenInfo { kind: TokenKind::Identifier(id), location }) if id == "let" => {
                Err(CompilerError::syntax_error("The 'secret let' form is no longer supported", location.clone())
                    .with_hint("Use 'secret var' instead"))
            }
            _ => Err(CompilerError::syntax_error("Expected 'proc', 'var', 'type', 'object', or 'enum' after 'secret'", self.get_location())),
        }
    }

    fn parse_function_definition(&mut self, is_secret: bool) -> CompilerResult<AstNode> {
        let node_id = self.next_node_id(); // Get a unique ID for this function node
        let start_location = self.get_location(); // Location of 'proc'
        self.consume_keyword("proc", "Expected 'proc'")?; // Consume 'proc'
        let name_token = self.consume(&TokenKind::Identifier("".to_string()), "Expected function name")?;
        let name = match name_token {
            TokenInfo { kind: TokenKind::Identifier(n), .. } => n.clone(),
            _ => unreachable!(), // consume ensures it's an identifier
        };

        self.consume(&TokenKind::LParen, "Expected '(' after function name")?;
        let mut parameters = Vec::new();
        if !self.check(&TokenKind::RParen) {
            loop {
                let param_name_token = self.consume(&TokenKind::Identifier("".to_string()), "Expected parameter name")?;
                let param_name = match param_name_token {
                    TokenInfo { kind: TokenKind::Identifier(n), .. } => n.clone(),
                    _ => unreachable!(), // consume ensures it's an identifier
                };

                // Parse optional type annotation
                let param_type_annotation = if self.check(&TokenKind::Colon) {
                    self.advance(); // Consume ':'
                    Some(Box::new(self.parse_type_annotation()?))
                } else { None };
                parameters.push(Parameter { name: param_name, type_annotation: param_type_annotation, default_value: None, is_secret: false });

                if self.check(&TokenKind::RParen) {
                    break;
                }
                self.consume(&TokenKind::Comma, "Expected ',' between parameters")?;
            }
        }
        self.consume(&TokenKind::RParen, "Expected ')' after parameters")?;

        // New syntax: optional '-> <type-or-nil>' before pragmas, then ':' to start body/header end
        let mut return_type: Option<Box<AstNode>> = None;
        if self.check(&TokenKind::Arrow) {
            self.advance(); // consume '->'
            // Special-case: allow 'nil' to mean no return (void)
            if matches!(self.current_token_info, Some(TokenInfo { kind: TokenKind::NilLiteral, .. })) {
                // Treat as no return type
                self.advance(); // consume 'nil'
                return_type = None;
            } else {
                return_type = Some(Box::new(self.parse_type_annotation()?));
            }
        }

        // Parse optional pragmas (AFTER return arrow, BEFORE ':')
        let mut pragmas = Vec::new();
        if self.check(&TokenKind::LPragma) {
            pragmas = self.parse_pragma()?;
        }

        // Expect ':' to end the header line
        self.consume(&TokenKind::Colon, "Expected ':' after function header")?;

        // For builtins, accept no body (empty block)
        let is_builtin = pragmas.iter().any(|p| matches!(p, Pragma::Simple(n, _) if n == "builtin"));
        let body = if is_builtin {
            // Allow just a header line and no body for builtins
            AstNode::Block(vec![])
        } else {
            // Parse function body after newline and indent
            self.parse_indented_block()?
        };

        Ok(AstNode::FunctionDefinition {
            name: Some(name),
            parameters,
            return_type,
            body: Box::new(body),
            is_secret, // Pass the flag indicating if 'secret proc' was used
            pragmas, // Store parsed pragmas
            location: start_location, // Use location of 'proc' keyword
            node_id, // Store the unique ID
        })
    }

    // Parse the special 'main' entry function definition.
    // New syntax:
    //   main <method_name>(<params>) [-> <type-or-nil>] [{. pragmas .}]:
    //     <body>
    fn parse_main_definition(&mut self) -> CompilerResult<AstNode> {
        let node_id = self.next_node_id();
        let start_location = self.get_location(); // location of 'main'
        self.consume_keyword("main", "Expected 'main'")?; // consume 'main'
        // function name after 'main'
        // Accept either Identifier or the keyword 'main' explicitly (to support `main main()`).
        let func_name = match self.current_token_info {
            Some(TokenInfo { kind: TokenKind::Identifier(ref n), .. }) => {
                let n = n.clone();
                self.advance();
                n
            }
            Some(TokenInfo { kind: TokenKind::Keyword(ref k), .. }) if k == "main" => {
                // Treat keyword(main) as the identifier "main" in this specific slot
                self.advance();
                "main".to_string()
            }
            Some(token) => {
                return Err(CompilerError::syntax_error(
                    "Expected function name after 'main'",
                    token.location.clone(),
                ).with_hint("Try adding identifier here"));
            }
            None => return Err(CompilerError::syntax_error("Expected function name after 'main'", self.last_location.clone())),
        };

        // Parameters
        self.consume(&TokenKind::LParen, "Expected '(' after entry function name")?;
        let mut parameters = Vec::new();
        if !self.check(&TokenKind::RParen) {
            loop {
                let param_name_token = self.consume(&TokenKind::Identifier("".to_string()), "Expected parameter name")?;
                let param_name = match param_name_token {
                    TokenInfo { kind: TokenKind::Identifier(n), .. } => n.clone(),
                    _ => unreachable!(),
                };
                let param_type_annotation = if self.check(&TokenKind::Colon) {
                    self.advance();
                    Some(Box::new(self.parse_type_annotation()?))
                } else { None };
                parameters.push(Parameter {
                    name: param_name,
                    type_annotation: param_type_annotation,
                    default_value: None,
                    is_secret: false,
                });
                if self.check(&TokenKind::RParen) { break; }
                self.consume(&TokenKind::Comma, "Expected ',' between parameters")?;
            }
        }
        self.consume(&TokenKind::RParen, "Expected ')' after parameters")?;

        // Optional return type arrow
        let mut return_type: Option<Box<AstNode>> = None;
        if self.check(&TokenKind::Arrow) {
            self.advance(); // '->'
            if matches!(self.current_token_info, Some(TokenInfo { kind: TokenKind::NilLiteral, .. })) {
                self.advance(); // consume 'nil' => treat as no return type (void)
                return_type = None;
            } else {
                return_type = Some(Box::new(self.parse_type_annotation()?));
            }
        }

        // Optional pragmas
        let mut pragmas = Vec::new();
        if self.check(&TokenKind::LPragma) {
            pragmas = self.parse_pragma()?;
        }

        // Body
        self.consume(&TokenKind::Colon, "Expected ':' after entry function header")?;
        let body = self.parse_indented_block()?;

        // Represent as a normal FunctionDefinition with the provided name.
        // Codegen/semantics will treat this as the program entry.
        let mut pragmas = pragmas;
        // Inject an internal marker so codegen can recognize explicit entry uniformly.
        // We piggyback on pragmas with a synthetic {.entry.} added here.
        pragmas.push(Pragma::Simple("entry".to_string(), start_location.clone()));

        Ok(AstNode::FunctionDefinition {
            name: Some(func_name),
            parameters,
            return_type,
            body: Box::new(body),
            is_secret: false, // 'main' cannot be prefixed with 'secret'
            pragmas,
            location: start_location,
            node_id,
        })
    }

    fn parse_type_definition(&mut self) -> CompilerResult<AstNode> {
        self.parse_type_definition_impl(false) // Not secret by default
    }

    fn parse_type_definition_impl(&mut self, is_secret: bool) -> CompilerResult<AstNode> {
        let location = self.get_location();
        // Determine if it's object, enum, or type alias
        if self.check_keyword("object") {
            self.advance(); // Consume 'object'
            // TODO: Parse object definition
            Err(CompilerError::syntax_error("Object definition parsing not implemented", location))
        } else if self.check_keyword("enum") {
            self.advance(); // Consume 'enum'
            // TODO: Parse enum definition
            Err(CompilerError::syntax_error("Enum definition parsing not implemented", location))
        } else if self.check_keyword("type") {
            self.advance(); // Consume 'type'
            // TODO: Parse type alias
            Err(CompilerError::syntax_error("Type alias parsing not implemented", location))
        } else {
            Err(CompilerError::syntax_error("Expected 'object', 'enum', or 'type' for type definition", location))
        }
    }

    fn parse_if_statement_or_expression(&mut self) -> CompilerResult<AstNode> {
        let start_location = self.get_location(); // Location of 'if'
        self.consume_keyword("if", "Expected 'if'")?;
        let condition = self.parse_expression()?;
        self.consume(&TokenKind::Colon, "Expected ':' after if condition")?;
        let then_branch = self.parse_indented_block()?;

        let mut elif_clauses = Vec::new();
        while self.check_keyword("elif") {
            self.advance(); // Consume 'elif'
            let elif_condition = self.parse_expression()?;
            self.consume(&TokenKind::Colon, "Expected ':' after elif condition")?;
            let elif_body = self.parse_indented_block()?;
            elif_clauses.push((elif_condition, elif_body));
        }

        let else_branch = if self.check_keyword("else") {
            self.advance(); // Consume 'else'
            self.consume(&TokenKind::Colon, "Expected ':' after else")?;
            Some(Box::new(self.parse_indented_block()?))
        } else {
            None
        };

        // Construct nested IfExpressions from the right
        let mut final_node = AstNode::IfExpression {
            condition: Box::new(condition),
            then_branch: Box::new(then_branch),
            else_branch, // Initial else branch
        };

        // Fold elif clauses into nested IfExpressions
        for (elif_condition, elif_body) in elif_clauses.into_iter().rev() {
            final_node = AstNode::IfExpression {
                condition: Box::new(elif_condition),
                then_branch: Box::new(elif_body),
                else_branch: Some(Box::new(final_node)),
            };
        }

        Ok(final_node)
    }

    // TODO: Add location to WhileLoop node
    fn parse_while_loop(&mut self) -> CompilerResult<AstNode> {
        let start_location = self.get_location(); // Location of 'while'
        self.consume_keyword("while", "Expected 'while'")?;
        let condition = self.parse_expression()?;
        self.consume(&TokenKind::Colon, "Expected ':' after while condition")?;
        let body = self.parse_indented_block()?;

        Ok(AstNode::WhileLoop {
            condition: Box::new(condition),
            body: Box::new(body),
            location: start_location, // Use location of 'while'
        })
    }

    fn parse_for_loop(&mut self) -> CompilerResult<AstNode> {
        let start_location = self.get_location(); // Location of 'for'
        self.consume_keyword("for", "Expected 'for'")?;

        // Parse one or more identifiers separated by commas
        let mut variables = Vec::new();
        let first_ident = self.consume(&TokenKind::Identifier("".to_string()), "Expected loop variable name")?;
        let first_name = match &first_ident.kind {
            TokenKind::Identifier(n) => n.clone(),
            _ => unreachable!(),
        };
        variables.push(first_name);
        while self.check(&TokenKind::Comma) {
            self.advance(); // consume ','
            let ident_tok = self.consume(&TokenKind::Identifier("".to_string()), "Expected loop variable name after ','")?;
            if let TokenKind::Identifier(n) = &ident_tok.kind {
                variables.push(n.clone());
            }
        }

        // Expect 'in'
        // 'in' is tokenized as a keyword in our lexer
        self.consume_keyword("in", "Expected 'in' in for-loop header")?;

        // Parse iterable expression, but enforce tight range syntax a..b for for-loops
        let iterable = {
            // Parse left expression
            let left = self.parse_expression_with_precedence(5 /* precedence just below '..' (4) so we stop before parsing '..' */)?;
            // Now we require exactly the '..' operator next, with no whitespace around it.
            // Since our lexer doesn't record end positions, we enforce the rule syntactically:
            // only accept the '..' operator token immediately next; any spaces before/after would have been tokenized as separate tokens already,
            // but to be strict per request, we reject forms like 'a .. b' by requiring that the operator appears right now,
            // and we forbid an intervening Newline.
            match self.current_token_info {
                Some(TokenInfo { kind: TokenKind::Operator(op), location: op_loc }) if op == ".." => {
                    // Ensure no spaces variant in source: best-effort by checking previous token and next token are expressions
                    // and emitting a tailored error if user likely wrote spaces in tests that used 'a .. b'.
                    // Consume '..'
                    self.advance();
                }
                Some(TokenInfo { ref kind, ref location }) => {
                    // If the next token is not '..', but a range was intended, produce a targeted error.
                    return Err(CompilerError::syntax_error(
                        "Expected tight range 'a..b' in for-loop (no spaces around '..')",
                        location.clone(),
                    ).with_hint("Write: for i in a..b:"));
                }
                None => {
                    return Err(CompilerError::syntax_error(
                        "Unexpected end of input while parsing for-loop range; expected '..'",
                        self.last_location.clone(),
                    ).with_hint("Write: for i in a..b:"));
                }
            }
            // After consuming '..', immediately parse the right expression
            let right = self.parse_expression_with_precedence(4)?;
            AstNode::BinaryOperation {
                op: "..".to_string(),
                left: Box::new(left),
                right: Box::new(right),
                location: self.last_location.clone(),
            }
        };

        // Expect ':' then a block
        self.consume(&TokenKind::Colon, "Expected ':' after for-loop header")?;
        let body = self.parse_indented_block()?;

        Ok(AstNode::ForLoop {
            variables,
            iterable: Box::new(iterable),
            body: Box::new(body),
            location: start_location,
        })
    }

    fn parse_return_statement(&mut self) -> CompilerResult<AstNode> {
        let start_location = self.get_location();
        self.consume_keyword("return", "Expected 'return'")?;
        let value = if !self.check(&TokenKind::Newline) && !self.check(&TokenKind::Eof) && !self.check(&TokenKind::Dedent) {
            Some(Box::new(self.parse_expression()?))
        } else {
            None
        };

        Ok(AstNode::Return { value, location: start_location })
    }

    fn parse_discard_statement(&mut self) -> CompilerResult<AstNode> {
        let start_location = self.get_location(); // Location of 'discard'
        self.consume_keyword("discard", "Expected 'discard'")?;
        let expression = self.parse_expression()?;

        // Expect newline, EOF, or Dedent after the statement
        if !self.check(&TokenKind::Newline) && !self.check(&TokenKind::Eof) && !self.check(&TokenKind::Dedent) && !self.check(&TokenKind::RParen) /* Allow in expr lists */ {
            return Err(CompilerError::syntax_error(format!("Expected newline, EOF, or dedent after discard statement, found {:?}", self.current_token_info), self.get_location()));
        }

        Ok(AstNode::DiscardStatement {
            expression: Box::new(expression),
            location: start_location,
        })
    }

    // --- Pratt Parser for Expressions ---

    // Gets the precedence level of the current token (if it's an infix operator).
    fn current_precedence(&self) -> u8 {
        match &self.current_token_info {
            Some(TokenInfo { kind: TokenKind::Operator(op), .. }) => match op.as_str() {
                "or" => 1,
                "and" => 2,
                "==" | "!=" | "<" | "<=" | ">" | ">=" | "is" | "in" => 3, // Comparison operators
                ".." => 4, // Range operator
                "+" | "-" => 5, // Addition/Subtraction
                "*" | "/" | "%" => 6, // Multiplication/Division/Modulo
                // Add other operators like power (**), bitwise (&, |, ^), etc.
                _ => 0, // Not an infix operator or lowest precedence
            },
            // Function call '(' has high precedence
            Some(TokenInfo { kind: TokenKind::LParen, .. }) => 7, // Higher than multiplication/division
            // Field access '.' has even higher precedence
            Some(TokenInfo { kind: TokenKind::Dot, .. }) => 8, // Higher than function calls
            _ => 0, // Not an operator
        }
    }

    // Parses a prefix expression (like literals, identifiers, unary operators).
    fn parse_prefix(&mut self) -> CompilerResult<AstNode> {
        let token_info = self.advance().ok_or_else(|| {
            // Use last_location if current is None
            CompilerError::syntax_error("Unexpected end of file while parsing expression", self.last_location.clone())
        })?;

        match &token_info.kind {
            TokenKind::IntLiteral { value, kind, .. } => Ok(AstNode::Literal(Value::Int { value: *value, kind: kind.clone() })), 
            TokenKind::FloatLiteral(f) => Ok(AstNode::Literal(Value::Float(*f))),
            TokenKind::StringLiteral(s) => Ok(AstNode::Literal(Value::String(s.clone()))),
            TokenKind::BoolLiteral(b) => Ok(AstNode::Literal(Value::Bool(*b))),
            TokenKind::NilLiteral => Ok(AstNode::Literal(Value::Nil)),
            TokenKind::Identifier(name) => Ok(AstNode::Identifier(name.clone(), token_info.location.clone())),
            TokenKind::LParen => {
                let expr = self.parse_expression_with_precedence(0)?; // Parse expression inside parentheses
                self.consume(&TokenKind::RParen, "Expected ')' after parenthesized expression")?;
                Ok(expr)
            }
            TokenKind::Operator(op) => {
                // Handle prefix operators (e.g., '-', 'not')
                match op.as_str() {
                    "-" | "not" => {
                        // Define prefix precedence (usually higher than most infix)
                        let prefix_precedence = 6; // Example precedence for unary minus/not
                        let operand = self.parse_expression_with_precedence(prefix_precedence)?;
                        Ok(AstNode::UnaryOperation {
                            op: op.clone(),
                            operand: Box::new(operand),
                            location: token_info.location.clone(),
                        })
                    }
                    _ => Err(CompilerError::syntax_error(format!("Unexpected prefix operator: {}", op), token_info.location.clone())),
                }
            }
            // TODO: Add function calls, list literals, etc.
            _ => Err(CompilerError::syntax_error(format!("Expected expression, found {:?}", token_info.kind), token_info.location.clone())
                    .with_hint("An expression can be a literal, identifier, function call, or use operators like +, -, *, /")),
        }
    }

    // Parses an infix expression (like `a + b`, `x > 5`).
    fn parse_infix(&mut self, left: AstNode) -> CompilerResult<AstNode> {
        let operator_location = self.get_location(); // Location of the operator/paren/dot
        let token_info = self.current_token_info.ok_or_else(|| {
             CompilerError::syntax_error("Unexpected end of file while parsing infix expression", self.last_location.clone())
        })?;

        match &token_info.kind {
            TokenKind::Operator(op) => {
                let precedence = self.current_precedence();
                self.advance(); // Consume the operator
                let right = self.parse_expression_with_precedence(precedence)?;
                Ok(AstNode::BinaryOperation {
                    op: op.clone(),
                    left: Box::new(left),
                    right: Box::new(right),
                    location: operator_location,
                })
            }
            TokenKind::LParen => {
                // This is a function call: left(arg1, arg2, ...)
                self.advance(); // Consume '('
                let mut arguments = Vec::new();
                if !self.check(&TokenKind::RParen) {
                    loop {
                        arguments.push(self.parse_expression()?);
                        if self.check(&TokenKind::RParen) {
                            break;
                        }
                        self.consume(&TokenKind::Comma, "Expected ',' or ')' after function argument")?;
                    }
                }
                self.consume(&TokenKind::RParen, "Expected ')' after function arguments")?;

                Ok(AstNode::FunctionCall {
                    function: Box::new(left),
                    arguments,
                    location: operator_location, // Location of '('
                    resolved_return_type: None, // Set to None during parsing
                })
            }
            TokenKind::Dot => {
                // This is field access: left.field
                self.advance(); // Consume '.'
                let field_name_token = self.consume(&TokenKind::Identifier("".to_string()), "Expected field name after '.'")?;
                let field_name = match &field_name_token.kind {
                    TokenKind::Identifier(name) => name.clone(),
                    _ => unreachable!(), // consume ensures it's an identifier
                };

                Ok(AstNode::FieldAccess {
                    object: Box::new(left),
                    field_name,
                    location: operator_location, // Location of '.'
                })
            }
            _ => Err(CompilerError::syntax_error(
                format!("Expected infix operator, function call '(', or field access '.', found {:?}", token_info.kind),
                token_info.location.clone())),
        }
    }

    // Main expression parsing function using Pratt parsing logic.
    fn parse_expression_with_precedence(&mut self, min_precedence: u8) -> CompilerResult<AstNode> {
        let mut left = self.parse_prefix()?;

        // The loop condition checks precedence.
        // For function calls, '(' has precedence 7.
        // For field access, '.' has precedence 8.
        // For binary operators, they have precedence 1-6.
        while min_precedence < self.current_precedence() {
            // If the next token is an infix operator, '(', or '.' with higher precedence, parse it.
            left = self.parse_infix(left)?;
        }

        Ok(left)
    }

    // Public entry point for expression parsing.
    fn parse_expression(&mut self) -> CompilerResult<AstNode> {
        self.parse_expression_with_precedence(0)
    }

    // Handles expression statements (e.g., assignments, function calls)
    fn parse_expression_statement(&mut self) -> CompilerResult<AstNode> {
        let start_location = self.get_location();
        let expr = self.parse_expression()?;
        // Could be assignment: expr = value
        if self.check(&TokenKind::Assign) {
            self.advance(); // Consume '='
            let value = self.parse_expression()?;
            // Expect newline, EOF, or Dedent after the statement
             if !self.check(&TokenKind::Newline) && !self.check(&TokenKind::Eof) && !self.check(&TokenKind::Dedent) && !self.check(&TokenKind::RParen) /* Allow in expr lists */ {
                 return Err(CompilerError::syntax_error(format!("Expected newline, EOF, or dedent after assignment, found {:?}", self.current_token_info), self.get_location()));
             }
            Ok(AstNode::Assignment { 
                target: Box::new(expr),
                value: Box::new(value),
                location: start_location, // Use location of the target expression start
            })
        } else {
            // Assume it's just an expression used as a statement (e.g., function call)
            // Expect newline, EOF, or Dedent after the statement
             if !self.check(&TokenKind::Newline) && !self.check(&TokenKind::Eof) && !self.check(&TokenKind::Dedent) && !self.check(&TokenKind::RParen) /* Allow in expr lists */ {
                 return Err(CompilerError::syntax_error(format!("Expected newline, EOF, or dedent after expression statement, found {:?}", self.current_token_info), self.get_location()));
             }
            Ok(expr)
        }
    }

    // Parses type annotations (e.g., int, string, MyObject, list[int], secret int)
    // IMPORTANT: This function *only* parses the type name/structure itself.
    // It handles the optional 'secret' keyword internally.
    fn parse_type_annotation(&mut self) -> CompilerResult<AstNode> {
         let type_location = self.get_location(); // Location of 'secret' or the type identifier
         let mut is_secret = false;
         if self.check_keyword("secret") {
             self.advance(); // Consume 'secret'
             is_secret = true;
         }

         // Now parse the actual type
         match &self.current_token_info {
            Some(TokenInfo { kind: TokenKind::Identifier(name), .. }) => { // TODO: Handle generics like list[int]
                let base_name = name.clone();
                self.advance(); // Consume identifier
                // TODO: Handle qualified names like module.Type
                if is_secret {
                    Ok(AstNode::SecretType(Box::new(AstNode::Identifier(base_name, type_location))))
                } else {
                    Ok(AstNode::Identifier(base_name, type_location))
                }
            }
            // TODO: Add cases for ListType, TupleType, DictType, FunctionType literals
            _ => {
                let (found_str, location) = match self.current_token_info {
                    Some(token) => (format!("{:?}", token), token.location.clone()),
                    None => ("end of file".to_string(), self.last_location.clone()),
                };

                Err(CompilerError::syntax_error(format!("Expected type name identifier after 'secret' (if present), found {}", found_str), location))
            }
        }
    }

    fn parse_variable_declaration(&mut self, is_secret: bool) -> CompilerResult<AstNode> {
        let start_location = self.get_location(); // Location of 'var'
        // Only allow 'var' now. If someone writes 'let', we should have errored earlier,
        // but double-check here defensively.
        if self.check_keyword("var") {
            self.advance(); // Consume 'var'
        } else if matches!(self.current_token_info, Some(TokenInfo { kind: TokenKind::Identifier(id), .. }) if id == "let") {
            let loc = self.get_location();
            return Err(CompilerError::syntax_error("The 'let' keyword is no longer supported", loc)
                .with_hint("Use 'var' for variable declarations"));
        } else {
            // Should not reach here if caller used correct entry points
            return Err(CompilerError::syntax_error("Expected 'var' to start a variable declaration", self.get_location()));
        }
        let is_mutable = true; // With only 'var', declarations are always mutable

        let name_token = self.consume(&TokenKind::Identifier("".to_string()), "Expected variable name")?;
        let name = match name_token {
            TokenInfo { kind: TokenKind::Identifier(n), .. } => n.clone(),
            _ => unreachable!(), // consume ensures it's an identifier
        };

        // Parse optional type annotation
        let type_annotation = if self.check(&TokenKind::Colon) {
            self.advance(); // Consume ':'
            Some(Box::new(self.parse_type_annotation()?))
        } else { None };

        let mut value = None;
        if self.check(&TokenKind::Assign) {
            self.advance(); // Consume '='
            value = Some(Box::new(self.parse_expression()?));
        } else if type_annotation.is_none() {
             let location = self.get_location();
             return Err(CompilerError::syntax_error("Variable declaration needs either a type annotation or an initial value", location)
                 .with_hint("Add a type annotation with ':' or initialize with '='"));
        }

        // Expect newline, EOF, or Dedent after declaration
        if !self.check(&TokenKind::Newline) && !self.check(&TokenKind::Eof) && !self.check(&TokenKind::Dedent) && !self.check(&TokenKind::RParen) /* Allow in expr lists */ {
             return Err(CompilerError::syntax_error(format!("Expected newline, EOF, or dedent after variable declaration, found {:?}", self.current_token_info), self.get_location()));
        }

        Ok(AstNode::VariableDeclaration {
            name,
            type_annotation,
            value,
            is_mutable, // always true now
            is_secret, // Set the flag based on whether 'secret let/var' was used
            location: start_location, // Use location of 'var'
        })
    }

    // Parses a pragma block like {. ident1 . ident2: value .}
    fn parse_pragma(&mut self) -> CompilerResult<Vec<Pragma>> {
        self.consume(&TokenKind::LPragma, "Expected '{.' to start pragma")?;
        let mut pragmas = Vec::new();
        loop {
            if self.check(&TokenKind::RPragma) {
                break;
            }
            // Expect identifier or dot
            if self.check(&TokenKind::Identifier("".to_string())) {
                let token = self.advance().unwrap(); // Safe unwrap
                let pragma_location = token.location.clone();
                if let TokenKind::Identifier(name) = &token.kind {
                    // Check if it's a key-value pragma (followed by ':')
                    if self.check(&TokenKind::Colon) {
                        self.advance(); // Consume ':'
                        let value_node = self.parse_expression()?; // Parse the value expression
                        pragmas.push(Pragma::KeyValue(name.clone(), Box::new(value_node), pragma_location));
                    } else {
                        // Simple identifier pragma
                        pragmas.push(Pragma::Simple(name.clone(), pragma_location));
                    }
                } else {
                    unreachable!(); // Should be identifier based on check
                }
            } else {
                 return Err(CompilerError::syntax_error("Expected identifier for pragma name", self.get_location()));
            }

            // Consume optional separator dot or expect end
            if self.check(&TokenKind::Dot) {
                self.advance(); // Consume '.'
            } else if !self.check(&TokenKind::RPragma) {
                 return Err(CompilerError::syntax_error("Expected '.' separator or '.}' to end pragma", self.get_location()));
            } else {
                // RPragma will be consumed next iteration or at the end
            }
        }
        self.consume(&TokenKind::RPragma, "Expected '.}' to end pragma")?;
        Ok(pragmas)
    }

    // Helper to get current location
    fn get_location(&self) -> SourceLocation {
        self.current_token_info
            .map(|info| info.location.clone())
            .unwrap_or_else(|| self.last_location.clone()) // Use last known location if at EOF
    }
}

pub fn parse(tokens: &[TokenInfo], filename: &str) -> CompilerResult<AstNode> {
    let mut parser = Parser::new(tokens, filename);
    // The top-level parsing function (e.g., parse_program or parse_module)
    let root_node = parser.parse_program()?;

    // Check if all tokens were consumed (except EOF)
    if !parser.check(&TokenKind::Eof) {
        let (found_str, location) = match parser.current_token_info {
            Some(token) => (format!("{:?}", token), token.location.clone()),
            None => ("end of file".to_string(), parser.last_location.clone()),
        };
        
        Err(CompilerError::syntax_error(format!("Unexpected token after parsing finished: {}", found_str), location))
    } else {
        Ok(root_node)
    }
}
