use crate::ast::{AstNode, FieldDefinition, Parameter, Pragma, Value};
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
                "def" => self.parse_function_definition(false),
                "main" => self.parse_main_definition(), // special entry syntax
                "type" | "object" | "enum" => self.parse_type_definition(),
                "secret" => self.parse_secret_declaration(),
                "if" => self.parse_if_statement_or_expression(),
                "while" => self.parse_while_loop(),
                "for" => self.parse_for_loop(),
                "return" => self.parse_return_statement(),
                "discard" => self.parse_discard_statement(),
                "import" => self.parse_import_statement(),
                // Add other statement keywords (break, continue, yield, etc.)
                _ => self.parse_expression_statement(), // Assume expression if keyword doesn't start a known statement/decl
            },
            // Friendly hard error for legacy 'proc' at start of a declaration
            Some(TokenInfo { kind: TokenKind::Identifier(id), location }) if id == "proc" => {
                Err(CompilerError::syntax_error(
                    "The 'proc' keyword is no longer supported; use 'def'",
                    location.clone(),
                ).with_hint("Rewrite: def name(args) -> type:"))
            }
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
                "def" => self.parse_function_definition(true), // Pass is_secret=true
                "var" => self.parse_variable_declaration(true), // Pass is_secret=true
                "type" | "object" | "enum" => self.parse_type_definition_impl(true), // Pass is_secret=true
                _ => Err(CompilerError::syntax_error(format!("Unexpected keyword '{}' after 'secret'", k), self.get_location())),
            },
            // Explicitly catch 'secret proc'
            Some(TokenInfo { kind: TokenKind::Identifier(id), location }) if id == "proc" => {
                Err(CompilerError::syntax_error(
                    "The 'proc' keyword is no longer supported; use 'def'",
                    location.clone(),
                ).with_hint("Rewrite: secret def name(args) -> type:"))
            }
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
        let start_location = self.get_location(); // Location of 'def'
        self.consume_keyword("def", "Expected 'def'")?; // Consume 'def'
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
            let arrow_location = self.current_token_info.map(|t| t.location.clone()).unwrap_or_default();
            self.advance(); // consume '->'

            // Check for tuple return type syntax: -> (Type1, Type2)
            // This is not supported - return types must be a single type
            if self.check(&TokenKind::LParen) {
                return Err(CompilerError::syntax_error(
                    "Tuple return types are not supported",
                    arrow_location
                ).with_hint("Return a single value. If you need multiple values, consider using a custom type or restructuring your code."));
            }

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
            is_secret, // Pass the flag indicating if 'secret def' was used
            pragmas, // Store parsed pragmas
            location: start_location, // Use location of 'def' keyword
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
            let arrow_location = self.current_token_info.map(|t| t.location.clone()).unwrap_or_default();
            self.advance(); // '->'

            // Check for tuple return type syntax: -> (Type1, Type2)
            if self.check(&TokenKind::LParen) {
                return Err(CompilerError::syntax_error(
                    "Tuple return types are not supported",
                    arrow_location
                ).with_hint("Return a single value. If you need multiple values, consider using a custom type or restructuring your code."));
            }

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
            self.parse_object_definition(is_secret, location)
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

    /// Parses an object definition.
    /// Syntax:
    ///   object Name:
    ///     field1: Type1
    ///     field2: Type2
    ///
    /// Or with base type:
    ///   object Name(BaseType):
    ///     field1: Type1
    fn parse_object_definition(&mut self, is_secret: bool, location: SourceLocation) -> CompilerResult<AstNode> {
        // Parse object name
        let name_token = self.consume(&TokenKind::Identifier("".to_string()), "Expected object name after 'object'")?;
        let name = match name_token {
            TokenInfo { kind: TokenKind::Identifier(n), .. } => n.clone(),
            _ => unreachable!(),
        };

        // Parse optional base type: object Name(BaseType):
        let base_type = if self.check(&TokenKind::LParen) {
            self.advance(); // Consume '('
            let base = self.parse_type_annotation()?;
            self.consume(&TokenKind::RParen, "Expected ')' after base type")?;
            Some(Box::new(base))
        } else {
            None
        };

        // Expect ':' to start the body
        self.consume(&TokenKind::Colon, "Expected ':' after object header")?;

        // Parse the indented block of field definitions
        let fields = self.parse_object_fields()?;

        Ok(AstNode::ObjectDefinition {
            name,
            base_type,
            fields,
            is_secret,
            location,
        })
    }

    /// Parses the fields inside an object definition.
    /// Each field is: field_name: Type
    fn parse_object_fields(&mut self) -> CompilerResult<Vec<FieldDefinition>> {
        let mut fields = Vec::new();

        // Consume any newlines before the block
        while self.check(&TokenKind::Newline) {
            self.advance();
        }

        // Expect indent to start the block
        if !self.check(&TokenKind::Indent) {
            return Err(CompilerError::syntax_error(
                "Expected indented block with field definitions after object header",
                self.get_location(),
            ));
        }
        self.advance(); // Consume Indent

        // Parse field definitions until we see Dedent
        loop {
            // Skip any extra newlines
            while self.check(&TokenKind::Newline) {
                self.advance();
            }

            // Check for end of block
            if self.check(&TokenKind::Dedent) || self.check(&TokenKind::Eof) {
                break;
            }

            // Check for 'secret' modifier on field
            let field_is_secret = if self.check_keyword("secret") {
                self.advance();
                true
            } else {
                false
            };

            // Parse field name
            let field_name_token = self.consume(&TokenKind::Identifier("".to_string()), "Expected field name")?;
            let field_name = match field_name_token {
                TokenInfo { kind: TokenKind::Identifier(n), .. } => n.clone(),
                _ => unreachable!(),
            };

            // Expect ':' followed by type annotation
            self.consume(&TokenKind::Colon, "Expected ':' after field name")?;
            let field_type = self.parse_type_annotation()?;

            fields.push(FieldDefinition {
                name: field_name,
                type_annotation: Box::new(field_type),
                is_secret: field_is_secret,
            });

            // Consume newline after field definition
            if self.check(&TokenKind::Newline) {
                self.advance();
            }
        }

        // Consume the Dedent
        if self.check(&TokenKind::Dedent) {
            self.advance();
        }

        if fields.is_empty() {
            return Err(CompilerError::syntax_error(
                "Object definition must have at least one field",
                self.get_location(),
            ));
        }

        Ok(fields)
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

        // Parse iterable expression - supports both range syntax (a..b) and collection iteration
        let iterable = {
            // Parse left expression with precedence just below '..' so we stop before parsing '..'
            let left = self.parse_expression_with_precedence(5)?;

            // Check if next token is '..' for range syntax
            match &self.current_token_info {
                Some(TokenInfo { kind: TokenKind::Operator(op), .. }) if op == ".." => {
                    // This is a range expression - consume '..' and parse right side
                    self.advance();
                    let right = self.parse_expression_with_precedence(4)?;
                    AstNode::BinaryOperation {
                        op: "..".to_string(),
                        left: Box::new(left),
                        right: Box::new(right),
                        location: self.last_location.clone(),
                    }
                }
                _ => {
                    // Not a range - this is a collection/iterable expression
                    // The 'left' expression is our iterable (e.g., a list variable)
                    left
                }
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

    /// Parses an import statement.
    /// Syntax: import module.submodule [as alias]
    /// Example: import utils.math
    /// Example: import utils.math as m
    fn parse_import_statement(&mut self) -> CompilerResult<AstNode> {
        let start_location = self.get_location();
        self.consume_keyword("import", "Expected 'import'")?;

        // Parse module path: identifier.identifier.identifier...
        let mut module_path = Vec::new();
        let first_ident = self.consume(&TokenKind::Identifier("".to_string()), "Expected module name after 'import'")?;
        module_path.push(match &first_ident.kind {
            TokenKind::Identifier(n) => n.clone(),
            _ => unreachable!(),
        });

        // Continue parsing dot-separated identifiers
        while self.check(&TokenKind::Dot) {
            self.advance(); // consume '.'
            let next_ident = self.consume(&TokenKind::Identifier("".to_string()), "Expected module name after '.'")?;
            module_path.push(match &next_ident.kind {
                TokenKind::Identifier(n) => n.clone(),
                _ => unreachable!(),
            });
        }

        // Optional alias: "as <identifier>"
        let alias = if self.check_keyword("as") {
            self.advance(); // consume 'as'
            let alias_token = self.consume(&TokenKind::Identifier("".to_string()), "Expected alias name after 'as'")?;
            Some(match &alias_token.kind {
                TokenKind::Identifier(n) => n.clone(),
                _ => unreachable!(),
            })
        } else {
            None
        };

        // Expect newline, EOF, or Dedent after import statement
        if !self.check(&TokenKind::Newline) && !self.check(&TokenKind::Eof) && !self.check(&TokenKind::Dedent) {
            return Err(CompilerError::syntax_error(
                format!("Expected newline after import statement, found {:?}", self.current_token_info),
                self.get_location(),
            ));
        }

        Ok(AstNode::Import {
            module_path,
            alias,
            imported_items: None, // For future "from X import Y" syntax
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
            // Index access '[' has same precedence as field access
            Some(TokenInfo { kind: TokenKind::LBracket, .. }) => 8, // Same as field access
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
            TokenKind::LBracket => {
                // List literal: [elem1, elem2, ...] or empty list []
                let mut elements = Vec::new();
                if !self.check(&TokenKind::RBracket) {
                    loop {
                        elements.push(self.parse_expression()?);
                        if self.check(&TokenKind::RBracket) {
                            break;
                        }
                        self.consume(&TokenKind::Comma, "Expected ',' or ']' after list element")?;
                    }
                }
                self.consume(&TokenKind::RBracket, "Expected ']' after list elements")?;

                // Empty list literals [] are now supported
                // Type will be inferred from context or explicit annotation
                Ok(AstNode::ListLiteral(elements))
            }
            TokenKind::LBrace => {
                // Dict literal: {key1: val1, key2: val2, ...}
                let mut pairs = Vec::new();
                if !self.check(&TokenKind::RBrace) {
                    loop {
                        let key = self.parse_expression()?;
                        self.consume(&TokenKind::Colon, "Expected ':' between dict key and value")?;
                        let value = self.parse_expression()?;
                        pairs.push((key, value));
                        if self.check(&TokenKind::RBrace) {
                            break;
                        }
                        self.consume(&TokenKind::Comma, "Expected ',' or '}' after dict entry")?;
                    }
                }
                self.consume(&TokenKind::RBrace, "Expected '}' after dict entries")?;
                Ok(AstNode::DictLiteral(pairs))
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
            TokenKind::LBracket => {
                // This is index access: left[index]
                self.advance(); // Consume '['
                let index = self.parse_expression()?;
                self.consume(&TokenKind::RBracket, "Expected ']' after index")?;

                Ok(AstNode::IndexAccess {
                    base: Box::new(left),
                    index: Box::new(index),
                    location: operator_location, // Location of '['
                })
            }
            _ => Err(CompilerError::syntax_error(
                format!("Expected infix operator, function call '(', field access '.', or index access '[', found {:?}", token_info.kind),
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

        // Check for tuple unpacking pattern: a, b = expr
        // This is not supported in Stoffel-Lang
        if self.check(&TokenKind::Comma) {
            // Look ahead to see if this could be tuple unpacking
            // Pattern: identifier, identifier... = expr
            if matches!(expr, AstNode::Identifier(..)) {
                return Err(CompilerError::syntax_error(
                    "Tuple unpacking is not supported",
                    start_location
                ).with_hint("Assign to a single variable instead of multiple comma-separated variables"));
            }
        }

        // Check for compound assignment operators: +=, -=, *=, /=, %=
        // These are desugared into: x = x op value
        if let Some(TokenInfo { kind: TokenKind::Operator(op), location: op_location }) = self.current_token_info {
            if let Some(base_op) = match op.as_str() {
                "+=" => Some("+"),
                "-=" => Some("-"),
                "*=" => Some("*"),
                "/=" => Some("/"),
                "%=" => Some("%"),
                _ => None,
            } {
                let op_location = op_location.clone();
                self.advance(); // Consume the compound operator
                let rhs = self.parse_expression()?;

                // Expect newline, EOF, or Dedent after the statement
                if !self.check(&TokenKind::Newline) && !self.check(&TokenKind::Eof) && !self.check(&TokenKind::Dedent) && !self.check(&TokenKind::RParen) {
                    return Err(CompilerError::syntax_error(format!("Expected newline, EOF, or dedent after compound assignment, found {:?}", self.current_token_info), self.get_location()));
                }

                // Desugar: x += y  =>  x = x + y
                let binary_op = AstNode::BinaryOperation {
                    op: base_op.to_string(),
                    left: Box::new(expr.clone()),
                    right: Box::new(rhs),
                    location: op_location,
                };

                return Ok(AstNode::Assignment {
                    target: Box::new(expr),
                    value: Box::new(binary_op),
                    location: start_location,
                });
            }
        }

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

    // Parses type annotations (e.g., int, string, MyObject, List[int], secret int)
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
         let base_type = match &self.current_token_info {
            Some(TokenInfo { kind: TokenKind::Identifier(name), .. }) => {
                let base_name = name.clone();
                self.advance(); // Consume identifier

                // Check for generic type parameters: List[int], Dict[string, int]
                if self.check(&TokenKind::LBracket) {
                    self.advance(); // Consume '['

                    match base_name.as_str() {
                        "List" => {
                            let element_type = self.parse_type_annotation()?;
                            self.consume(&TokenKind::RBracket, "Expected ']' after List element type")?;
                            AstNode::ListType(Box::new(element_type))
                        }
                        "Dict" => {
                            let key_type = self.parse_type_annotation()?;
                            self.consume(&TokenKind::Comma, "Expected ',' between Dict key and value types")?;
                            let value_type = self.parse_type_annotation()?;
                            self.consume(&TokenKind::RBracket, "Expected ']' after Dict value type")?;
                            AstNode::DictType {
                                key_type: Box::new(key_type),
                                value_type: Box::new(value_type),
                                location: type_location.clone(),
                            }
                        }
                        _ => {
                            // Check if this is a capitalization error for List/Dict
                            if base_name == "list" {
                                return Err(CompilerError::syntax_error(
                                    format!("Unknown generic type: {}", base_name),
                                    type_location,
                                ).with_hint("Did you mean 'List'? Generic types use PascalCase"));
                            } else if base_name == "dict" {
                                return Err(CompilerError::syntax_error(
                                    format!("Unknown generic type: {}", base_name),
                                    type_location,
                                ).with_hint("Did you mean 'Dict'? Generic types use PascalCase"));
                            }

                            // General generic type: Name[T1, T2, ...]
                            let mut type_params = Vec::new();
                            loop {
                                type_params.push(self.parse_type_annotation()?);
                                if self.check(&TokenKind::RBracket) {
                                    break;
                                }
                                self.consume(&TokenKind::Comma, "Expected ',' between type parameters")?;
                            }
                            self.consume(&TokenKind::RBracket, "Expected ']' after type parameters")?;
                            AstNode::GenericType {
                                base_name,
                                type_params,
                                location: type_location.clone(),
                            }
                        }
                    }
                } else {
                    // Simple type identifier
                    AstNode::Identifier(base_name, type_location.clone())
                }
            }
            _ => {
                let (found_str, location) = match self.current_token_info {
                    Some(token) => (format!("{:?}", token), token.location.clone()),
                    None => ("end of file".to_string(), self.last_location.clone()),
                };

                return Err(CompilerError::syntax_error(format!("Expected type name identifier after 'secret' (if present), found {}", found_str), location));
            }
        };

        // Wrap in SecretType if needed
        if is_secret {
            Ok(AstNode::SecretType(Box::new(base_type)))
        } else {
            Ok(base_type)
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
