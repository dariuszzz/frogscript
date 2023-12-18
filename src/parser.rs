use std::{collections::HashMap, sync::WaitTimeoutResult};

use crate::lexer::{Token, TokenKind, Literal, Identifier};
use crate::ast::*;

#[derive(Debug, Clone, Default)]
pub struct Program {
    pub modules: Vec<Module>
}

pub struct Parser {
    pub tokens: Vec<Token>,
    pub program: Program,
    pub current: usize,
    pub expr_start: usize,
}

impl Parser {
    pub fn new(tokens: Vec<Token>) -> Self {
        Self {
            tokens,
            program: Program::default(),
            current: 0,
            expr_start: 0
        }
    }
    
    fn is_at_end(&self) -> bool {
        self.current >= self.tokens.len()
    }

    fn advance(&mut self) -> Token {
        match self.peek(0) {
            t => {
                self.current += 1;
                t
            },
        }
    }

    fn peek(&mut self, n: usize) -> Token {
        if self.is_at_end() { return Token { kind: TokenKind::EOF, start_char: 0, start_line: 0, lexeme: String::new() } }
        return self.tokens
            .get(self.current + n)
            .map_or(
                Token { kind: TokenKind::EOF, start_char: 0, start_line: 0, lexeme: String::new() },
                |t| t.clone()
            )
    }

    fn match_token(&mut self, expected: Token) -> bool {
        if self.is_at_end() { return false }
        if self.tokens.get(self.current + 1).unwrap().clone() != expected {
            return false
        }

        self.current += 1;
        return true
    }

    // fn collect_until<F>(&mut self, until: F) -> Result<Vec<Token>, String> 
    // where F: Fn(Token) -> bool 
    // {
    //     let mut tokens = Vec::new();
    //     while let Some(t) = self.peek(0) {
    //         if until(t) { break }
    //         tokens.push(self.advance());
    //     }

    //     if self.is_at_end() {
    //         return Err("Token not found".to_owned());
    //     }

    //     return Ok(tokens)
    // }
    
    fn collect_pattern(&mut self, pattern: &[(TokenKind, bool)]) -> Result<Vec<Token>, String> {

        let mut tokens = Vec::new();

        for (token_kind, opt) in pattern {
            match self.peek(0) {
                Token { kind, .. } if kind == *token_kind => tokens.push(self.advance()),
                Token { kind, .. } if !opt => return Err(format!("Token {token_kind:?} missing, found: {kind:?}").to_owned()),
                _ if !opt => return Err(format!("Token {token_kind:?} not found.").to_owned()),
                _ => {}
            }
        }

        Ok(tokens)
    }

    fn safe_collect_pattern(&mut self, pattern: &[(bool, &str, TokenKind)]) -> Option<HashMap<String, Token>> {

        let mut tokens = HashMap::new();
        let starting_pos = self.current;

        for (opt, key, token_kind) in pattern {  
            match (self.peek(0), token_kind) {
                (Token { kind: TokenKind::Identifier(Identifier::Custom(_)), .. }, TokenKind::Identifier(Identifier::_MatchAnyCustom)) => { tokens.insert(key.to_string(), self.advance()); }
                (Token { kind, .. }, _) if kind == *token_kind => { tokens.insert(key.to_string(), self.advance()); } 
                _ if !opt => {
                    // roll back
                    self.current = starting_pos;
                    return None;
                }
                // didnt match but also was optional so who cares
                _ => {}
            }
        }


        Some(tokens)
    }

    fn parse_fn_no_args(&mut self, module: &mut Module, args: Vec<FunctionArgument>) -> Result<(), String> {

        let mut function_def = FunctionDef {
            export: false,
            func_name: String::new(),
            argument_list: args,
            return_type: Type { type_kind: TypeKind::Infer, is_reference: false },
            function_body: CodeBlock::default()
        };

        if let Some(fn_decl_tokens) = self.safe_collect_pattern(
            &[
                (true,  "ident_1",  TokenKind::Indentation(0)),
                (true,  "export",   TokenKind::Identifier(Identifier::Export)),
                (false, "fn_key",   TokenKind::Identifier(Identifier::Fn)),
                (false, "func_name",TokenKind::Identifier(Identifier::_MatchAnyCustom)),
                (true,  "colon",    TokenKind::Colon),
                (true,  "ret_type", TokenKind::Identifier(Identifier::_MatchAnyCustom)),
                (false, "arrow",    TokenKind::FatArrow)
            ]
        ) {
            if let Some(_) = fn_decl_tokens.get("export") {
                function_def.export = true;
            }

            let name_token = fn_decl_tokens.get("func_name").unwrap().clone();
            match name_token.kind {
                TokenKind::Identifier(Identifier::Custom(name)) => function_def.func_name = name,
                _ => unreachable!()
            };

            match (fn_decl_tokens.get("colon"), fn_decl_tokens.get("ret_type")) {
                (Some(_), Some(ret_type_token)) => {
                    let ret_type_token = ret_type_token.clone();
                    match ret_type_token.kind {
                        TokenKind::Identifier(Identifier::Custom(type_name)) => { 
                            match type_name.as_str() {
                                "bool" => function_def.return_type.type_kind = TypeKind::Boolean,
                                "string" => function_def.return_type.type_kind = TypeKind::String,
                                "float" => function_def.return_type.type_kind = TypeKind::Float,
                                "int" => function_def.return_type.type_kind = TypeKind::Int,
                                "uint" => function_def.return_type.type_kind = TypeKind::Uint,
                                "void" => function_def.return_type.type_kind = TypeKind::Void,
                                _ => function_def.return_type.type_kind = TypeKind::Custom(type_name) 
                            }
                        }
                        _ => unreachable!()
                    }
                }
                (None, None) => {}
                _ => return Err(format!("Unfinished fn return type"))
            }

        } else {
            return Err("Missing tokens in '(export) fn funcname'".to_owned())
        }

        match self.peek(0) {
            Token { kind: TokenKind::Newline, .. } => {
                //consume nl
                self.advance();

                let block = self.parse_codeblock(0)?;
                function_def.function_body = block;
            },
            _ => {
                let expr = self.parse_codeblock_expression(0)?;
                function_def.function_body.expressions.push(expr);
            }
        }

        module.function_defs.push(function_def);

        Ok(())
    }

    fn parse_fn_with_args(&mut self, module: &mut Module) -> Result<(), String> {
        let mut argument_list = Vec::new();

        while let Some(arg_tokens) = self.safe_collect_pattern(
            &[
                (true, "indent_1",         TokenKind::Indentation(0)),
                (false, "double_colon",     TokenKind::DoubleColon),
                (true,  "implicit",         TokenKind::Identifier(Identifier::Implicit)),
                (false, "var_name",         TokenKind::Identifier(Identifier::_MatchAnyCustom)),
                (false, "colon",            TokenKind::Colon),
                (true,  "reference_mark",   TokenKind::Ampersand),
                (false, "type",             TokenKind::Identifier(Identifier::_MatchAnyCustom)),
                (false, "nl",               TokenKind::Newline),
            ]
        ) {
            let mut arg_def = FunctionArgument {
                arg_name: String::new(),
                arg_type: Type { type_kind: TypeKind::Uint, is_reference: false },
                is_implicit: false,
            };

            let name_token = arg_tokens.get("var_name").unwrap().clone();
            match name_token.kind {
                TokenKind::Identifier(Identifier::Custom(name)) => arg_def.arg_name = name,
                _ => unreachable!(),
            };

            let type_token = arg_tokens.get("type").unwrap().clone();
            match type_token.kind {
                TokenKind::Identifier(Identifier::Custom(type_name)) => { 
                    match type_name.as_str() {
                        "bool" => arg_def.arg_type.type_kind = TypeKind::Boolean,
                        "string" => arg_def.arg_type.type_kind = TypeKind::String,
                        "float" => arg_def.arg_type.type_kind = TypeKind::Float,
                        "int" => arg_def.arg_type.type_kind = TypeKind::Int,
                        "uint" => arg_def.arg_type.type_kind = TypeKind::Uint,
                        "void" => arg_def.arg_type.type_kind = TypeKind::Void,
                        _ => arg_def.arg_type.type_kind = TypeKind::Custom(type_name) 
                    }
                }
                _ => unreachable!()
            };

            if let Some(_) = arg_tokens.get("reference_mark") {
                arg_def.arg_type.is_reference = true;
            }

            if let Some(_) = arg_tokens.get("implicit") {
                arg_def.is_implicit = true;
            }

            argument_list.push(arg_def);
        }

        self.parse_fn_no_args(module, argument_list)
    }

    pub fn parse_variable_decl(&mut self, indent: usize) -> Result<Expression, String> {
        let mut is_mutable = true;

        if let Token { kind: TokenKind::Identifier(Identifier::Let), .. } = self.advance() {
            is_mutable = false;
        }

        if let Some(variable_decl_tokens) = self.safe_collect_pattern(
            &[
                (true, "indent_1",  TokenKind::Indentation(0)),
                (true, "implicit",  TokenKind::Identifier(Identifier::Implicit)),
                (false, "var_name", TokenKind::Identifier(Identifier::_MatchAnyCustom)),
                (true,  "colon",    TokenKind::Colon),
                (true,  "reference",TokenKind::Ampersand),
                (true,  "var_type", TokenKind::Identifier(Identifier::_MatchAnyCustom)),
                (false,  "eq",      TokenKind::Equal),
            ]
        ) {
            let is_implicit = variable_decl_tokens.get("implicit").is_some();

            let name_token = variable_decl_tokens.get("var_name").unwrap().clone();
            let var_name = match name_token.kind {
                TokenKind::Identifier(Identifier::Custom(name)) => name,
                _ => unreachable!(),
            };

            let mut is_reference = false;
            let mut type_kind = TypeKind::Infer;
            match (variable_decl_tokens.get("colon"), variable_decl_tokens.get("var_type")) {
                (Some(_), Some(type_token)) => {
                    if let Some(_) = variable_decl_tokens.get("reference") {
                        is_reference = true;
                    }

                    match type_token.clone().kind {
                        TokenKind::Identifier(Identifier::Custom(type_name)) => { 
                            match type_name.as_str() {
                                "bool" => type_kind = TypeKind::Boolean,
                                "string" => type_kind = TypeKind::String,
                                "float" => type_kind = TypeKind::Float,
                                "int" => type_kind = TypeKind::Int,
                                "uint" => type_kind = TypeKind::Uint,
                                "void" => type_kind = TypeKind::Void,
                                _ => type_kind = TypeKind::Custom(type_name) 
                            }
                        }
                        _ => unreachable!()
                    };

                }
                (None, None) => {
                    if let Some(_) = variable_decl_tokens.get("reference") {
                        return Err(format!("Unexpected '&' in variable declaration"));
                    }
                }
                _ => {
                    return Err(format!("Invalid variable type annotation"));
                }
            }

            let value = self.parse_expression(indent)?;

            let variable = VariableDecl {
                var_name,
                var_type: Type { type_kind, is_reference },
                var_value: Box::new(value),
                is_mutable,
                is_implicit,
            };

            Ok(Expression::VariableDecl(variable))
        } else {
            return Err(format!("Invalid variable declaration"));
        }
    }

    pub fn parse_method_call(&mut self, called_on: Expression, indent: usize) -> Result<Expression, String> {
        let name = if let Token { kind: TokenKind::Identifier(Identifier::Custom(func_name)), .. } = self.advance() {
            func_name
        } else {
            return Err(format!("no func name found"));
        };

        let mut call = FunctionCall { 
            func_name: name, 
            arguments: vec![called_on]
        };

        if let Token { kind: TokenKind::ParenLeft, .. } = self.advance() {
            loop {
                let Token { kind, .. } = self.peek(0);
                match kind {
                    TokenKind::ParenRight => {
                        self.advance();
                        break;
                    }
                    TokenKind::Comma => {
                        self.advance();
                    }
                    _ => call.arguments.push(self.parse_expression(indent)?)
                }
            }
            
        } else {
            unreachable!()
        }
        
        let expr = Expression::FunctionCall(call);

        match self.peek(0) {
            Token { kind: TokenKind::Dot, .. } => {
                self.advance();
                self.parse_method_call(expr, indent)
            }
            Token { kind: TokenKind::SquareLeft, .. } => {
                self.advance();
                self.parse_array_access(expr, indent)
            }
            _ => Ok(expr),
        }
    }

    pub fn parse_standalone_function_call(&mut self, name: String, indent: usize) -> Result<Expression, String> {
        let mut call = FunctionCall { 
            func_name: name, 
            arguments: Vec::new()
        };

        if let Token { kind: TokenKind::ParenLeft, .. } = self.advance() {
            loop {
                let Token { kind, .. } = self.peek(0);
                match kind {
                    TokenKind::ParenRight => {
                        self.advance();
                        break;
                    }
                    TokenKind::Comma => {
                        self.advance();
                    }
                    _ => call.arguments.push(self.parse_expression(indent)?)
                }
            }
        } else {
            unreachable!()
        }

        let expr = Expression::FunctionCall(call);

        match self.peek(0) {
            Token { kind: TokenKind::Dot, .. } => {
                self.advance();
                self.parse_method_call(expr, indent)
            }
            Token { kind: TokenKind::SquareLeft, .. } => {
                self.advance();
                self.parse_array_access(expr, indent)
            }
            _ => Ok(expr),
        }
    }

    pub fn parse_equality(&mut self, indent: usize) -> Result<Expression, String> {
        let mut lhs = self.parse_ord(indent)?;

        loop {
            let Token { kind, ..  } = self.peek(0);
            let op = match kind {
                TokenKind::NotEqual => BinaryOperation::NotEqual,
                TokenKind::EqualEqual => BinaryOperation::Equal,
                _ => break,
            };

            // consume != or ==
            self.advance();
            
            let rhs = self.parse_ord(indent)?;
            
            lhs = Expression::BinaryOp(BinaryOp { op, lhs: Box::new(lhs), rhs: Box::new(rhs) });
        }

        Ok(lhs)
    }

    pub fn parse_ord(&mut self, indent: usize) -> Result<Expression, String> {
        let mut lhs = self.parse_range(indent)?;

        let Token { kind, ..  } = self.peek(0);
        let op = match kind {
            TokenKind::AngleLeft => BinaryOperation::Less,
            TokenKind::AngleRight => BinaryOperation::Greater,
            TokenKind::LessEqual => BinaryOperation::LessEqual,
            TokenKind::GreaterEqual => BinaryOperation::GreaterEqual,
            _ => return Ok(lhs),
        };

        // consume > or < or >= or <=
        self.advance();
        
        let rhs = self.parse_range(indent)?;
        
        lhs = Expression::BinaryOp(BinaryOp { op, lhs: Box::new(lhs), rhs: Box::new(rhs) });

        Ok(lhs)
    }

    pub fn parse_range(&mut self, indent: usize) -> Result<Expression, String> {
        let mut lhs = self.parse_sum(indent)?;

        loop {
            let Token { kind, ..  } = self.peek(0);
            let inclusive = match kind {
                TokenKind::DoubleDot => false,
                TokenKind::DoubleDotEqual => true,
                _ => break,
            };

            // consume .. or ..=
            self.advance();
            
            let rhs = self.parse_sum(indent)?;
            
            lhs = Expression::StructLiteral(StructLiteral { 
                name: "Range".to_owned(), 
                fields: HashMap::from([
                    ("start".to_owned(), lhs),
                    ("end".to_owned(), rhs),
                    ("step".to_owned(), Expression::Literal(Literal::Int(1))),
                    ("inclusive".to_owned(), Expression::Literal(Literal::Boolean(inclusive)))
                ]) 
            });
        }

        Ok(lhs)
    }

    pub fn parse_sum(&mut self, indent: usize) -> Result<Expression, String> {
        let mut lhs = self.parse_product(indent)?;

        loop {
            let Token { kind, ..  } = self.peek(0);
            let op = match kind {
                TokenKind::Plus => BinaryOperation::Add,
                TokenKind::Minus => BinaryOperation::Subtract,
                _ => break,
            };

            // consume + or -
            self.advance();
            
            let rhs = self.parse_product(indent)?;
            
            lhs = Expression::BinaryOp(BinaryOp { op, lhs: Box::new(lhs), rhs: Box::new(rhs) });
        }

        Ok(lhs)
    }

    pub fn parse_product(&mut self, indent: usize) -> Result<Expression, String> {
        let mut lhs = self.parse_term(indent)?;

        loop {
            let Token { kind, ..  } = self.peek(0);
            let op = match kind {
                TokenKind::Star => BinaryOperation::Multiply,
                TokenKind::Slash => BinaryOperation::Divide,
                _ => break,
            };

            // consume * or / 
            self.advance();
            
            let rhs = self.parse_term(indent)?;
            
            lhs = Expression::BinaryOp(BinaryOp { op, lhs: Box::new(lhs), rhs: Box::new(rhs) });
        }

        Ok(lhs)
    }

    pub fn parse_term(&mut self, indent: usize) -> Result<Expression, String> {
        match self.advance() {
            Token { start_char, start_line, kind, .. } => {
                match kind {
                    TokenKind::Literal(literal) => self.parse_num(literal, indent),
                    TokenKind::ParenLeft => self.parse_expr_in_parentheses(indent),
                    TokenKind::Identifier(Identifier::Custom(name)) => self.parse_custom_iden(name, indent),
                    TokenKind::SquareLeft => self.parse_array_literal(indent),
                    kind => {
                        dbg!(format!("[{:?}:{:?}] unexpected token {:?}", start_line, start_char, kind));
                        todo!("This is either invalid or unimplemented")
                    }
                }
            }
        }
    }

    pub fn parse_array_literal(&mut self, indent: usize) -> Result<Expression, String> {
        let mut array = ArrayLiteral {
            elements: Vec::new()
        };

        loop {
            let elem = self.parse_expression(indent)?;
            
            let elem = match self.peek(0) {
                Token { kind: TokenKind::Dot, .. } => {
                    self.advance();
                    self.parse_method_call(elem, indent)?
                }
                Token { kind: TokenKind::SquareLeft, .. } => {
                    self.advance();
                    self.parse_array_access(elem, indent)?
                }
                _ => elem,
            };
            
            array.elements.push(elem);

            match self.peek(0).kind {
                TokenKind::Comma => self.advance(),
                TokenKind::SquareRight => {
                    self.advance();
                    break
                },
                _ => return Err(format!("Unexpected token in array literal instead of ','")),
            };
        }

        Ok(Expression::ArrayLiteral(array))
    }

    pub fn parse_expr_in_parentheses(&mut self, indent: usize) -> Result<Expression, String> {

        let expr = self.parse_expression(indent)?;

        if let Token { kind: TokenKind::ParenRight, .. } = self.advance() {
        } else {
            return Err(format!("Unclosed parentheses"))
        }

        match self.peek(0) {
            Token { kind: TokenKind::Dot, .. } => {
                self.advance();
                self.parse_method_call(expr, indent)
            }
            Token { kind: TokenKind::SquareLeft, .. } => {
                self.advance();
                self.parse_array_access(expr, indent)
            }
            _ => Ok(expr),
        }
    }

    pub fn parse_num(&mut self, literal: Literal, indent: usize) -> Result<Expression, String> {
        let expr = Expression::Literal(literal);

        match self.peek(0) {
            Token { kind: TokenKind::Dot, .. } => {
                self.advance();
                self.parse_method_call(expr, indent)
            }
            Token { kind: TokenKind::SquareLeft, .. } => {
                self.advance();
                self.parse_array_access(expr, indent)
            }
            _ => Ok(expr),
        }
    }

    pub fn parse_array_access(&mut self, lhs: Expression, indent: usize) -> Result<Expression, String> {
        let index = self.parse_expression(indent)?;

        let expr = if let TokenKind::SquareRight = self.advance().kind {
            Expression::ArrayAccess(ArrayAccess { 
                expr: Box::new(lhs),
                index: Box::new(index)
            })
        } else {
            return Err(format!("Array access operator not closed"))
        };

        match self.peek(0) {
            Token { kind: TokenKind::Dot, .. } => {
                self.advance();
                self.parse_method_call(expr, indent)
            }
            Token { kind: TokenKind::SquareLeft, .. } => {
                self.advance();
                self.parse_array_access(expr, indent)
            }
            _ => Ok(expr),
        }
    }

    pub fn parse_variable(&mut self, var_name: String, indent: usize) -> Result<Expression, String> {
        let expr = Expression::Variable(Variable { name: var_name });

        match self.peek(0) {
            Token { kind: TokenKind::Dot, .. } => {
                self.advance();
                self.parse_method_call(expr, indent)
            }
            Token { kind: TokenKind::SquareLeft, .. } => {
                self.advance();
                self.parse_array_access(expr, indent)
            }
            _ => Ok(expr),
        }
    }

    pub fn parse_custom_iden(&mut self, identifier: String, indent: usize) -> Result<Expression, String> {
        match self.peek(0) {
            Token { kind: TokenKind::ParenLeft, .. } => self.parse_standalone_function_call(identifier, indent),
            _ => self.parse_variable(identifier, indent),
        }
    }

    pub fn parse_for(&mut self, indent: usize) -> Result<Expression, String> {

        if let Some(tokens) = self.safe_collect_pattern(&[
            (false, "for", TokenKind::Identifier(Identifier::For)),
            (false, "binding", TokenKind::Identifier(Identifier::_MatchAnyCustom)),
            (false, "in", TokenKind::Identifier(Identifier::In))
        ]) {
            let binding = if let TokenKind::Identifier(Identifier::Custom(binding_name)) = tokens.get("binding").unwrap().clone().kind {
                binding_name
            } else {
                unreachable!()
            };

            let iterator = self.parse_range(indent)?;

            match self.advance().kind {
                TokenKind::FatArrow => {}
                kind => return Err(format!("missing '=>' after for expression, found {kind:?}"))
            }

            let body = match self.peek(0).kind {
                TokenKind::Newline => {
                    self.advance();
                    self.parse_codeblock(indent)?
                }
                _ => {
                    let expr = self.parse_codeblock_expression(indent)?;

                    if TokenKind::Newline == self.peek(0).kind {
                        self.advance();
                    }

                    CodeBlock {
                        indentation: indent,
                        expressions: vec![expr]
                    }
                }
            };

            Ok(Expression::For(For {
                binding,
                iterator: Box::new(iterator),
                body
            }))
        } else {
            return Err(format!("Invalid for loop construction"))
        }
    }

    pub fn parse_if(&mut self, indent: usize) -> Result<Expression, String> {
        // consume if
        self.advance();

        let check = self.parse_expression(indent)?;

        match self.advance().kind {
            TokenKind::FatArrow => {}
            kind => return Err(format!("missing '=>' after if expression, found {kind:?}"))
        }

        // consume nl
        let true_branch = match self.peek(0).kind {
            TokenKind::Newline => {
                self.advance();
                self.parse_codeblock(indent)?
            }
            TokenKind::Identifier(Identifier::If) => return Err(format!("Nested if blocks have to be on a new line and indented")),
            _ => {
                let expr = self.parse_codeblock_expression(indent)?;

                if TokenKind::Newline == self.peek(0).kind {
                    self.advance();
                }

                CodeBlock {
                    indentation: indent,
                    expressions: vec![expr]
                }
            }
        };

        // else
        let else_branch = match (self.peek(0).kind, self.peek(1).kind) {
            (TokenKind::Indentation(indentation), TokenKind::Identifier(Identifier::Else)) if indentation == indent => {

                //consume indent and else
                self.advance();
                self.advance();

                // consume nl
                let else_branch = match self.peek(0).kind {
                    TokenKind::Newline => {
                        self.advance();
                        self.parse_codeblock(indent)?
                    },
                    _ => {
                        let expr = self.parse_codeblock_expression(indent)?;

                        if TokenKind::Newline == self.peek(0).kind {
                            self.advance();
                        }

                        CodeBlock {
                            indentation: indent,
                            expressions: vec![expr]
                        }
                    }
                };

                Some(else_branch)
            }
            _ => None
        };

        Ok(Expression::If(If {
            cond: Box::new(check),
            true_branch,
            else_branch
        }))
    }

    pub fn parse_expression(&mut self, indent: usize) -> Result<Expression, String> {
        match self.peek(0).kind {
            TokenKind::Identifier(Identifier::If) => {
                self.parse_if(indent)
            }
            TokenKind::Identifier(Identifier::For) => {
                self.parse_for(indent)
            }
            TokenKind::TripleDot => {
                self.advance();
                Ok(Expression::Placeholder)
            }
            TokenKind::Identifier(Identifier::Break) => {
                self.advance();
                Ok(Expression::Break)
            }
            TokenKind::JS => {
                self.parse_js()
            }
            TokenKind::Identifier(Identifier::Continue) => {
                self.advance();
                Ok(Expression::Continue)
            }
            _ => self.parse_equality(indent)
        }
    }

    pub fn parse_codeblock(&mut self, original_indent: usize) -> Result<CodeBlock, String> {
        let mut block = CodeBlock {
            indentation: original_indent,
            expressions: Vec::new()
        };

        loop {
            match (self.peek(0).kind, self.peek(1).kind) {
                (TokenKind::Indentation(_), TokenKind::Newline) => {
                    // consume indent and nl
                    self.advance();
                    self.advance();
                    continue;
                }
                (TokenKind::Indentation(indent), _) => {
                    if indent < block.indentation {
                        break;
                    }
                    if block.indentation == original_indent {
                        block.indentation = indent
                    }
                    if indent > block.indentation {
                        return Err(format!("Code block has inconsistent indentation"))
                    }
                }
                (_, _) => break
            }

            // consume indent
            self.advance();

            let expr = self.parse_codeblock_expression(block.indentation)?;

            block.expressions.push(expr);

            match self.peek(0).kind {
                TokenKind::Newline | TokenKind::EOF => {
                    self.advance();
                }
                // I dont understand why this case is needed
                TokenKind::Indentation(indent) => {}
                kind => return Err(format!("Invalid expression in code block: {kind:?}"))
            }
        }

        Ok(block)
    }

    pub fn parse_codeblock_expression(&mut self, indent: usize) -> Result<Expression, String> {
        match self.peek(0).kind {
            TokenKind::Identifier(Identifier::Let)
            | TokenKind::Identifier(Identifier::Mut) => self.parse_variable_decl(indent),
            TokenKind::Identifier(Identifier::Return) => {
                // consume return
                self.advance();
                let expr = self.parse_expression(indent)?;
                Ok(Expression::Return(Box::new(expr)))
            }
            TokenKind::Identifier(Identifier::Custom(iden)) => {
                match self.peek(1).kind {
                    TokenKind::Equal => {
                        // consume iden and =
                        self.advance();
                        self.advance();

                        let rhs = self.parse_expression(indent)?;

                        Ok(Expression::Assignment(Assignment {
                            lhs: iden,
                            rhs: Box::new(rhs)
                        }))
                    }
                    _ => {
                        self.parse_expression(indent)
                    }
                }
            }
            _ => self.parse_expression(indent)
        }
    }

    pub fn parse_js(&mut self) -> Result<Expression, String> {
        // consume JS token
        self.advance();

        if let TokenKind::Literal(Literal::String(code)) = self.advance().kind {
            Ok(Expression::JS(code))
        } else {
            Err(format!("Couldnt find js source code after @JS"))
        }
    }

    pub fn parse_module(&mut self, file_name: String) -> Result<Module, String> {
        let mut module = Module {
            module_name: file_name,
            type_defs: Vec::new(),
            function_defs: Vec::new(),
            toplevel_scope: CodeBlock::default()
        };

        while !self.is_at_end() {
            self.expr_start = self.current;
            let t = self.peek(0);
            match t.kind {
                TokenKind::EOF => break,
                TokenKind::ParenLeft => {
                    let expr = self.parse_expression(0)?;
                    module.toplevel_scope.expressions.push(expr);
                },
                TokenKind::ParenRight => todo!(),
                TokenKind::CurlyLeft => todo!(),
                TokenKind::CurlyRight => todo!(),
                TokenKind::SquareLeft => todo!(),
                TokenKind::SquareRight => todo!(),
                TokenKind::AngleLeft => todo!(),
                TokenKind::AngleRight => todo!(),
                TokenKind::Comma => todo!(),
                TokenKind::Colon => todo!(),
                TokenKind::DoubleColon => self.parse_fn_with_args(&mut module)?,
                TokenKind::Plus => todo!(),
                TokenKind::PlusEqual => todo!(),
                TokenKind::Mod => todo!(),
                TokenKind::Star => todo!(),
                TokenKind::LessEqual => todo!(),
                TokenKind::GreaterEqual => todo!(),
                TokenKind::EqualEqual => todo!(),
                TokenKind::Equal => todo!(),
                TokenKind::ThinArrow => todo!(),
                TokenKind::FatArrow => todo!(),
                TokenKind::Minus => todo!(),
                TokenKind::MinusEqual => todo!(),
                TokenKind::Slash => todo!(),
                TokenKind::Comment => todo!(),
                TokenKind::MultilineComment => todo!(),
                TokenKind::Power => todo!(),
                TokenKind::NotEqual => todo!(),
                TokenKind::NoneType => todo!(),
                TokenKind::Dot => todo!(),
                TokenKind::Ampersand => todo!(),
                TokenKind::Pipe => todo!(),
                TokenKind::Caret => todo!(),
                TokenKind::Tilde => todo!(),
                TokenKind::RShift => todo!(),
                TokenKind::LShift => todo!(),
                TokenKind::DoubleDot => todo!(),
                TokenKind::DoubleDotEqual => todo!(),
                TokenKind::TripleDot => todo!(),
                TokenKind::Tab => todo!(),
                TokenKind::Newline => { self.advance(); },
                TokenKind::TrianglePipe => todo!(),
                TokenKind::Dollar => todo!(),
                TokenKind::Indentation(_) => { self.advance(); },
                TokenKind::Literal(_) => {
                    let expr = self.parse_expression(0)?;
                    module.toplevel_scope.expressions.push(expr);
                },
                TokenKind::JS => {
                    let expr = self.parse_js()?;
                    module.toplevel_scope.expressions.push(expr);
                },
                TokenKind::Identifier(iden) => { 
                    match iden {
                        Identifier::Export 
                        | Identifier::Fn => {
                            // unconsume export/fn keyword
                            self.parse_fn_no_args(&mut module, Vec::new())?
                        }
                        Identifier::Let 
                        | Identifier::Mut => {
                            let expr = self.parse_variable_decl(0)?;
                            module.toplevel_scope.expressions.push(expr);
                        }
                        Identifier::If
                        | Identifier::For => {
                            let expr = self.parse_expression(0)?;
                            module.toplevel_scope.expressions.push(expr);
                        }
                        Identifier::Custom(name) => {
                            match self.peek(1).kind {
                                TokenKind::Equal => {
                                    self.advance(); // consume iden
                                    self.advance(); // consume = 

                                    let rhs = self.parse_expression(0)?;

                                    module.toplevel_scope.expressions.push(Expression::Assignment(Assignment {
                                        lhs: name,
                                        rhs: Box::new(rhs),
                                    }));
                                }
                                _ => {
                                    let expr = self.parse_expression(0)?;

                                    module.toplevel_scope.expressions.push(expr);
                                }
                            }
                        }
                        _ => { self.advance(); }
                    }
                }
                TokenKind::Hash => todo!(),
            };

        }

        Ok(module)
    }
}