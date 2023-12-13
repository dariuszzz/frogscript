use std::collections::HashMap;

use crate::lexer::{Token, TokenKind, Literal, Identifier};

#[derive(Debug, Clone)]
pub enum BinaryOperation {
    Add,
    Subtract,
    Multiply,
    Divide,
    Power,
    And,
    Or,
}

#[derive(Debug, Clone)]
pub enum TypeKind {
    Infer, 
    Void,
    Int,
    Uint,
    Float,
    String,
    Boolean,
    Custom(String),
}

#[derive(Debug, Clone)]
pub struct Type {
    pub type_kind: TypeKind,
    pub is_reference: bool,
}


#[derive(Debug, Clone)]
pub struct VariableDecl  {
    pub var_name: String,
    pub var_type: Type,
    pub var_value: Box<Expression>,
    pub is_implicit: bool,
}

#[derive(Debug, Clone)]
pub struct FunctionCall  {
    pub func_name: String,
    pub arguments: Vec<Expression>,
}

#[derive(Debug, Clone)]
pub struct BinaryOp  {
    pub op: BinaryOperation,
    pub lhs: Box<Expression>,
    pub rhs: Box<Expression>,
}

#[derive(Debug, Clone)]
pub enum Expression {
    VariableDecl(VariableDecl),
    Literal(Literal),
    BinaryOp(BinaryOp),
    FunctionCall(FunctionCall),
    If,
}

#[derive(Debug, Clone, Default)]
pub struct CodeBlock  {
    pub indentation: usize,
    pub expressions: Vec<Expression>
}

#[derive(Debug, Clone)]
pub struct FunctionArgument {
    pub arg_name: String,
    pub arg_type: Type,
    pub is_implicit: bool,
}

#[derive(Debug, Clone)]
pub struct FunctionDef {
    pub export: bool,
    pub func_name: String,
    pub argument_list: Vec<FunctionArgument>,
    pub return_type: Type,
    pub function_body: CodeBlock
}

#[derive(Debug, Clone)]
pub struct VariantDef {
    pub variant_name: String,
    pub fields: Vec<StructField>
}

#[derive(Debug, Clone)]
pub struct EnumDef {
    pub enum_name: String,
    pub variants: Vec<VariantDef>
}

#[derive(Debug, Clone)]
pub struct StructField {
    pub field_name: String,
    pub field_type: Type,
    pub is_final: bool
}

#[derive(Debug, Clone)]
pub struct StructDef {
    pub struct_name: String,
    pub fields: Vec<StructField>,
    pub methods: Vec<FunctionDef> 
}

#[derive(Debug, Clone)]
pub struct TypeDef {
    pub export: bool,
    pub type_kind: TypeDefKind
}

#[derive(Debug, Clone)]
pub enum TypeDefKind {
    EnumDef(EnumDef),
    StructDef(StructDef)
}

#[derive(Debug, Clone, Default)]
pub struct Module {
    pub module_name: String,
    pub type_defs: Vec<TypeDef>,
    pub function_defs: Vec<FunctionDef>,
    pub toplevel_scope: CodeBlock
}

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

    // skips comments
    fn advance(&mut self) -> Token {
        match self.peek(0) {
            Some(t) => {
                self.current += 1;
                t
            },
            None => {
                self.current += 1;
                Token { kind: TokenKind::EOF, start_char: 0, start_line: 0, lexeme: "".to_owned() }
            }
        }
    }

    fn peek(&mut self, n: usize) -> Option<Token> {
        if self.is_at_end() { return None }
        return self.tokens.get(self.current + n).and_then(|t| Some(t.clone()))
    }

    fn match_token(&mut self, expected: Token) -> bool {
        if self.is_at_end() { return false }
        if self.tokens.get(self.current + 1).unwrap().clone() != expected {
            return false
        }

        self.current += 1;
        return true
    }

    fn collect_until<F>(&mut self, until: F) -> Result<Vec<Token>, String> 
    where F: Fn(Token) -> bool 
    {
        let mut tokens = Vec::new();
        while let Some(t) = self.peek(0) {
            if until(t) { break }
            tokens.push(self.advance());
        }

        if self.is_at_end() {
            return Err("Token not found".to_owned());
        }

        return Ok(tokens)
    }
    
    fn collect_pattern(&mut self, pattern: &[(TokenKind, bool)]) -> Result<Vec<Token>, String> {

        let mut tokens = Vec::new();

        for (token_kind, opt) in pattern {
            match self.peek(0) {
                Some(Token { kind, .. }) if kind == *token_kind => tokens.push(self.advance()),
                Some(Token { kind, .. }) if !opt => return Err(format!("Token {token_kind:?} missing, found: {kind:?}").to_owned()),
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
                (Some(Token { kind: TokenKind::Identifier(Identifier::Custom(_)), .. }), TokenKind::Identifier(Identifier::_MatchAnyCustom)) => { tokens.insert(key.to_string(), self.advance()); }
                (Some(Token { kind, .. }), _) if kind == *token_kind => { tokens.insert(key.to_string(), self.advance()); } 
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
                (true,  "export",   TokenKind::Identifier(Identifier::Export)),
                (false, "fn_key",   TokenKind::Identifier(Identifier::Fn)),
                (false, "func_name",TokenKind::Identifier(Identifier::_MatchAnyCustom)),
                (true,  "colon",    TokenKind::Colon),
                (true,  "ret_type", TokenKind::Identifier(Identifier::_MatchAnyCustom)),
                (false, "arrow",    TokenKind::FatArrow)
            ]
        ) {
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

            if let Some(_) = fn_decl_tokens.get("export") {
                function_def.export = true;
            }
        } else {
            return Err("Missing tokens in '(export) fn funcname'".to_owned())
        }

        module.function_defs.push(function_def);

        Ok(())
    }

    fn parse_fn_with_args(&mut self, module: &mut Module) -> Result<(), String> {

        let mut argument_list = Vec::new();

        while let Some(arg_tokens) = self.safe_collect_pattern(
            &[
                (false, "double_colon",     TokenKind::DoubleColon),
                (true, "implicit",         TokenKind::Identifier(Identifier::Implicit)),
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

    pub fn parse_variable_decl(&mut self, module: &mut Module) -> Result<(), String> {
        //we know the first token is a let or mut so we skip the first token
        self.advance();

        if let Some(variable_decl_tokens) = self.safe_collect_pattern(
            &[
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

            let value = self.parse_expression()?;

            let variable = VariableDecl {
                var_name,
                var_type: Type { type_kind, is_reference },
                var_value: Box::new(value),
                is_implicit,
            };

            module.toplevel_scope.expressions.push(Expression::VariableDecl(variable));

            Ok(())
        } else {
            return Err(format!("Invalid variable declaration"));
        }
    }

    pub fn parse_method_call(&mut self, called_on: Expression) -> Result<Expression, String> {
        // consume dot
        self.advance();

        let name = if let Token { kind: TokenKind::Identifier(Identifier::Custom(func_name)), .. } = self.advance() {
            func_name
        } else {
            return Err(format!("no func name found"));
        };

        let mut call = FunctionCall { 
            func_name: name, 
            arguments: vec![called_on]
        };

        let expr = match self.advance() {
            Token { kind: TokenKind::ParenLeft, .. } => {
                loop {
                    if let Some(next_token) = self.peek(0) {
                        match next_token.kind {
                            TokenKind::ParenRight => {
                                self.advance();
                                break;
                            }
                            TokenKind::Comma => {
                                self.advance();
                            }
                            _ => call.arguments.push(self.parse_expression()?)
                        }
                    }
                }

                Expression::FunctionCall(call)
            }
            _ => todo!("implement no parens for single arg")
        };

        match self.peek(0) {
            Some(Token { kind: TokenKind::Dot, .. }) => {
                self.parse_method_call(expr)
            }
            _ => Ok(expr)
        }
    }

    pub fn parse_standalone_function_call(&mut self, name: String) -> Result<Expression, String> {
        let mut call = FunctionCall { 
            func_name: name, 
            arguments: Vec::new()
        };

        let expr = match self.advance() {
            Token { kind: TokenKind::ParenLeft, .. } => {
                loop {
                    if let Some(next_token) = self.peek(0) {
                        match next_token.kind {
                            TokenKind::ParenRight => {
                                self.advance();
                                break;
                            }
                            TokenKind::Comma => {
                                self.advance();
                            }
                            _ => call.arguments.push(self.parse_expression()?)
                        }
                    }
                }

                Expression::FunctionCall(call)
            }
            _ => todo!("implement no parens for single arg")
        };
        
        match self.peek(0) {
            Some(Token { kind: TokenKind::Dot, .. }) => {
                self.parse_method_call(expr)
            }
            _ => Ok(expr)
        }
    }

    pub fn parse_operator(&mut self, op: BinaryOperation, lhs: Expression) -> Result<Expression, String> {
        self.advance();
        let rhs = self.parse_expression()?;

        Ok(Expression::BinaryOp(BinaryOp { op, lhs: Box::new(lhs), rhs: Box::new(rhs) }))
    }

    pub fn parse_expr_in_parentheses(&mut self) -> Result<Expression, String> {

        let inner_expr = self.parse_expression()?;

        if let Token { kind: TokenKind::ParenRight, .. } = self.advance() {
            return Ok(inner_expr)
        } else {
            return Err(format!("Unclosed parentheses"))
        }
    }

    pub fn parse_expression(&mut self) -> Result<Expression, String> {
        println!("{:?}", self.peek(0));
        match self.advance() {
            Token { kind, .. } => {
                match kind {
                    TokenKind::Literal(literal) => {
                        let expr = Expression::Literal(literal);
                        match self.peek(0) {
                            Some(Token { kind: TokenKind::Newline, .. }) 
                            | Some(Token { kind: TokenKind::Comma, .. }) 
                            | Some(Token { kind: TokenKind::ParenRight, .. }) => Ok(expr),
                            Some(Token { kind: TokenKind::Dot, .. }) => self.parse_method_call(expr),
                            Some(Token { kind: TokenKind::Plus, .. }) => self.parse_operator(BinaryOperation::Add, expr),
                            Some(Token { kind: TokenKind::Minus, .. }) => self.parse_operator(BinaryOperation::Subtract, expr),
                            Some(Token { kind: TokenKind::Star, .. }) => self.parse_operator(BinaryOperation::Multiply, expr),
                            Some(Token { kind: TokenKind::Slash, .. }) => self.parse_operator(BinaryOperation::Divide, expr),
                            Some(Token { kind: TokenKind::Caret, .. }) => self.parse_operator(BinaryOperation::Power, expr),
                            Some(Token { kind: TokenKind::Ampersand, .. }) => self.parse_operator(BinaryOperation::And, expr),
                            Some(Token { kind: TokenKind::Pipe, .. }) => self.parse_operator(BinaryOperation::Or, expr),
                            _ => return Err(format!("Unexpected token after literal")),
                        }
                    }
                    TokenKind::ParenLeft => {
                        let expr = self.parse_expr_in_parentheses()?;
                        match self.peek(0) {
                            Some(Token { kind: TokenKind::Newline, .. }) 
                            | Some(Token { kind: TokenKind::ParenRight, .. }) => Ok(expr),
                            Some(Token { kind: TokenKind::Dot, .. }) => self.parse_method_call(expr),
                            Some(Token { kind: TokenKind::Plus, .. }) => self.parse_operator(BinaryOperation::Add, expr),
                            Some(Token { kind: TokenKind::Minus, .. }) => self.parse_operator(BinaryOperation::Subtract, expr),
                            Some(Token { kind: TokenKind::Star, .. }) => self.parse_operator(BinaryOperation::Multiply, expr),
                            Some(Token { kind: TokenKind::Slash, .. }) => self.parse_operator(BinaryOperation::Divide, expr),
                            Some(Token { kind: TokenKind::Caret, .. }) => self.parse_operator(BinaryOperation::Power, expr),
                            Some(Token { kind: TokenKind::Ampersand, .. }) => self.parse_operator(BinaryOperation::And, expr),
                            Some(Token { kind: TokenKind::Pipe, .. }) => self.parse_operator(BinaryOperation::Or, expr),
                            _ => return Err(format!("Unexpected token after paren")),
                        }
                    }
                    TokenKind::Identifier(Identifier::Custom(name)) => {
                        self.parse_standalone_function_call(name)
                    }
                    kind @ _ => {
                        println!("{kind:?}");
                        todo!("This is either invalid or unimplemented")
                    }
                }
            }
        }
    }

    pub fn parse_file(&mut self, file_name: String) -> Result<Module, String> {
        let mut module = Module {
            module_name: file_name,
            type_defs: Vec::new(),
            function_defs: Vec::new(),
            toplevel_scope: CodeBlock::default()
        };

        while !self.is_at_end() {
            self.expr_start = self.current;
            let t = self.peek(0);
            if let None = t { break; }
            let t = t.unwrap();
            match t.kind {
                TokenKind::EOF => unreachable!(),
                TokenKind::ParenLeft => todo!(),
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
                TokenKind::Tab => todo!(),
                TokenKind::Newline => { self.advance(); },
                TokenKind::TrianglePipe => todo!(),
                TokenKind::Dollar => todo!(),
                TokenKind::Indentation(_) => { self.advance(); },
                TokenKind::Literal(_) => todo!(),
                TokenKind::Identifier(iden) => { 
                    match iden {
                        Identifier::Export 
                        | Identifier::Fn => self.parse_fn_no_args(&mut module, Vec::new())?,
                        Identifier::Let 
                        | Identifier::Mut => self.parse_variable_decl(&mut module)?, 
                        _ => { self.advance(); }
                    }
                }
                TokenKind::Hash => todo!(),
            };

        }

        Ok(module)
    }
}