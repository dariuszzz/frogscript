use std::collections::HashMap;
use std::env::temp_dir;
use std::path::{Path, PathBuf};

use crate::ast::*;
use crate::lexer::{Identifier, Lexer, Literal, Token, TokenKind};

#[derive(Debug, Clone, Default)]
pub struct Program {
    pub modules: Vec<Module>,
}

pub struct Parser {
    pub tokens: Vec<Token>,
    pub current: usize,
    pub expr_start: usize,
    pub path: PathBuf,
    pub modules_to_parse: Vec<String>,
    pub parsed_modules: Vec<String>,
    pub current_module: String,
}

impl Parser {
    pub fn new(path: PathBuf) -> Self {
        Self {
            tokens: Vec::new(),
            current: 0,
            expr_start: 0,
            path,
            modules_to_parse: Vec::new(),
            parsed_modules: Vec::new(),
            current_module: String::new(),
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
            }
        }
    }

    fn peek(&mut self, n: usize) -> Token {
        if self.is_at_end() {
            return Token {
                kind: TokenKind::EOF,
                start_char: 0,
                start_line: 0,
                lexeme: String::new(),
            };
        }
        return self.tokens.get(self.current + n).map_or(
            Token {
                kind: TokenKind::EOF,
                start_char: 0,
                start_line: 0,
                lexeme: String::new(),
            },
            |t| t.clone(),
        );
    }

    fn peek_skip_ws(&mut self, min_indent: usize) -> Result<Token, String> {
        let mut i = 0;
        loop {
            let token = self.peek(i);
            match token.kind {
                TokenKind::Newline => {
                    i += 1;
                }
                TokenKind::Indentation(indent) if indent >= min_indent => {
                    i += 1;
                }
                _ => return Ok(token),
            }
        }
    }

    fn advance_skip_ws(&mut self, min_indent: usize) -> Token {
        loop {
            let token = self.peek(0);
            match token.kind {
                TokenKind::Newline => {
                    self.advance();
                }
                TokenKind::Indentation(indent) if indent >= min_indent => {
                    self.advance();
                }
                _ => return self.advance(),
            }
        }
    }

    fn safe_collect_pattern(
        &mut self,
        pattern: &[(bool, &str, TokenKind)],
    ) -> Option<HashMap<String, Token>> {
        let mut tokens = HashMap::new();
        let starting_pos = self.current;

        for (opt, key, token_kind) in pattern {
            match (self.peek(0), token_kind) {
                (
                    Token {
                        kind: TokenKind::Identifier(Identifier::Custom(_)),
                        ..
                    },
                    TokenKind::Identifier(Identifier::_MatchAnyCustom),
                ) => {
                    tokens.insert(key.to_string(), self.advance());
                }
                (Token { kind, .. }, _) if kind == *token_kind => {
                    tokens.insert(key.to_string(), self.advance());
                }
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

    fn parse_fn_no_args(&mut self, args: Vec<FunctionArgument>) -> Result<FunctionDef, String> {
        let mut function_def = FunctionDef {
            export: false,
            func_name: String::new(),
            argument_list: args,
            return_type: Type {
                type_kind: TypeKind::Infer,
                is_reference: false,
                is_structural: false,
            },
            function_body: CodeBlock::default(),
        };

        if let Some(fn_decl_tokens) = self.safe_collect_pattern(&[
            (true, "ident_1", TokenKind::Indentation(0)),
            (true, "export", TokenKind::Identifier(Identifier::Export)),
            (false, "fn_key", TokenKind::Identifier(Identifier::Fn)),
            (
                false,
                "name",
                TokenKind::Identifier(Identifier::_MatchAnyCustom),
            ),
        ]) {
            if let Some(_) = fn_decl_tokens.get("export") {
                function_def.export = true;
            }

            let name_token = fn_decl_tokens.get("name").unwrap();
            match &name_token.kind {
                TokenKind::Identifier(Identifier::Custom(name)) => {
                    function_def.func_name = name.clone()
                }
                _ => unreachable!(),
            }

            if let TokenKind::ParenLeft = self.peek(0).kind {
                self.advance();

                loop {
                    let mut arg = FunctionArgument {
                        arg_name: String::new(),
                        arg_type: Type {
                            type_kind: TypeKind::Infer,
                            is_reference: false,
                            is_structural: false,
                        },
                        is_env: false,
                    };

                    match self.peek_skip_ws(0)?.kind {
                        TokenKind::Identifier(Identifier::Custom(arg_name)) => {
                            self.advance_skip_ws(0);
                            arg.arg_name = arg_name.clone();
                            arg.arg_type = self.parse_type()?;

                            if let TokenKind::Comma = self.peek_skip_ws(0)?.kind {
                                self.advance_skip_ws(0);
                            }

                            function_def.argument_list.push(arg);
                        }
                        TokenKind::ParenRight => {
                            self.advance_skip_ws(0);
                            break;
                        }
                        _ => unreachable!(),
                    }
                }
            }

            if let TokenKind::ThinArrow = self.peek(0).kind {
                self.advance();
                function_def.return_type = self.parse_type()?;
            }

            if let TokenKind::Equal = self.advance().kind {
            } else {
                return Err(format!("'=' missing in func definition"));
            }
        } else {
            let line = self.peek(0).start_line;
            let pos = self.peek(0).start_char;
            return Err(format!(
                "{}:{line}:{pos} Missing tokens in '(export) fn funcname'",
                self.current_module
            ));
        }

        match self.peek(0) {
            Token {
                kind: TokenKind::Newline,
                ..
            } => {
                //consume nl
                self.advance();

                let block = self.parse_codeblock(0)?;
                function_def.function_body = block;
            }
            _ => {
                let expr = self.parse_codeblock_expression(0)?;
                function_def.function_body.expressions.push(expr);
            }
        }

        Ok(function_def)
    }

    fn parse_fn_with_args(&mut self, module: &mut Module) -> Result<FunctionDef, String> {
        let mut argument_list = Vec::new();

        while let Some(arg_tokens) = self.safe_collect_pattern(&[
            (true, "indent_1", TokenKind::Indentation(0)),
            (false, "double_colon", TokenKind::DoubleColon),
            (
                false,
                "name",
                TokenKind::Identifier(Identifier::_MatchAnyCustom),
            ),
        ]) {
            let mut arg_def = FunctionArgument {
                arg_name: String::new(),
                arg_type: Type {
                    type_kind: TypeKind::Uint,
                    is_reference: false,
                    is_structural: false,
                },
                is_env: true,
            };

            let name_token = arg_tokens.get("name").unwrap();
            match &name_token.kind {
                TokenKind::Identifier(Identifier::Custom(name)) => arg_def.arg_name = name.clone(),
                _ => {}
            };

            arg_def.arg_type = self.parse_type()?;

            // newline i believe
            self.advance();

            argument_list.push(arg_def);
        }

        self.parse_fn_no_args(argument_list)
    }

    pub fn parse_type(&mut self) -> Result<Type, String> {
        let mut type_ = Type {
            type_kind: TypeKind::Infer,
            is_reference: false,
            is_structural: false,
        };

        type_.type_kind = match self.peek(0).kind {
            TokenKind::Ampersand => {
                self.advance();
                type_.is_reference = true;
                self.parse_type()?.type_kind
            }
            TokenKind::Tilde => {
                self.advance();
                type_.is_structural = true;
                self.parse_type()?.type_kind
            }
            TokenKind::Identifier(Identifier::Custom(type_name)) => {
                self.advance();

                let mut path = vec![type_name];

                while let TokenKind::DoubleColon = self.peek(0).kind {
                    self.advance();
                    match self.peek(0).kind {
                        TokenKind::Identifier(Identifier::Custom(iden)) => {
                            path.push(iden);
                            self.advance();
                        }
                        _ => break,
                    }
                }

                if path.len() > 1 {
                    self.modules_to_parse.push(path[0].clone());
                }

                let name = path.join("::");

                match name.as_str() {
                    "bool" => TypeKind::Boolean,
                    "string" => TypeKind::String,
                    "float" => TypeKind::Float,
                    "int" => TypeKind::Int,
                    "uint" => TypeKind::Uint,
                    _ => TypeKind::Custom(CustomType {
                        type_module: Vec::new(),
                        name: name,
                    }),
                }
            }
            TokenKind::SquareLeft => {
                self.advance();

                if let TokenKind::SquareRight = self.advance().kind {
                } else {
                    return Err(format!("Unclosed array type"));
                }

                let arr_type = self.parse_type()?;

                TypeKind::Array(Box::new(arr_type))
            }
            TokenKind::Identifier(Identifier::Fn) => {
                self.advance();

                if let TokenKind::ParenLeft = self.peek(0).kind {
                    self.advance();
                    let mut args1 = self.parse_func_type_args()?;
                    let mut args2 = Vec::new();
                    let mut were_there_2_arg_lists = false;

                    match self.advance().kind {
                        TokenKind::ThinArrow => {}
                        TokenKind::ParenRight => {
                            were_there_2_arg_lists = true;

                            if let TokenKind::ParenLeft = self.advance().kind {
                            } else {
                                return Err(format!("Expected another arg list"));
                            }

                            args2.append(&mut self.parse_func_type_args()?);

                            match self.advance().kind {
                                TokenKind::ThinArrow => {}
                                _ => return Err(format!("'->' token missing in function type")),
                            }
                        }
                        _ => return Err(format!("'->' or ')' token missing in function type")),
                    }

                    let return_type = self.parse_type()?;

                    if let TokenKind::ParenRight = self.advance().kind {
                    } else {
                        return Err(format!("Unclosed function type"));
                    }

                    if args1.len() == 1 {
                        if let TypeKind::Void = args1[0].type_kind {
                            args1 = Vec::new();
                        }
                    }

                    if args2.len() == 1 {
                        if let TypeKind::Void = args2[0].type_kind {
                            args2 = Vec::new();
                        }
                    }

                    if were_there_2_arg_lists {
                        TypeKind::Function(FunctionType {
                            env_args: args1,
                            args: args2,
                            ret: Box::new(return_type),
                        })
                    } else {
                        TypeKind::Function(FunctionType {
                            env_args: Vec::new(),
                            args: args1,
                            ret: Box::new(return_type),
                        })
                    }
                } else {
                    return Err(format!("Expected '(' after Fn in type"));
                }
            }
            TokenKind::ParenLeft => {
                self.advance();

                // yuck
                let token = self.peek(0);
                if let TokenKind::ParenRight = token.kind {
                    // handle () type
                    self.advance();
                    TypeKind::Void
                } else {
                    return Err(format!(
                        "{}:{}:{} Unexpected token after '(' in type",
                        self.current_module, token.start_line, token.start_char
                    ));
                }
            }
            token => return Err(format!("Invalid token in type: {token:?}")),
        };

        Ok(type_)
    }

    pub fn parse_func_type_args(&mut self) -> Result<Vec<Type>, String> {
        let mut args = Vec::new();

        loop {
            let arg_type = self.parse_type()?;

            args.push(arg_type);

            match self.peek(0).kind {
                TokenKind::Comma => self.advance(),
                TokenKind::ParenRight | TokenKind::ThinArrow => break,
                _ => return Err(format!("Invalid function argument separator in type")),
            };
        }

        Ok(args)
    }

    pub fn parse_variable_decl(&mut self, indent: usize) -> Result<Expression, String> {
        let mut is_mutable = true;

        if let Token {
            kind: TokenKind::Identifier(Identifier::Let),
            ..
        } = self.advance()
        {
            is_mutable = false;
        }

        if let Some(variable_decl_tokens) = self.safe_collect_pattern(&[
            (true, "indent_1", TokenKind::Indentation(0)),
            (true, "env", TokenKind::Identifier(Identifier::Env)),
        ]) {
            let is_env = variable_decl_tokens.get("env").is_some();

            let var_type = match self.peek(1).kind {
                TokenKind::Equal => {
                    // No type
                    Type {
                        type_kind: TypeKind::Infer,
                        is_reference: false,
                        is_structural: false,
                    }
                }
                _ => {
                    // Type
                    self.parse_type()?
                }
            };

            let var_name = match self.advance().kind {
                TokenKind::Identifier(Identifier::Custom(name)) => name,
                _ => return Err(format!("Variable name missing in declaration")),
            };

            match self.advance().kind {
                TokenKind::Equal => {}
                token => return Err(format!("'=' missing in var decl: {token:?}")),
            }

            let value = self.parse_expression(indent)?;

            let variable = VariableDecl {
                var_name,
                var_type,
                var_value: Box::new(value),
                is_mutable,
                is_env,
            };

            Ok(Expression::VariableDecl(variable))
        } else {
            return Err(format!("Invalid variable declaration"));
        }
    }

    pub fn parse_method_call_or_field_access(
        &mut self,
        called_on: Expression,
        indent: usize,
    ) -> Result<Expression, String> {
        let name = match self.advance() {
            Token {
                kind: TokenKind::Identifier(Identifier::Custom(iden_name)),
                ..
            } => {
                let mut path = vec![iden_name];

                while let TokenKind::DoubleColon = self.peek(0).kind {
                    self.advance();
                    match self.peek(0).kind {
                        TokenKind::Identifier(Identifier::Custom(iden)) => {
                            path.push(iden);
                            self.advance();
                        }
                        _ => break,
                    }
                }

                path
            }
            token => {
                return Err(format!(
                    "{:?}:{:?}: No func/field name found, got {:?} instead",
                    token.start_line, token.start_char, token.kind
                ))
            }
        };

        if let Token {
            kind: TokenKind::ParenLeft,
            ..
        } = self.peek(0)
        {
            if name.len() > 1 {
                self.modules_to_parse.push(name[0].clone());
            }
            self.advance();
            let mut call = FunctionCall {
                func_name: name.join("::"),
                arguments: vec![called_on],
            };

            loop {
                let token = self.peek_skip_ws(indent)?;
                match token.kind {
                    TokenKind::ParenRight => {
                        self.advance_skip_ws(indent);
                        break;
                    }
                    TokenKind::Comma => {
                        self.advance_skip_ws(indent);

                        // allow for trailing ,
                        if let TokenKind::ParenRight = self.peek_skip_ws(0)?.kind {
                            self.advance_skip_ws(indent);
                            break;
                        }
                    }
                    _ => call.arguments.push(self.parse_expression(indent)?),
                }
            }

            Ok(Expression::FunctionCall(call))
        } else {
            if name.len() > 1 {
                return Err(format!("Missing '(' after qualifed function name"));
            }

            Ok(Expression::FieldAccess(FieldAccess {
                expr: Box::new(called_on),
                field: name[0].clone(),
            }))
        }
    }

    pub fn parse_standalone_function_call(
        &mut self,
        name: String,
        indent: usize,
    ) -> Result<Expression, String> {
        let mut call = FunctionCall {
            func_name: name,
            arguments: Vec::new(),
        };

        if let Token {
            kind: TokenKind::ParenLeft,
            ..
        } = self.advance()
        {
            loop {
                let token = self.peek_skip_ws(indent)?;
                match token.kind {
                    TokenKind::ParenRight => {
                        self.advance_skip_ws(indent);
                        break;
                    }
                    TokenKind::Comma => {
                        self.advance_skip_ws(indent);
                        // allow for trailing ,
                        if let TokenKind::ParenRight = self.peek_skip_ws(0)?.kind {
                            self.advance_skip_ws(indent);
                            break;
                        }
                    }
                    _ => call.arguments.push(self.parse_expression(indent)?),
                }
            }
        } else {
            unreachable!()
        }

        Ok(Expression::FunctionCall(call))
    }

    pub fn parse_equality(&mut self, indent: usize) -> Result<Expression, String> {
        let mut lhs = self.parse_ord(indent)?;

        loop {
            let token = self.peek_skip_ws(indent)?;
            let op = match token.kind {
                TokenKind::NotEqual => BinaryOperation::NotEqual,
                TokenKind::EqualEqual => BinaryOperation::Equal,
                _ => break,
            };

            // consume != or ==
            self.advance_skip_ws(indent);

            let rhs = self.parse_ord(indent)?;

            lhs = Expression::BinaryOp(BinaryOp {
                op,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            });
        }

        Ok(lhs)
    }

    pub fn parse_ord(&mut self, indent: usize) -> Result<Expression, String> {
        let mut lhs = self.parse_range(indent)?;

        let token = self.peek_skip_ws(indent)?;
        let op = match token.kind {
            TokenKind::AngleLeft => BinaryOperation::Less,
            TokenKind::AngleRight => BinaryOperation::Greater,
            TokenKind::LessEqual => BinaryOperation::LessEqual,
            TokenKind::GreaterEqual => BinaryOperation::GreaterEqual,
            _ => return Ok(lhs),
        };

        // consume > or < or >= or <=
        self.advance_skip_ws(indent);

        let rhs = self.parse_range(indent)?;

        lhs = Expression::BinaryOp(BinaryOp {
            op,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        });

        Ok(lhs)
    }

    pub fn parse_range(&mut self, indent: usize) -> Result<Expression, String> {
        let mut lhs = self.parse_sum(indent)?;

        loop {
            let token = self.peek_skip_ws(indent)?;
            let inclusive = match token.kind {
                TokenKind::DoubleDot => false,
                TokenKind::DoubleDotEqual => true,
                _ => break,
            };

            // consume .. or ..=
            self.advance_skip_ws(indent);

            let rhs = self.parse_sum(indent)?;

            lhs = Expression::Range(Range {
                start: Box::new(lhs),
                end: Box::new(rhs),
                inclusive,
            });
        }

        Ok(lhs)
    }

    pub fn parse_sum(&mut self, indent: usize) -> Result<Expression, String> {
        let mut lhs = self.parse_product(indent)?;

        loop {
            let token = self.peek_skip_ws(indent)?;
            let op = match token.kind {
                TokenKind::Plus => BinaryOperation::Add,
                TokenKind::Minus => BinaryOperation::Subtract,
                _ => break,
            };

            // consume + or -
            self.advance_skip_ws(indent);

            let rhs = self.parse_product(indent)?;

            lhs = Expression::BinaryOp(BinaryOp {
                op,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            });
        }

        Ok(lhs)
    }

    pub fn parse_product(&mut self, indent: usize) -> Result<Expression, String> {
        let mut lhs = self.parse_term(indent)?;

        loop {
            let token = self.peek_skip_ws(indent)?;
            let op = match token.kind {
                TokenKind::Star => BinaryOperation::Multiply,
                TokenKind::Slash => BinaryOperation::Divide,
                _ => break,
            };

            // consume * or /
            self.advance_skip_ws(indent);

            let rhs = self.parse_term(indent)?;

            lhs = Expression::BinaryOp(BinaryOp {
                op,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            });
        }

        Ok(lhs)
    }

    pub fn parse_term(&mut self, indent: usize) -> Result<Expression, String> {
        let token = self.advance_skip_ws(indent);
        let mut term = match token {
            Token {
                start_char,
                start_line,
                kind,
                ..
            } => match kind {
                TokenKind::Minus => {
                    let term = self.parse_term(indent)?;

                    Expression::UnaryOp(UnaryOp {
                        op: UnaryOperation::Negative,
                        operand: Box::new(term),
                    })
                }
                TokenKind::Literal(literal) => self.parse_num(literal, indent)?,
                TokenKind::ParenLeft => self.parse_expr_in_parentheses(indent)?,
                TokenKind::Identifier(Identifier::Custom(name)) => {
                    self.parse_custom_iden(name, indent)?
                }
                TokenKind::SquareLeft => self.parse_array_literal(indent)?,
                kind => {
                    dbg!(format!(
                        "[{:?}:{:?}] unexpected token {:?}",
                        start_line, start_char, kind
                    ));
                    todo!("This is either invalid or unimplemented")
                }
            },
        };

        loop {
            let token = self.peek_skip_ws(indent)?;
            term = match token {
                Token {
                    kind: TokenKind::Dot,
                    ..
                } => {
                    self.advance_skip_ws(indent);
                    self.parse_method_call_or_field_access(term, indent)?
                }
                Token {
                    kind: TokenKind::SquareLeft,
                    ..
                } => {
                    self.advance_skip_ws(indent);
                    self.parse_array_access(term, indent)?
                }
                _ => break,
            };
        }

        Ok(term)
    }

    pub fn parse_array_literal(&mut self, indent: usize) -> Result<Expression, String> {
        let mut array = ArrayLiteral {
            elements: Vec::new(),
        };

        loop {
            let elem = self.parse_expression(indent)?;

            array.elements.push(elem);

            let token = self.peek_skip_ws(indent)?;
            match token.kind {
                TokenKind::Comma => {
                    self.advance_skip_ws(indent);
                    // allow for trailing ,
                    if let TokenKind::SquareRight = self.peek_skip_ws(indent)?.kind {
                        self.advance_skip_ws(indent);
                        break;
                    }
                }
                TokenKind::SquareRight => {
                    self.advance_skip_ws(indent);
                    break;
                }
                _ => return Err(format!("Unexpected token in array literal instead of ','")),
            };
        }

        Ok(Expression::ArrayLiteral(array))
    }

    pub fn parse_expr_in_parentheses(&mut self, indent: usize) -> Result<Expression, String> {
        let expr = self.parse_expression(indent)?;

        if let Token {
            kind: TokenKind::ParenRight,
            ..
        } = self.advance()
        {
        } else {
            return Err(format!("Unclosed parentheses"));
        }

        Ok(expr)
    }

    pub fn parse_num(&mut self, literal: Literal, indent: usize) -> Result<Expression, String> {
        Ok(Expression::Literal(literal))
    }

    pub fn parse_array_access(
        &mut self,
        lhs: Expression,
        indent: usize,
    ) -> Result<Expression, String> {
        let index = self.parse_expression(indent)?;

        let expr = if let TokenKind::SquareRight = self.advance().kind {
            Expression::ArrayAccess(ArrayAccess {
                expr: Box::new(lhs),
                index: Box::new(index),
            })
        } else {
            return Err(format!("Array access operator not closed"));
        };

        match self.peek(0) {
            Token {
                kind: TokenKind::Dot,
                ..
            } => {
                self.advance();
                self.parse_method_call_or_field_access(expr, indent)
            }
            Token {
                kind: TokenKind::SquareLeft,
                ..
            } => {
                self.advance();
                self.parse_array_access(expr, indent)
            }
            _ => Ok(expr),
        }
    }

    pub fn parse_variable(
        &mut self,
        var_name: String,
        indent: usize,
    ) -> Result<Expression, String> {
        Ok(Expression::Variable(Variable { name: var_name }))
    }

    pub fn parse_custom_iden(
        &mut self,
        identifier: String,
        indent: usize,
    ) -> Result<Expression, String> {
        let mut path = vec![identifier];

        while let TokenKind::DoubleColon = self.peek_skip_ws(indent)?.kind {
            self.advance_skip_ws(indent);
            match self.peek(0).kind {
                TokenKind::Identifier(Identifier::Custom(iden)) => {
                    path.push(iden);
                    self.advance();
                }
                _ => break,
            }
        }

        if path.len() > 1 {
            self.modules_to_parse.push(path[0].clone());
        }

        let final_name = path.join("::");

        let expr = match self.peek_skip_ws(0)?.kind {
            TokenKind::ParenLeft => self.parse_standalone_function_call(final_name, indent)?,
            TokenKind::CurlyLeft => {
                let struct_literal =
                    if let Expression::AnonStruct(lit) = self.parse_struct_literal(indent)? {
                        lit
                    } else {
                        unreachable!()
                    };

                Expression::NamedStruct(NamedStruct {
                    casted_to: final_name,
                    struct_literal,
                })
            }
            _ => self.parse_variable(final_name, indent)?,
        };

        Ok(expr)
    }

    pub fn parse_for(&mut self, indent: usize) -> Result<Expression, String> {
        if let Some(tokens) = self.safe_collect_pattern(&[
            (false, "for", TokenKind::Identifier(Identifier::For)),
            (
                false,
                "binding",
                TokenKind::Identifier(Identifier::_MatchAnyCustom),
            ),
            (false, "in", TokenKind::Identifier(Identifier::In)),
        ]) {
            let binding = if let TokenKind::Identifier(Identifier::Custom(binding_name)) =
                tokens.get("binding").unwrap().clone().kind
            {
                binding_name
            } else {
                unreachable!()
            };

            let iterator = self.parse_range(indent)?;

            match self.advance().kind {
                TokenKind::Colon => {}
                kind => return Err(format!("missing ':' after for expression, found {kind:?}")),
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
                        expressions: vec![expr],
                    }
                }
            };

            Ok(Expression::For(For {
                binding,
                iterator: Box::new(iterator),
                body,
            }))
        } else {
            return Err(format!("Invalid for loop construction"));
        }
    }

    pub fn parse_if(&mut self, indent: usize) -> Result<Expression, String> {
        // consume if
        self.advance();

        let check = self.parse_expression(indent)?;

        match self.advance().kind {
            TokenKind::Colon => {}
            kind => return Err(format!("missing ':' after if expression, found {kind:?}")),
        }

        // consume nl
        let true_branch = match self.peek(0).kind {
            TokenKind::Newline => {
                self.advance();
                self.parse_codeblock(indent)?
            }
            TokenKind::Identifier(Identifier::If) => {
                return Err(format!(
                    "Nested if blocks have to be on a new line and indented"
                ))
            }
            _ => {
                let expr = self.parse_codeblock_expression(indent)?;

                if TokenKind::Newline == self.peek(0).kind {
                    self.advance();
                }

                CodeBlock {
                    indentation: indent,
                    expressions: vec![expr],
                }
            }
        };

        // else
        let else_branch = match (self.peek(0).kind, self.peek(1).kind) {
            (TokenKind::Indentation(indentation), TokenKind::Identifier(Identifier::Else))
                if indentation == indent =>
            {
                //consume indent and else
                self.advance();
                self.advance();

                // consume nl
                let else_branch = match self.peek(0).kind {
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
                            expressions: vec![expr],
                        }
                    }
                };

                Some(else_branch)
            }
            _ => None,
        };

        Ok(Expression::If(If {
            cond: Box::new(check),
            true_branch,
            else_branch,
        }))
    }

    pub fn parse_struct_literal(&mut self, indent: usize) -> Result<Expression, String> {
        self.advance_skip_ws(indent);

        let mut struct_literal = AnonStruct {
            fields: HashMap::new(),
        };

        loop {
            let field_name = match self.advance_skip_ws(indent).kind {
                TokenKind::Identifier(Identifier::Custom(field_name)) => field_name,
                _ => return Err(format!("Unexpected token, expected struct field name")),
            };

            match self.advance_skip_ws(indent).kind {
                TokenKind::Colon => {}
                _ => return Err(format!("Unexpected token, expected struct field name")),
            };

            let field_val = self.parse_expression(indent)?;

            struct_literal.fields.insert(field_name, field_val);

            let token = self.peek_skip_ws(indent)?;
            match token.kind {
                TokenKind::CurlyRight => {
                    self.advance_skip_ws(indent);
                    break;
                }
                TokenKind::Comma => {
                    self.advance_skip_ws(indent);
                    // allow for trailing comma
                    if let TokenKind::CurlyRight = self.peek_skip_ws(indent)?.kind {
                        self.advance_skip_ws(indent);
                        break;
                    }
                }
                _ => return Err(format!("Invalid token in struct literal body")),
            }
        }

        Ok(Expression::AnonStruct(struct_literal))
    }

    pub fn parse_expression(&mut self, indent: usize) -> Result<Expression, String> {
        match self.peek_skip_ws(indent)?.kind {
            TokenKind::Identifier(Identifier::If) => self.parse_if(indent),
            TokenKind::Identifier(Identifier::For) => self.parse_for(indent),
            TokenKind::TripleDot => {
                self.advance();
                Ok(Expression::Placeholder)
            }
            TokenKind::Identifier(Identifier::Break) => {
                self.advance();
                Ok(Expression::Break)
            }
            TokenKind::JS => self.parse_js(indent),
            TokenKind::CurlyLeft => self.parse_struct_literal(indent),
            TokenKind::Identifier(Identifier::Continue) => {
                self.advance();
                Ok(Expression::Continue)
            }
            _ => self.parse_equality(indent),
        }
    }

    pub fn parse_codeblock(&mut self, original_indent: usize) -> Result<CodeBlock, String> {
        let mut block = CodeBlock {
            indentation: original_indent,
            expressions: Vec::new(),
        };

        self.advance_skip_ws(original_indent);
        self.current -= 2;

        block.indentation = match self.peek(0).kind {
            TokenKind::Indentation(indent) if indent > original_indent => indent,
            _ => return Err(format!("Codeblock body must be indented")),
        };

        loop {
            match (self.peek(0).kind, self.peek(1).kind) {
                (TokenKind::Indentation(_), TokenKind::Newline)
                | (TokenKind::Indentation(_), TokenKind::EOF) => {
                    // consume indent and nl
                    self.advance();
                    self.advance();
                    continue;
                }
                (TokenKind::Indentation(indent), _) => {
                    if indent < block.indentation {
                        break;
                    }
                    if indent > block.indentation {
                        return Err(format!("Code block has inconsistent indentation"));
                    }
                }
                (_, _) => break,
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
                kind => {}
            }
        }

        Ok(block)
    }

    pub fn parse_assignment_or_call(&mut self, indent: usize) -> Result<Expression, String> {
        let start_curr = self.current;

        let term = self.parse_assignment(indent);

        match term {
            Ok(_) => return term,
            Err(_) => {}
        };

        // roll back
        self.current = start_curr;

        self.parse_expression(indent)
    }

    pub fn parse_assignment(&mut self, indent: usize) -> Result<Expression, String> {
        let lhs = self.parse_term(indent)?;
        match self.peek(0).kind {
            TokenKind::Equal => {
                if let TokenKind::Equal = self.advance().kind {
                } else {
                    return Err(format!("missing = in assignment expr"));
                }

                let rhs = self.parse_expression(indent)?;

                Ok(Expression::Assignment(Assignment {
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                }))
            }
            TokenKind::PlusEqual
            | TokenKind::MinusEqual
            | TokenKind::MultEqual
            | TokenKind::DivEqual => {
                let op = match self.advance().kind {
                    TokenKind::PlusEqual => BinaryOperation::Add,
                    TokenKind::MinusEqual => BinaryOperation::Subtract,
                    TokenKind::MultEqual => BinaryOperation::Multiply,
                    TokenKind::DivEqual => BinaryOperation::Divide,
                    _ => return Err(format!("Invalid assignment operator")),
                };

                let rhs = self.parse_expression(indent)?;

                Ok(Expression::Assignment(Assignment {
                    lhs: Box::new(lhs.clone()),
                    rhs: Box::new(Expression::BinaryOp(BinaryOp {
                        op,
                        lhs: Box::new(lhs),
                        rhs: Box::new(rhs),
                    })),
                }))
            }
            _ => return Err(format!("Invalid assignment operator")),
        }
    }

    pub fn parse_codeblock_expression(&mut self, indent: usize) -> Result<Expression, String> {
        match self.peek(0).kind {
            TokenKind::Identifier(Identifier::Let) | TokenKind::Identifier(Identifier::Mut) => {
                self.parse_variable_decl(indent)
            }
            TokenKind::Identifier(Identifier::Return) => {
                // consume return
                self.advance();
                let expr = self.parse_expression(indent)?;
                Ok(Expression::Return(Box::new(expr)))
            }
            TokenKind::Identifier(Identifier::Custom(_)) => self.parse_assignment_or_call(indent),
            _ => self.parse_expression(indent),
        }
    }

    pub fn parse_js(&mut self, indent: usize) -> Result<Expression, String> {
        // consume JS token
        self.advance();

        if let TokenKind::ParenLeft = self.advance_skip_ws(indent).kind {
        } else {
            return Err(format!("Couldnt find js source code after @JS"));
        }

        let mut expressions = Vec::new();
        let expr = match self.peek_skip_ws(indent)?.kind {
            TokenKind::Literal(Literal::String(code)) => {
                self.advance_skip_ws(indent);
                Expression::Literal(Literal::String(code))
            }
            TokenKind::Identifier(Identifier::Custom(iden)) => {
                self.advance_skip_ws(indent);
                Expression::Variable(Variable { name: iden })
            }
            _ => {
                return Err(format!(
                    "Source code after @js must have at least one element"
                ));
            }
        };

        expressions.push(expr);

        loop {
            let expr = match self.peek_skip_ws(indent)?.kind {
                TokenKind::ParenRight => {
                    self.advance_skip_ws(indent);
                    break;
                }
                TokenKind::Literal(Literal::String(code)) => {
                    self.advance_skip_ws(indent);
                    Expression::Literal(Literal::String(code))
                }
                TokenKind::Identifier(Identifier::Custom(iden)) => {
                    self.advance_skip_ws(indent);
                    Expression::Variable(Variable { name: iden })
                }
                _ => {
                    return Err(format!("Source code after @js doesn't have a ')'"));
                }
            };

            expressions.push(expr);
        }

        Ok(Expression::JS(expressions))
    }

    pub fn parse_import(&mut self) -> Result<ImportStmt, String> {
        // consume `use`
        self.advance();

        let mut imports = Vec::new();

        let module_name = match self.advance().kind {
            TokenKind::Identifier(Identifier::Custom(file)) => file,
            _ => return Err(format!("Missing file in use statement")),
        };

        match self.peek(0).kind {
            TokenKind::Newline => {
                self.advance();

                return Ok(ImportStmt {
                    module_name,
                    imports,
                    everything: true,
                });
            }
            _ => {}
        };

        match self.advance().kind {
            TokenKind::CurlyLeft => {}
            _ => return Err(format!("Missing '{{' in use statement")),
        }

        loop {
            let name = match self.advance_skip_ws(0).kind {
                TokenKind::Identifier(Identifier::Custom(iden)) => iden,
                token => return Err(format!("Invalid token in use statement body {token:?}")),
            };

            let alias = match self.peek(0).kind {
                TokenKind::Identifier(Identifier::As) => {
                    self.advance();
                    match self.advance().kind {
                        TokenKind::Identifier(Identifier::Custom(iden)) => Some(iden),
                        _ => return Err(format!("Invalid token used for import alias")),
                    }
                }
                _ => None,
            };

            imports.push(Imported { name, alias });

            let token = self.peek_skip_ws(0)?;
            match token.kind {
                TokenKind::CurlyRight => {
                    self.advance_skip_ws(0);
                    break;
                }
                TokenKind::Comma => {
                    self.advance_skip_ws(0);
                    // allow for trailing ,
                    if let TokenKind::CurlyRight = self.peek_skip_ws(0)?.kind {
                        self.advance_skip_ws(0);
                        break;
                    }
                }
                _ => return Err(format!("Invalid token in use statement body")),
            }
        }

        Ok(ImportStmt {
            module_name,
            imports,
            everything: false,
        })
    }

    pub fn parse_type_def(&mut self) -> Result<TypeDef, String> {
        let export = match self.peek(0).kind {
            TokenKind::Identifier(Identifier::Export) => {
                self.advance();
                true
            }
            _ => false,
        };

        match self.advance().kind {
            TokenKind::Identifier(Identifier::Type) => {}
            token => return Err(format!("No 'type' in type decl, found {token:?} instead")),
        };

        let type_name = match self.advance().kind {
            TokenKind::Identifier(Identifier::Custom(type_name)) => type_name,
            _ => return Err(format!("No type name provided in type decl")),
        };

        match self.advance().kind {
            TokenKind::Equal => {}
            _ => return Err(format!("Missing '=' in type decl")),
        }

        let value = match self.peek(0).kind {
            TokenKind::Newline => {
                self.advance();

                let block_indent = match self.peek(0).kind {
                    TokenKind::Indentation(indent) => indent,
                    _ => return Err(format!("type decl body must be indented")),
                };

                let mut struct_def = StructDef {
                    fields: Vec::new(),
                    methods: Vec::new(),
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
                            if indent < block_indent {
                                break;
                            }
                            if indent > block_indent {
                                return Err(format!("type decl has inconsistent indentation"));
                            }
                        }
                        (_, _) => break,
                    }

                    // consume indent
                    self.advance();

                    let field_name = match self.advance_skip_ws(0).kind {
                        TokenKind::Identifier(Identifier::Custom(field_name)) => field_name,
                        _ => return Err(format!("field name missing in function decl")),
                    };

                    // match self.advance().kind {
                    //     TokenKind::Colon => {}
                    //     _ => return Err(format!("colon missing in function field decl")),
                    // };

                    let field_type = self.parse_type()?;

                    match self.peek(0).kind {
                        TokenKind::Newline => {
                            self.advance();
                        }
                        _ => {}
                    };

                    struct_def.fields.push(StructField {
                        field_name,
                        field_type,
                        is_final: false,
                        default_value: None,
                    });
                }

                Type {
                    type_kind: TypeKind::Struct(struct_def),
                    is_reference: false,
                    is_structural: false,
                }
            }
            _ => self.parse_type()?,
        };

        Ok(TypeDef {
            name: type_name,
            export,
            value,
        })
    }

    pub fn parse_file(&mut self, file_name: String) -> Result<Vec<Module>, String> {
        let mut modules = Vec::new();
        self.modules_to_parse.push(file_name);

        while let Some(module_name) = self.modules_to_parse.pop() {
            self.current_module = module_name.clone();
            if self.parsed_modules.contains(&module_name) {
                continue;
            }

            let file_path = &self.path.join(format!("{}.fr", module_name.clone()));
            let mut lexer = Lexer::new(&file_path);
            let tokens = lexer.parse()?;
            self.tokens = tokens
                .into_iter()
                .filter(|t| t.kind != TokenKind::MultilineComment && t.kind != TokenKind::Comment)
                .collect::<Vec<_>>();

            self.current = 0;
            self.expr_start = 0;

            let mut current_module = Module {
                module_name,
                type_defs: Vec::new(),
                function_defs: Vec::new(),
                toplevel_scope: CodeBlock::default(),
            };

            while !self.is_at_end() {
                self.expr_start = self.current;
                let t = self.peek(0);
                match t.kind {
                    TokenKind::EOF => break,
                    TokenKind::ParenLeft => {
                        let expr = self.parse_expression(0)?;
                        current_module.toplevel_scope.expressions.push(expr);
                    }
                    TokenKind::DoubleColon => {
                        let func_def = self.parse_fn_with_args(&mut current_module)?;
                        current_module.function_defs.push(func_def);
                    }
                    TokenKind::Newline => {
                        self.advance();
                    }
                    TokenKind::Dollar => todo!(),
                    TokenKind::Indentation(_) => {
                        self.advance();
                    }
                    TokenKind::Literal(_) => {
                        let expr = self.parse_expression(0)?;
                        current_module.toplevel_scope.expressions.push(expr);
                    }
                    TokenKind::JS => {
                        let expr = self.parse_js(0)?;
                        current_module.toplevel_scope.expressions.push(expr);
                    }
                    TokenKind::Identifier(iden) => match iden {
                        Identifier::Type => {
                            let type_def = self.parse_type_def()?;
                            current_module.type_defs.push(type_def);
                        }
                        Identifier::Export => match self.peek(1).kind {
                            TokenKind::Identifier(Identifier::Type) => {
                                let type_def = self.parse_type_def()?;
                                current_module.type_defs.push(type_def);
                            }
                            TokenKind::Identifier(Identifier::Fn) => {
                                let func_def = self.parse_fn_no_args(Vec::new())?;
                                current_module.function_defs.push(func_def);
                            }
                            TokenKind::Identifier(Identifier::Let) => {
                                let var_decl = self.parse_variable_decl(0)?;
                                current_module.toplevel_scope.expressions.push(var_decl);
                            }
                            _ => return Err(format!("Invalid token after export")),
                        },
                        Identifier::Use => {
                            todo!("use statements dont work yet")
                            // let import = self.parse_import()?;
                            // module.imports.push(import);
                        }
                        Identifier::Fn => {
                            let func_def = self.parse_fn_no_args(Vec::new())?;
                            current_module.function_defs.push(func_def);
                        }
                        Identifier::Let => {
                            // TODO: dont allow function calls in top level let bindings
                            let expr = self.parse_variable_decl(0)?;
                            current_module.toplevel_scope.expressions.push(expr);
                        }
                        Identifier::Mut => {
                            panic!("Mutable global variables are yuck i think");
                            let expr = self.parse_variable_decl(0)?;
                            current_module.toplevel_scope.expressions.push(expr);
                        }

                        Identifier::If | Identifier::For => {
                            panic!("Top level statements are yuck");
                            let expr = self.parse_expression(0)?;
                            current_module.toplevel_scope.expressions.push(expr);
                        }
                        Identifier::Custom(iden) => {
                            panic!("Top level expressions are yuck");
                            let expr = self.parse_assignment_or_call(0)?;

                            current_module.toplevel_scope.expressions.push(expr);
                        }
                        _ => {
                            self.advance();
                        }
                    },
                    token => {
                        eprintln!(
                            "{:?}:{:?} - Unexpected {token:?}",
                            t.start_line, t.start_char
                        );
                        todo!();
                    }
                };
            }

            self.parsed_modules.push(current_module.module_name.clone());
            modules.push(current_module);
        }

        // add a main() method invocation at the end of the compiled module
        modules
            .first_mut()
            .unwrap()
            .toplevel_scope
            .expressions
            .push(Expression::FunctionCall(FunctionCall {
                func_name: "main".to_owned(),
                arguments: Vec::new(),
            }));

        Ok(modules)
    }
}
