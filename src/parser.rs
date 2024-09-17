use std::collections::HashMap;
use std::path::{Path, PathBuf};

use crate::lexer::{Identifier, Lexer, Literal, Token, TokenKind};
use crate::pond::Pond;
use crate::{ast::*, FStringPart};

#[derive(Debug, Clone, Default)]
pub struct Program {
    pub modules: Vec<Module>,
}

pub struct Parser {
    pub tokens: Vec<Token>,
    pub current: usize,
    pub expr_start: usize,
}

impl Parser {
    pub fn new() -> Self {
        Self {
            tokens: Vec::new(),
            current: 0,
            expr_start: 0,
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

    fn parse_fn_no_implicits(
        &mut self,
        args: Vec<FunctionArgument>,
    ) -> Result<FunctionDef, String> {
        let mut function_def = FunctionDef {
            export: false,
            func_name: String::new(),
            argument_list: args,
            return_type: Type::Infer,
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
                        arg_type: Type::Infer,
                        is_env: false,
                    };

                    match self.peek_skip_ws(0)?.kind {
                        TokenKind::Identifier(Identifier::Custom(arg_name)) => {
                            self.advance_skip_ws(0);
                            arg.arg_name = arg_name.clone();
                            arg.arg_type = self.parse_type()?;

                            match self.peek(0).kind {
                                TokenKind::Comma => {
                                    self.advance();
                                }
                                TokenKind::Newline => {
                                    self.advance_skip_ws(0);
                                    self.current -= 1;
                                }
                                _ => match self.peek_skip_ws(0)?.kind {
                                    TokenKind::ParenRight => {}
                                    _ => return Err(format!("Function args must be separated by either a comma or a newline"))
                                }
                            }

                            function_def.argument_list.push(arg);
                        }
                        TokenKind::ParenRight => {
                            self.advance_skip_ws(0);
                            break;
                        }
                        token => {
                            return Err(format!("Expected argument name or `)` got {token:?}"))
                        }
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
                "{line}:{pos} Missing tokens in '(export) fn funcname'",
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

    fn parse_fn_with_implicits(&mut self, module: &mut Module) -> Result<FunctionDef, String> {
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
                arg_type: Type::Uint,
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

        self.parse_fn_no_implicits(argument_list)
    }

    pub fn parse_type(&mut self) -> Result<Type, String> {
        let mut type_ = Type::Infer;

        type_ = match self.peek(0).kind {
            TokenKind::Ampersand => {
                self.advance();
                Type::Reference(Box::new(self.parse_type()?))
            }
            TokenKind::Tilde => {
                self.advance();
                Type::Structural(Box::new(self.parse_type()?))
            }
            TokenKind::Identifier(Identifier::Custom(type_name)) => {
                self.advance();
                if type_name == "_" {
                    Type::Infer
                } else {
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

                    let name = path.join("::");

                    match name.as_str() {
                        "bool" => Type::Boolean,
                        "string" => Type::String,
                        "float" => Type::Float,
                        "int" => Type::Int,
                        "uint" => Type::Uint,
                        "any" => Type::Any,
                        _ => Type::Custom(CustomType { name }),
                    }
                }
            }
            TokenKind::SquareRight => {
                return Err(format!("Empty array type"));
            }
            TokenKind::SquareLeft => {
                self.advance();

                let arr_type = self.parse_type()?;

                if let TokenKind::SquareRight = self.advance().kind {
                } else {
                    return Err(format!("Unclosed array type"));
                }

                Type::Array(Box::new(arr_type))
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
                        if let Type::Void = args1[0] {
                            args1 = Vec::new();
                        }
                    }

                    if args2.len() == 1 {
                        if let Type::Void = args2[0] {
                            args2 = Vec::new();
                        }
                    }

                    if were_there_2_arg_lists {
                        Type::Function(FunctionType {
                            env_args: args1,
                            args: args2,
                            ret: Box::new(return_type),
                        })
                    } else {
                        Type::Function(FunctionType {
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
                    Type::Void
                } else {
                    return Err(format!(
                        "{}:{} Unexpected token after '(' in type",
                        token.start_line, token.start_char
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
                TokenKind::Equal => Type::Infer,
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
            self.advance();
            let mut call = FunctionCall {
                func_expr: Box::new(Expression::Variable(Variable {
                    name: name.join("::"),
                })),
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
        expr: Expression,
        indent: usize,
    ) -> Result<Expression, String> {
        let mut call = FunctionCall {
            func_expr: Box::new(expr),
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

            // FIXME: goofy ahh way to get ranges working, this shouldnt happen in the parser
            lhs = Expression::FunctionCall(FunctionCall {
                func_expr: Box::new(Expression::Variable(Variable {
                    name: "core::range".to_owned(),
                })),
                arguments: vec![
                    lhs,
                    if inclusive {
                        Expression::BinaryOp(BinaryOp {
                            op: BinaryOperation::Add,
                            lhs: Box::new(rhs),
                            rhs: Box::new(Expression::Literal(Literal::Int(1))),
                        })
                    } else {
                        rhs
                    },
                ],
            });

            // lhs = Expression::Range(Range {
            //     start: Box::new(lhs),
            //     end: Box::new(rhs),
            //     inclusive,
            // });
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
                TokenKind::Exclamation => {
                    let term = self.parse_term(indent)?;

                    Expression::UnaryOp(UnaryOp {
                        op: UnaryOperation::Negate,
                        operand: Box::new(term),
                    })
                }
                TokenKind::StartString => self.parse_string(indent)?,
                TokenKind::Literal(literal) => self.parse_literal(literal, indent)?,
                TokenKind::ParenLeft => self.parse_expr_in_parentheses(indent)?,
                TokenKind::Identifier(Identifier::Custom(name)) => {
                    self.parse_custom_iden(name, indent)?
                }
                TokenKind::Identifier(Identifier::Fn) => self.parse_lambda(indent)?,
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
            term = match token.kind {
                TokenKind::ParenLeft => self.parse_standalone_function_call(term, indent)?,
                TokenKind::Dot => {
                    self.advance_skip_ws(indent);
                    self.parse_method_call_or_field_access(term, indent)?
                }
                TokenKind::SquareLeft => {
                    self.advance_skip_ws(indent);
                    self.parse_array_access(term, indent)?
                }
                _ => break,
            };
        }

        Ok(term)
    }

    pub fn parse_lambda(&mut self, indent: usize) -> Result<Expression, String> {
        let mut lambda = Lambda {
            argument_list: Vec::new(),
            return_type: Type::Infer,
            function_body: CodeBlock::default(),
        };

        match self.advance().kind {
            TokenKind::ParenLeft => {}
            _ => return Err(format!("'(' missing after 'fn' in lambda decl")),
        }

        loop {
            let mut arg = FunctionArgument {
                arg_name: String::new(),
                arg_type: Type::Infer,
                is_env: false,
            };

            match self.peek_skip_ws(0)?.kind {
                TokenKind::Identifier(Identifier::Custom(arg_name)) => {
                    self.advance_skip_ws(0);
                    arg.arg_name = arg_name.clone();

                    if let Ok(arg_type) = self.parse_type() {
                        arg.arg_type = arg_type;
                    }

                    match self.peek(0).kind {
                        TokenKind::Comma => {
                            self.advance();
                        }
                        TokenKind::Newline => {
                            self.advance_skip_ws(0);
                            self.current -= 1;
                        }
                        _ => match self.peek_skip_ws(0)?.kind {
                            TokenKind::ParenRight => {}
                            _ => {
                                return Err(format!(
                                    "Lambda args must be separated by either a comma or a newline"
                                ))
                            }
                        },
                    }

                    lambda.argument_list.push(arg);
                }
                TokenKind::ParenRight => {
                    self.advance_skip_ws(0);
                    break;
                }
                _ => unreachable!(),
            }
        }

        if let TokenKind::ThinArrow = self.peek(0).kind {
            self.advance();
            lambda.return_type = self.parse_type()?;
        }

        match self.peek(0) {
            Token {
                kind: TokenKind::Newline,
                ..
            } => {
                //consume nl
                self.advance();

                let block = self.parse_codeblock(0)?;
                lambda.function_body = block;
            }
            _ => {
                let expr = self.parse_codeblock_expression(0)?;
                lambda.function_body.expressions.push(expr);
            }
        }

        Ok(Expression::Lambda(lambda))
    }

    pub fn parse_array_literal(&mut self, indent: usize) -> Result<Expression, String> {
        let mut array = ArrayLiteral {
            elements: Vec::new(),
        };

        let token = self.peek_skip_ws(indent)?;
        match token.kind {
            TokenKind::SquareRight => {
                self.advance_skip_ws(indent);
                return Ok(Expression::ArrayLiteral(array));
            }
            _ => {}
        }

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

    pub fn parse_string(&mut self, indent: usize) -> Result<Expression, String> {
        let mut parts = Vec::new();
        loop {
            let token = self.peek(0);
            match token.kind {
                TokenKind::StopString => {
                    self.advance();
                    break;
                }
                TokenKind::StringPart(string) => {
                    self.advance();
                    parts.push(FStringPart::String(string));
                }
                TokenKind::EOF => return Err(format!("Unterminated string (parsing)")),
                kind => {
                    let expr = self.parse_expression(indent)?;
                    parts.push(FStringPart::Code(Box::new(expr)))
                }
            };
        }

        return Ok(Expression::Literal(Literal::String(parts)));
    }

    pub fn parse_literal(&mut self, literal: Literal, indent: usize) -> Result<Expression, String> {
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

        // match self.peek(0) {
        //     Token {
        //         kind: TokenKind::Dot,
        //         ..
        //     } => {
        //         self.advance();
        //         self.parse_method_call_or_field_access(expr, indent)
        //     }
        //     Token {
        //         kind: TokenKind::SquareLeft,
        //         ..
        //     } => {
        //         self.advance();
        //         self.parse_array_access(expr, indent)
        //     }
        //     _ => Ok(expr),
        // }
        Ok(expr)
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

        let final_name = path.join("::");
        let func_expr = Expression::Variable(Variable {
            name: final_name.clone(),
        });

        let expr = match self.peek_skip_ws(0)?.kind {
            TokenKind::ParenLeft => self.parse_standalone_function_call(func_expr, indent)?,
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
        if let TokenKind::Identifier(Identifier::For) = self.advance().kind {
            let binding_type = match self.peek(1).kind {
                TokenKind::Identifier(Identifier::In) => Type::Infer,
                _ => self.parse_type()?,
            };

            let binding = match self.advance().kind {
                TokenKind::Identifier(Identifier::Custom(binding_name)) => binding_name,
                _ => return Err(format!("Invalid or missing binding in for loop")),
            };

            match self.advance().kind {
                TokenKind::Identifier(Identifier::In) => {}
                _ => return Err(format!("Expected 'in' keyword after for loop binding")),
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
                binding_type,
                iterator: Box::new(iterator),
                body,
            }))
        } else {
            return Err(format!("Expected for keyword"));
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

            let field_value = match self.peek_skip_ws(indent)?.kind {
                TokenKind::Colon => {
                    self.advance_skip_ws(indent);
                    self.parse_expression(indent)?
                }
                TokenKind::Comma | TokenKind::CurlyRight => Expression::Variable(Variable {
                    name: field_name.clone(),
                }),
                _ => {
                    return Err(format!(
                        "Unexpected token, expected struct field value, comma or right curly"
                    ))
                }
            };

            struct_literal.fields.insert(field_name, field_value);

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
            TokenKind::Identifier(Identifier::Break) => Ok(Expression::Break),
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
                (TokenKind::Newline, _) => {
                    self.advance();
                    continue;
                }
                (TokenKind::Indentation(_), TokenKind::Newline)
                | (TokenKind::Indentation(_), TokenKind::EOF) => {
                    // consume indent and nl
                    self.advance();
                    self.advance();
                    continue;
                }
                (TokenKind::Indentation(indent), smth) => {
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
            // println!("{:?}", expr);

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
            TokenKind::Identifier(Identifier::Use) => self.parse_import(),
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
            return Err(format!("Couldnt find lparen after @JS"));
        }

        if let TokenKind::StartString = self.advance_skip_ws(indent).kind {
        } else {
            return Err(format!("Couldnt find js source code after @JS"));
        }

        let expr = self.parse_string(indent)?;

        if let TokenKind::ParenRight = self.advance_skip_ws(indent).kind {
        } else {
            return Err(format!("Couldnt find end of js source code after @JS"));
        }

        Ok(Expression::JS(Box::new(expr)))
    }

    pub fn parse_import(&mut self) -> Result<Expression, String> {
        // consume `use`
        self.advance();

        let module_name = match self.advance().kind {
            TokenKind::Identifier(Identifier::Custom(part)) => {
                let mut module_path = vec![part];

                while let TokenKind::DoubleColon = self.peek(0).kind {
                    self.advance();
                    match self.peek(0).kind {
                        TokenKind::Identifier(Identifier::Custom(iden)) => {
                            module_path.push(iden);
                            self.advance();
                        }
                        _ => return Err(format!("Missing module name after ::")),
                    }
                }

                module_path.join("::")
            }
            _ => return Err(format!("Missing module name in use statement")),
        };

        match self.peek(0).kind {
            TokenKind::Newline => {
                self.advance();

                return Ok(Expression::Import(Import {
                    module_name,
                    alias: None,
                }));
            }
            _ => {}
        };

        match self.advance().kind {
            TokenKind::Identifier(Identifier::As) => {
                let alias = match self.advance().kind {
                    TokenKind::Identifier(Identifier::Custom(alias)) => alias,
                    _ => return Err(format!("Missing use statement alias")),
                };

                return Ok(Expression::Import(Import {
                    module_name,
                    alias: Some(alias),
                }));
            }
            kind => {
                return Err(format!(
                    "Invalid token after use statement, expected `as` got {kind:?}"
                ))
            }
        }

        // loop {
        //     let name = match self.advance_skip_ws(0).kind {
        //         TokenKind::Identifier(Identifier::Custom(iden)) => iden,
        //         token => return Err(format!("Invalid token in use statement body {token:?}")),
        //     };

        //     let alias = match self.peek(0).kind {
        //         TokenKind::Identifier(Identifier::As) => {
        //             self.advance();
        //             match self.advance().kind {
        //                 TokenKind::Identifier(Identifier::Custom(iden)) => Some(iden),
        //                 _ => return Err(format!("Invalid token used for import alias")),
        //             }
        //         }
        //         _ => None,
        //     };

        //     imports.push(Imported { name, alias });

        //     let token = self.peek_skip_ws(0)?;
        //     match token.kind {
        //         TokenKind::CurlyRight => {
        //             self.advance_skip_ws(0);
        //             break;
        //         }
        //         TokenKind::Comma => {
        //             self.advance_skip_ws(0);
        //             // allow for trailing ,
        //             if let TokenKind::CurlyRight = self.peek_skip_ws(0)?.kind {
        //                 self.advance_skip_ws(0);
        //                 break;
        //             }
        //         }
        //         _ => return Err(format!("Invalid token in use statement body")),
        //     }
        // }

        // Ok(ImportStmt {
        //     module_name,
        //     imports,
        //     everything: false,
        // })
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

                let mut struct_def = StructDef { fields: Vec::new() };

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
                    });
                }

                Type::Struct(struct_def)
            }
            _ => self.parse_type()?,
        };

        Ok(TypeDef {
            name: type_name,
            export,
            underlying_ty: value,
        })
    }

    fn parse_module(
        &mut self,
        original_indent: usize,
        curr_module_name: &str,
        modules: &mut Vec<Module>,
    ) -> Result<(), String> {
        let mut current_module = Module {
            module_name: curr_module_name.to_string(),
            ..Default::default()
        };

        if original_indent != 0 {
            self.advance_skip_ws(original_indent);
            self.current -= 2;
        }

        let curr_indent = match self.peek(0).kind {
            TokenKind::Indentation(indent) if indent > original_indent => indent,
            _ if original_indent != 0 => return Err(format!("Module must be indented")),
            _ => 0,
        };

        loop {
            self.expr_start = self.current;
            let t = self.peek(0);
            let next = self.peek(1);
            match t.kind {
                TokenKind::EOF => break,
                TokenKind::ParenLeft => {
                    let expr = self.parse_expression(curr_indent)?;
                    current_module.toplevel_scope.expressions.push(expr);
                }
                TokenKind::DoubleColon => {
                    let func_def = self.parse_fn_with_implicits(&mut current_module)?;
                    current_module.function_defs.push(func_def);
                }
                TokenKind::Newline => {
                    self.advance();
                }
                TokenKind::Dollar => todo!(),
                TokenKind::Indentation(indent) => {
                    if indent < curr_indent {
                        break;
                    }
                    if indent > curr_indent {
                        return Err(format!("Code block has inconsistent indentation"));
                    }
                    self.advance();
                }
                TokenKind::Literal(_) => {
                    let expr = self.parse_expression(curr_indent)?;
                    current_module.toplevel_scope.expressions.push(expr);
                }
                TokenKind::JS => {
                    let expr = self.parse_js(curr_indent)?;
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
                            let func_def = self.parse_fn_no_implicits(Vec::new())?;
                            current_module.function_defs.push(func_def);
                        }
                        TokenKind::Identifier(Identifier::Let) => {
                            let var_decl = self.parse_variable_decl(curr_indent)?;
                            current_module.toplevel_scope.expressions.push(var_decl);
                        }
                        _ => return Err(format!("Invalid token after export")),
                    },
                    Identifier::Module => {
                        //consume module iden
                        self.advance();
                        let module_name = match self.advance().kind {
                            TokenKind::Identifier(Identifier::Custom(name)) => name,
                            _ => {
                                return Err(
                                    "Unexpected identifier, expected module name".to_string()
                                )
                            }
                        };

                        if !matches!(self.advance().kind, TokenKind::Equal) {
                            return Err(
                                "Unexpected token expected `=` after module name".to_string()
                            );
                        }

                        if !matches!(self.advance().kind, TokenKind::Newline) {
                            return Err(
                                "Unexpected token expected `\n` after module statement".to_string()
                            );
                        }

                        self.parse_module(
                            curr_indent,
                            &format!("{curr_module_name}::{module_name}"),
                            modules,
                        )?;
                    }
                    Identifier::Use => {
                        let import = self.parse_import()?;
                        current_module.toplevel_scope.expressions.push(import);
                    }
                    Identifier::Fn => {
                        let func_def = self.parse_fn_no_implicits(Vec::new())?;
                        current_module.function_defs.push(func_def);
                    }
                    Identifier::Let => {
                        // TODO: dont allow function calls in top level let bindings
                        let expr = self.parse_variable_decl(curr_indent)?;
                        current_module.toplevel_scope.expressions.push(expr);
                    }
                    Identifier::Mut => {
                        panic!("Mutable global variables are yuck i think");
                        let expr = self.parse_variable_decl(curr_indent)?;
                        current_module.toplevel_scope.expressions.push(expr);
                    }

                    Identifier::If | Identifier::For => {
                        panic!("Top level statements are yuck");
                        let expr = self.parse_expression(curr_indent)?;
                        current_module.toplevel_scope.expressions.push(expr);
                    }
                    Identifier::Custom(iden) => {
                        println!("{}:{} -> {iden:?}", t.start_line, t.start_char);
                        panic!("Top level expressions are yuck");
                        let expr = self.parse_assignment_or_call(curr_indent)?;

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

        modules.push(current_module);

        Ok(())
    }

    pub fn parse_file(&mut self, pond_name: &str, file_path: &Path) -> Result<Vec<Module>, String> {
        let mut lexer = Lexer::new(&file_path);
        let tokens = lexer.parse()?;
        self.tokens = tokens
            .into_iter()
            .filter(|t| t.kind != TokenKind::MultilineComment && t.kind != TokenKind::Comment)
            .collect::<Vec<_>>();

        self.current = 0;
        self.expr_start = 0;

        let mut modules = vec![];

        while !self.is_at_end() {
            self.parse_module(0, pond_name, &mut modules)?;
        }

        Ok(modules)
    }

    pub fn parse_pond(&mut self, pond: &Pond) -> Result<Vec<Module>, String> {
        let files = pond.get_pond_files()?;

        let mut modules: Vec<Module> = Vec::new();
        for file in &files {
            let mut file_modules = self.parse_file(&pond.name, file)?;
            modules.append(&mut file_modules)
        }

        //merge modules
        let mut merged_modules: Vec<Module> = Vec::new();
        for mut module in modules {
            let existing_mod = merged_modules
                .iter_mut()
                .find(|m| m.module_name == module.module_name);

            match existing_mod {
                Some(existing_mod) => {
                    existing_mod.function_defs.append(&mut module.function_defs);
                    existing_mod.type_defs.append(&mut module.type_defs);
                    existing_mod
                        .toplevel_scope
                        .expressions
                        .append(&mut module.toplevel_scope.expressions)
                }
                None => {
                    merged_modules.push(module);
                }
            }
        }

        Ok(merged_modules)
    }
}
