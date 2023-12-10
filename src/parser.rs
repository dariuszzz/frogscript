use crate::lexer::{Token, TokenKind, Literal, Identifier};

#[derive(Debug, Clone)]
pub enum Type {
    Int,
    Uint,
    Float,
    String,
}

#[derive(Debug, Clone)]
pub struct Statement {

}

#[derive(Debug, Clone, Default)]
pub struct CodeBlock  {
    pub indentation: usize,
    pub statements: Vec<Statement>
}

#[derive(Debug, Clone)]
pub struct FunctionArgument {
    pub arg_name: String,
    pub arg_type: Type,
    pub is_implicit: bool,
    pub is_reference: bool,
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

    fn advance(&mut self) -> Token {
        self.current += 1;
        self.tokens.get(self.current - 1).unwrap().clone()
    }

    fn peek(&mut self) -> Option<Token> {
        if self.is_at_end() { return None }
        return self.tokens.get(self.current).and_then(|t| Some(t.clone()))
    }

    fn peek_next(&mut self) -> Option<Token> {
        if self.is_at_end() { return None }
        return self.tokens.get(self.current + 1).and_then(|t| Some(t.clone()))
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
        while let Some(t) = self.peek() {
            if until(t) { break }
            tokens.push(self.advance());
        }

        if self.is_at_end() {
            return Err("Token not found".to_owned());
        }

        return Ok(tokens)
    }

    fn parse_fn_with_args(&mut self, module: &mut Module, t: Token) -> Result<(), String> {

        let arg_list_tokens = self.collect_until(|token| token.kind == TokenKind::Identifier(crate::lexer::Identifier::Fn))?;

        let arg_tokens = arg_list_tokens.split(|token| token.kind == TokenKind::DoubleColon).collect::<Vec<_>>();

        let mut function_def = FunctionDef {
            export: false,
            func_name: String::new(),
            argument_list: Vec::new(),
            return_type: Type::Uint,
            function_body: CodeBlock::default()
        };

        for (arg_idx, arg) in arg_tokens.into_iter().enumerate() {

            let mut arg_iter = arg.iter();

            let mut arg_def = FunctionArgument {
                arg_name: String::new(),
                arg_type: Type::Uint,
                is_implicit: false,
                is_reference: false
            };

            match arg_iter.next().unwrap().clone().kind {
                TokenKind::Identifier(Identifier::Custom(name)) => arg_def.arg_name = name,
                _ => return Err("Invalid arg name".to_owned())
            };

            let _colon = arg_iter.next();

            // god save me
            if let Some(_) = arg_iter.clone().find(|t| t.kind == TokenKind::Identifier(Identifier::Float)) {
                arg_def.arg_type = Type::Float
            }
            if let Some(_) = arg_iter.clone().find(|t| t.kind == TokenKind::Identifier(Identifier::Int)) {
                arg_def.arg_type = Type::Int
            }
            if let Some(_) = arg_iter.clone().find(|t| t.kind == TokenKind::Identifier(Identifier::Uint)) {
                arg_def.arg_type = Type::Uint
            }
            if let Some(_) = arg_iter.clone().find(|t| t.kind == TokenKind::Identifier(Identifier::String)) {
                arg_def.arg_type = Type::String
            }
            // Will implement implicit sometime else
            // if let Some(_) = arg_iter.clone().find(|t| t.kind == TokenKind::Hash) {
            //     arg_def.is_implicit = true
            // }
            if let Some(_) = arg_iter.clone().find(|t| t.kind == TokenKind::Ampersand) {
                arg_def.is_reference = true
            }

            function_def.argument_list.push(arg_def);
        }

        // this doesnt work cuz args are collected with collect until Fn so this ends up as a part of the args
        if let Some(Token { kind: TokenKind::Identifier(Identifier::Export), .. }) = self.peek() {
            function_def.export = true;
            self.advance();
        }
        
        if let Some(Token { kind: TokenKind::Identifier(Identifier::Fn), .. }) = self.peek() {
            self.advance();
        } else {
            return Err("'fn' keyword missing in function def".to_owned())
        }

        if let Some(Token { kind: TokenKind::Identifier(Identifier::Custom(name)), .. }) = self.peek() {
            self.advance();
            function_def.func_name = name;
        } else {
            return Err("'fn' keyword missing in function def".to_owned());
        }

        if let Some(Token { kind: TokenKind::FatArrow, .. }) = self.peek() {
            self.advance();
        } else {
            return Err("'=>' missing in function def".to_owned());
        }

        module.function_defs.push(function_def);

        Ok(())
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
            let t = self.advance();
            match t.kind {
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
                TokenKind::DoubleColon => self.parse_fn_with_args(&mut module, t)?,
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
                TokenKind::Newline => {},
                TokenKind::TrianglePipe => todo!(),
                TokenKind::Dollar => todo!(),
                TokenKind::Indentation(_) => {},
                TokenKind::Literal(_) => todo!(),
                TokenKind::Identifier(e) => println!("{e:?}"),
                TokenKind::Hash => todo!(),
            }

        }

        Ok(module)
    }
}