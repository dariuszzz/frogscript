use std::{
    collections::HashMap,
    fs,
    ops::RangeBounds,
    path::{Path, PathBuf},
    slice::SliceIndex,
    time::Instant,
};

use crate::{Expression, Range};

#[derive(Clone, Debug, PartialEq)]
pub enum FStringPart {
    String(String),
    Code(Box<Expression>),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Literal {
    String(Vec<FStringPart>),
    Int(isize),
    Uint(usize),
    Float(f32),
    Boolean(bool),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Identifier {
    _MatchAnyCustom,
    Custom(String),
    Let,
    Mut,
    Final,
    Fn,
    Type,
    Enum,
    For,
    While,
    Break,
    Continue,
    Return,
    If,
    Else,
    Match,
    Use,
    Export,
    From,
    Env,
    As,
    In,
    Inline,
    Module,
}

#[derive(Clone, Debug, PartialEq)]
pub enum TokenKind {
    EOF,
    ParenLeft,
    ParenRight,
    CurlyLeft,
    CurlyRight,
    SquareLeft,
    SquareRight,
    AngleLeft,
    AngleRight,
    Comma,
    Colon,
    DoubleColon,
    Plus,
    PlusEqual,
    Mod,
    Star,
    LessEqual,
    GreaterEqual,
    EqualEqual,
    Equal,
    ThinArrow,
    FatArrow,
    Minus,
    MinusEqual,
    Slash,
    Comment,
    MultilineComment,
    Power,
    NotEqual,
    Dot,
    DoubleDot,
    DoubleDotEqual,
    TripleDot,
    Ampersand,
    Pipe,
    Caret,
    Tilde,
    RShift,
    LShift,
    Newline,
    TrianglePipe,
    Dollar,
    Hash,
    Exclamation,
    MultEqual,
    DivEqual,
    BuiltinJS,
    BuiltinType,
    Indentation(usize),

    StartString,
    StringPart(String),
    StopString,

    Literal(Literal),
    Identifier(Identifier),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub start_line: usize,
    pub start_char: usize,
    pub lexeme: String,
}

#[derive(Debug)]
pub enum NestedParsingCount {
    None,
    Count(i32),
}

impl NestedParsingCount {
    pub fn increment(&mut self) {
        match self {
            Self::None => *self = Self::Count(1),
            Self::Count(c) => *c = *c + 1,
        }
    }

    pub fn decrement(&mut self) {
        match self {
            Self::None => panic!("Unterminated string or comment"),
            Self::Count(c) => {
                *c = *c - 1;
                if *c == 0 {
                    *self = Self::None
                }
            }
        }
    }
}

pub struct Lexer {
    pub source_path: PathBuf,
    pub source_file: Vec<char>,
    pub tokens: Vec<Token>,
    pub current: usize,
    pub line: usize,
    pub line_char: usize,
    pub lexeme_start: usize,
    pub lexeme_start_line: usize,
    pub lexeme_start_line_char: usize,
    pub parsing_multiline_comment: NestedParsingCount,
    pub currently_in_string: NestedParsingCount,
    pub keyword_map: HashMap<&'static str, Identifier>,

    pub perf: bool,
}

impl Lexer {
    pub fn new(source_str: &str, path: &Path, perf: bool) -> Self {
        let source_file = source_str.chars().collect::<Vec<_>>();

        let keyword_map = HashMap::from([
            ("let", Identifier::Let),
            ("final", Identifier::Final),
            ("mut", Identifier::Mut),
            ("type", Identifier::Type),
            ("enum", Identifier::Enum),
            ("for", Identifier::For),
            ("while", Identifier::While),
            ("break", Identifier::Break),
            ("continue", Identifier::Continue),
            ("return", Identifier::Return),
            ("if", Identifier::If),
            ("else", Identifier::Else),
            ("match", Identifier::Match),
            ("use", Identifier::Use),
            ("export", Identifier::Export),
            ("from", Identifier::From),
            ("env", Identifier::Env),
            ("as", Identifier::As),
            ("fn", Identifier::Fn),
            ("in", Identifier::In),
            ("inline", Identifier::Inline),
            ("module", Identifier::Module),
        ]);

        Self {
            source_path: path.to_path_buf(),
            source_file,
            tokens: Vec::new(),
            current: 0,
            line: 1,
            line_char: 0,
            lexeme_start: 0,
            lexeme_start_line: 0,
            lexeme_start_line_char: 0,
            parsing_multiline_comment: NestedParsingCount::None,
            currently_in_string: NestedParsingCount::None,
            keyword_map,
            perf,
        }
    }

    fn is_at_end(&self) -> bool {
        self.current >= self.source_file.len()
    }

    fn advance(&mut self) -> char {
        self.current += 1;
        self.line_char += 1;
        let current_char = self.source_file.get(self.current - 1).unwrap();

        if *current_char == '\n' {
            self.line += 1;
            self.line_char = 0
        }

        return *current_char;
    }

    fn peek(&mut self) -> Option<char> {
        if self.is_at_end() {
            return None;
        }
        return self.source_file.get(self.current).cloned();
    }

    fn peek_next(&mut self) -> Option<char> {
        if self.current + 1 >= self.source_file.len() {
            return None;
        }
        return self.source_file.get(self.current + 1).cloned();
    }

    fn match_char(&mut self, expected: char) -> bool {
        if self.is_at_end() {
            return false;
        }
        if self.source_file.get(self.current).unwrap() != &expected {
            return false;
        }

        self.current += 1;
        return true;
    }

    fn match_word(&mut self, expected: &str) -> bool {
        let next_word = self
            .get_substring(self.current, self.current + expected.len())
            .unwrap();

        if next_word != expected {
            return false;
        }

        for i in 0..expected.len() {
            self.advance();
        }

        return true;
    }

    fn consume_until(&mut self, until: char) -> bool {
        while let Some(c) = self.peek() {
            if c == until {
                break;
            }
            self.advance();
        }

        if self.is_at_end() {
            return false;
        }

        self.advance();

        return true;
    }

    fn get_substring(&self, start: usize, end: usize) -> Option<String> {
        let chars = self.source_file.get(start..end).unwrap();

        return Some(chars.into_iter().collect());
    }

    fn add_token(&mut self, kind: TokenKind) {
        let token = Token {
            kind,
            start_line: self.lexeme_start_line,
            start_char: self.lexeme_start_line_char,
            lexeme: self.get_substring(self.lexeme_start, self.current).unwrap(),
        };

        self.tokens.push(token);
    }

    fn parse_multiline_comment(&mut self) -> Result<(), String> {
        self.parsing_multiline_comment.increment();
        while let (Some(c), Some(nc)) = (self.peek(), self.peek_next()) {
            if c == '/' && nc == '*' {
                self.parsing_multiline_comment.increment();
            }
            if c == '*' && nc == '/' {
                self.parsing_multiline_comment.decrement();

                match self.parsing_multiline_comment {
                    NestedParsingCount::None => break,
                    _ => {}
                }
            }
            self.advance();
        }

        match self.parsing_multiline_comment {
            NestedParsingCount::Count(count) if count != 0 => {
                Err(format!("Unterminated multiline comment"))
            }
            NestedParsingCount::None => {
                self.advance();
                self.advance();

                self.add_token(TokenKind::MultilineComment);

                Ok(())
            }
            _ => unreachable!(),
        }
    }

    fn parse_fstring_string_part(&mut self) -> Result<(), String> {
        let mut prev = self.source_file.get(self.current - 1).unwrap().clone();

        while let Some(c) = self.peek() {
            // TODO: Add escapes
            if prev != '\\' {
                if c == '{' {
                    break;
                }
                if c == '"' {
                    break;
                }
            }

            prev = self.advance();
        }

        if self.is_at_end() {
            return Err(format!("Unterminated string (at EOF)"));
        }

        let string = self
            .get_substring(self.lexeme_start + 1, self.current)
            .unwrap();

        if !string.is_empty() {
            self.add_token(TokenKind::StringPart(string));
        }

        let last = self.advance();
        if '"' == last {
            self.add_token(TokenKind::StopString);
            self.currently_in_string.decrement();
        }

        Ok(())
    }

    fn parse_fstring(&mut self) -> Result<(), String> {
        self.add_token(TokenKind::StartString);
        self.currently_in_string.increment();

        self.parse_fstring_string_part()?;

        Ok(())
    }

    fn parse_number(&mut self) {
        while let Some(c) = self.peek() {
            if !c.is_ascii_digit() {
                break;
            }
            self.advance();
        }

        let mut literal_type = Literal::Int(0);

        if let (Some(c), Some(nc)) = (self.peek(), self.peek_next()) {
            if c == '.' && nc.is_ascii_digit() {
                literal_type = Literal::Float(0f32);
                self.advance();
                while let Some(c) = self.peek() {
                    if !c.is_ascii_digit() {
                        break;
                    }
                    self.advance();
                }
            }
        }

        let lexeme = self.get_substring(self.lexeme_start, self.current).unwrap();

        match &mut literal_type {
            Literal::Int(x) => *x = lexeme.parse::<isize>().unwrap(),
            Literal::Float(x) => *x = lexeme.parse::<f32>().unwrap(),
            _ => unreachable!(),
        }

        if let Some(c) = self.peek() {
            match c {
                'u' => {
                    literal_type = Literal::Uint(lexeme.parse::<usize>().unwrap());
                    self.advance();
                }
                'i' => {
                    literal_type = Literal::Int(lexeme.parse::<isize>().unwrap());
                    self.advance();
                }
                'f' => {
                    literal_type = Literal::Float(lexeme.parse::<f32>().unwrap());
                    self.advance();
                }
                _ => {}
            };
        }

        self.add_token(TokenKind::Literal(literal_type));
    }

    fn parse_identifier(&mut self) {
        let is_alpha = |c: char| c.is_ascii_alphanumeric() || c == '_';

        while let Some(c) = self.peek() {
            if !is_alpha(c) {
                break;
            }
            self.advance();
        }

        let lexeme = self.get_substring(self.lexeme_start, self.current).unwrap();

        if lexeme == "true" {
            self.add_token(TokenKind::Literal(Literal::Boolean(true)));
            return;
        } else if lexeme == "false" {
            self.add_token(TokenKind::Literal(Literal::Boolean(false)));
            return;
        }

        if let Some(kind) = self.keyword_map.get(lexeme.as_str()) {
            self.add_token(TokenKind::Identifier(kind.clone()));
        } else {
            self.add_token(TokenKind::Identifier(Identifier::Custom(lexeme.to_owned())));
        }
    }

    fn parse_indent(&mut self, c: char) {
        let mut indentation_level = if c == ' ' {
            1
        } else if c == '\t' {
            4
        } else {
            0
        };
        while let Some(c) = self.peek() {
            if c == ' ' {
                indentation_level += 1;
            } else if c == '\t' {
                indentation_level += 4;
            } else {
                break;
            }
            self.advance();
        }
        self.add_token(TokenKind::Indentation(indentation_level));
    }

    pub fn parse(&mut self) -> Result<Vec<Token>, String> {
        let start = Instant::now();

        while !self.is_at_end() {
            self.lexeme_start = self.current;
            self.lexeme_start_line = self.line;
            self.lexeme_start_line_char = self.line_char + 1;
            let c = self.advance();
            match c {
                '(' => self.add_token(TokenKind::ParenLeft),
                ')' => self.add_token(TokenKind::ParenRight),
                '{' => self.add_token(TokenKind::CurlyLeft),
                '}' => {
                    if let NestedParsingCount::Count(_) = self.currently_in_string {
                        self.parse_fstring_string_part()?;
                    } else {
                        self.add_token(TokenKind::CurlyRight)
                    }
                }
                '[' => self.add_token(TokenKind::SquareLeft),
                ']' => self.add_token(TokenKind::SquareRight),
                '<' => {
                    if self.match_char('=') {
                        self.add_token(TokenKind::LessEqual);
                    } else if self.match_char('<') {
                        self.add_token(TokenKind::LShift);
                    } else {
                        self.add_token(TokenKind::AngleLeft);
                    }
                }
                '>' => {
                    if self.match_char('=') {
                        self.add_token(TokenKind::GreaterEqual);
                    } else if self.match_char('>') {
                        self.add_token(TokenKind::RShift);
                    } else {
                        self.add_token(TokenKind::AngleRight);
                    }
                }
                '=' => {
                    if self.match_char('=') {
                        self.add_token(TokenKind::EqualEqual);
                    } else if self.match_char('>') {
                        self.add_token(TokenKind::FatArrow);
                    } else {
                        self.add_token(TokenKind::Equal);
                    }
                }
                '-' => {
                    if self.match_char('=') {
                        self.add_token(TokenKind::MinusEqual);
                    } else if self.match_char('>') {
                        self.add_token(TokenKind::ThinArrow);
                    } else {
                        self.add_token(TokenKind::Minus);
                    }
                }
                ',' => self.add_token(TokenKind::Comma),
                ':' => {
                    if self.match_char(':') {
                        self.add_token(TokenKind::DoubleColon)
                    } else {
                        self.add_token(TokenKind::Colon)
                    }
                }
                '+' => {
                    if self.match_char('=') {
                        self.add_token(TokenKind::PlusEqual);
                    } else {
                        self.add_token(TokenKind::Plus);
                    }
                }
                '%' => self.add_token(TokenKind::Mod),
                '*' => {
                    if self.match_char('*') {
                        self.add_token(TokenKind::Power);
                    }
                    if self.match_char('=') {
                        self.add_token(TokenKind::MultEqual);
                    } else {
                        self.add_token(TokenKind::Star);
                    }
                }
                '!' => {
                    if self.match_char('=') {
                        self.add_token(TokenKind::NotEqual);
                    } else {
                        self.add_token(TokenKind::Exclamation);
                    }
                }
                '/' => {
                    if self.match_char('/') {
                        if self.consume_until('\n') {
                            self.add_token(TokenKind::Comment);
                            self.add_token(TokenKind::Newline);
                        }
                    } else if self.match_char('*') {
                        self.parse_multiline_comment()?;
                    } else if self.match_char('=') {
                        self.add_token(TokenKind::DivEqual);
                    } else {
                        self.add_token(TokenKind::Slash);
                    }
                }
                '|' => {
                    if self.match_char('>') {
                        self.add_token(TokenKind::TrianglePipe)
                    } else {
                        self.add_token(TokenKind::Pipe)
                    }
                }
                '\n' => {
                    self.add_token(TokenKind::Newline);
                    if let Some(c) = self.peek() {
                        if !c.is_ascii_whitespace() {
                            self.add_token(TokenKind::Indentation(0));
                        }
                    }
                }
                '.' => {
                    if self.match_char('.') {
                        if self.match_char('.') {
                            self.add_token(TokenKind::TripleDot);
                        } else {
                            if self.match_char('=') {
                                self.add_token(TokenKind::DoubleDotEqual);
                            } else {
                                self.add_token(TokenKind::DoubleDot);
                            }
                        }
                    } else {
                        self.add_token(TokenKind::Dot)
                    }
                }
                '&' => self.add_token(TokenKind::Ampersand),
                '^' => self.add_token(TokenKind::Caret),
                '~' => self.add_token(TokenKind::Tilde),
                '$' => self.add_token(TokenKind::Dollar),
                '#' => self.add_token(TokenKind::Hash),
                '@' => {
                    if self.match_word("js") {
                        self.add_token(TokenKind::BuiltinJS)
                    }
                    if self.match_word("type") {
                        self.add_token(TokenKind::BuiltinJS)
                    }
                }
                '"' => self.parse_fstring()?,
                c if c.is_numeric() => self.parse_number(),
                c if c.is_ascii_alphabetic() || c == '_' => self.parse_identifier(),
                c if c.is_ascii_whitespace() => {
                    if self.line_char == 1 {
                        self.parse_indent(c);
                    }
                }
                c => {
                    return Err(format!(
                        "Unexpected char at {}:{} - {c}",
                        self.line, self.line_char
                    ))
                }
            }
        }

        if self.perf {
            println!(
                "\tLexing:  {}us\t{:?}",
                Instant::now().duration_since(start).as_micros(),
                self.source_path.file_name().unwrap()
            );
        }

        return Ok(self.tokens.clone());
    }
}
