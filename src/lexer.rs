use std::collections::HashMap;


#[derive(Clone, Debug, PartialEq)]
pub enum Literal {
    String(String),
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
    Implicit,
    As,
    In,
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
    NoneType,
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
    Tab,
    Newline,
    TrianglePipe,
    Dollar,
    Hash,
    Indentation(usize),
    
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
    Count(i32)
}

impl NestedParsingCount {
    pub fn increment(&mut self) {
        match self {
            Self::None => {},
            Self::Count(c) => *c = *c + 1
        }
    }

    pub fn decrement(&mut self) {
        match self {
            Self::None => {},
            Self::Count(c) => *c = *c - 1
        }
    }
}


pub struct Lexer {
    pub source_file: String,
    pub tokens: Vec<Token>,
    pub current: usize,
    pub line: usize,
    pub line_char: usize,
    pub lexeme_start: usize,
    pub lexeme_start_line: usize,
    pub lexeme_start_line_char: usize,
    pub parsing_multiline_comment: NestedParsingCount,
}

impl Lexer {
    pub fn new(source_file: String) -> Self {
        Self { 
            source_file,
            tokens: Vec::new(),
            current: 0,
            line: 1,
            line_char: 0,
            lexeme_start: 0,
            lexeme_start_line: 0,
            lexeme_start_line_char: 0,
            parsing_multiline_comment: NestedParsingCount::None,
        }
    }

    fn is_at_end(&self) -> bool {
        self.current >= self.source_file.len()
    }

    fn advance(&mut self) -> char {
        self.current += 1;
        self.line_char += 1;
        let current_char = self.source_file.chars().skip(self.current - 1).next().unwrap();

        if current_char == '\n' { self.line += 1; self.line_char = 0 }

        return current_char
    }     

    fn peek(&mut self) -> Option<char> {
        if self.is_at_end() { return None }
        return self.source_file.chars().skip(self.current).next()
    }

    fn peek_next(&mut self) -> Option<char> {
        if self.current + 1 >= self.source_file.len() { return None }
        return self.source_file.chars().skip(self.current + 1).next()
    }

    fn match_char(&mut self, expected: char) -> bool {
        if self.is_at_end() { return false }
        if self.source_file.chars().skip(self.current).next().unwrap() != expected { return false }

        self.current += 1;
        return true
        
    }

    fn consume_until(&mut self, until: char) -> bool {
        while let Some(c) = self.peek() {
            if c == until { break }
            self.advance();
        }

        if self.is_at_end() {
            return false;
        }

        self.advance();

        return true
    }

    fn add_token(&mut self, kind: TokenKind) {
        self.tokens.push(
            Token {
                kind,
                start_line: self.lexeme_start_line,
                start_char: self.lexeme_start_line_char,
                lexeme: self.source_file.get(self.lexeme_start..self.current).unwrap().to_owned()
            }
        );
    }

    fn parse_multiline_comment(&mut self) -> Result<(), String> {
        self.parsing_multiline_comment = NestedParsingCount::Count(1);
        while let (Some(c), Some(nc)) = (self.peek(), self.peek_next()) {
            if c == '/' && nc == '*' {
                self.parsing_multiline_comment.increment();
            }
            if c == '*' && nc == '/' {
                self.parsing_multiline_comment.decrement();

                match self.parsing_multiline_comment {
                    NestedParsingCount::Count(count) if count == 0 => break,
                    NestedParsingCount::Count(_) => {}
                    NestedParsingCount::None => unreachable!()
                }
            }
            self.advance();
        }

        match self.parsing_multiline_comment {
            NestedParsingCount::Count(count) if count != 0 => Err(format!("Unterminated multiline comment")),
            NestedParsingCount::Count(_) => {
                self.parsing_multiline_comment = NestedParsingCount::None;
                self.advance();
                self.advance();
        
                self.add_token(TokenKind::MultilineComment);

                Ok(())
            },
            NestedParsingCount::None => unreachable!()
        }
    }

    fn parse_string(&mut self) -> Result<(), String> {
        let starting_line = self.line;
        let starting_line_char = self.line_char;
        if self.consume_until('"') {
            let string = self.source_file.get((self.lexeme_start + 1)..(self.current - 1)).unwrap().to_owned();
            self.tokens.push(Token { 
                kind: TokenKind::Literal(Literal::String(string.clone())),
                start_char: self.lexeme_start_line_char,
                start_line: self.lexeme_start_line,
                lexeme: string 
            });

            return Ok(())
        } else {
            return Err(format!("Unterminated string"))
        }
    }

    fn parse_number(&mut self) {
        while let Some(c) = self.peek() {
            if !c.is_ascii_digit() {
                break 
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
                        break 
                    }
                    self.advance();
                }

            }
        }

        let lexeme = self.source_file.get(self.lexeme_start..self.current).unwrap().to_owned();       

        match &mut literal_type {
            Literal::Int(x) => *x = lexeme.parse::<isize>().unwrap(),
            Literal::Float(x) => *x = lexeme.parse::<f32>().unwrap(),
            _ => unreachable!()
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
                _ => {},
            };
        }

        self.add_token(TokenKind::Literal(literal_type));
    }
        
    fn parse_identifier(&mut self) {
        let is_alpha = |c: char| {
            c.is_ascii_alphanumeric() || c == '_'
        };

        let keywords = HashMap::from([
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
            ("implicit", Identifier::Implicit),
            ("as", Identifier::As),
            ("fn", Identifier::Fn),
            ("in", Identifier::In),
        ]);

        while let Some(c) = self.peek() {
            if !is_alpha(c) {
                break
            }
            self.advance();
        }

        let lexeme = self.source_file.get(self.lexeme_start..self.current).unwrap().to_owned();

        if lexeme == "true" {
            self.add_token(TokenKind::Literal(Literal::Boolean(true)));
            return
        } else if lexeme == "false" {
            self.add_token(TokenKind::Literal(Literal::Boolean(false)));
            return
        }
        
        if let Some(kind) = keywords.get(lexeme.as_str()) {
            self.add_token(TokenKind::Identifier(kind.clone()));
        } else {
            self.add_token(TokenKind::Identifier(Identifier::Custom(lexeme.to_owned())));
        }
    }

    fn parse_indent(&mut self, c: char) {
        let mut indentation_level = if c == ' ' { 1 } else if c == '\t' { 4 } else { 0 };
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
        while !self.is_at_end() {
            self.lexeme_start = self.current;
            self.lexeme_start_line = self.line;
            self.lexeme_start_line_char = self.line_char + 1;
            let c = self.advance();
            match c {
                '(' => self.add_token(TokenKind::ParenLeft),
                ')' => self.add_token(TokenKind::ParenRight),
                '{' => self.add_token(TokenKind::CurlyLeft),
                '}' => self.add_token(TokenKind::CurlyRight),
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
                    } else {
                        self.add_token(TokenKind::Star);
                    }
                }
                '!' => {
                    if self.match_char('=') {
                        self.add_token(TokenKind::NotEqual);
                    } else {
                        self.add_token(TokenKind::NoneType);
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
                },
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
                },
                '&' => self.add_token(TokenKind::Ampersand),
                '^' => self.add_token(TokenKind::Caret),
                '~' => self.add_token(TokenKind::Tilde),
                '$' => self.add_token(TokenKind::Dollar),
                '#' => self.add_token(TokenKind::Hash),
                '"' => self.parse_string()?,
                c if c.is_numeric() => self.parse_number(),
                c if c.is_ascii_alphabetic() || c == '_' => self.parse_identifier(),
                c if c.is_ascii_whitespace() => {
                    if self.line_char == 1 {
                        self.parse_indent(c);
                    }
                },
                c => return Err(format!("Unexpected char at {}:{} - {c}", self.line, self.line_char))
            }
        }

        return Ok(self.tokens.clone())
    }
} 