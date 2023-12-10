use std::{path::Path, fs::{File, self}, io::Read, collections::HashMap};

use gumdrop::Options;

#[derive(Debug, Options)]
struct MyOptions {
    #[options(command)]
    command: Option<Command>
}

#[derive(Debug, Options)]
enum Command {
    #[options(help = "parse a file")]
    Parse(ParseOpts),
    #[options(help = "lex a file")]
    Lex(LexOpts)
}

#[derive(Debug, Options)]
struct LexOpts {
    #[options(free)]
    free: Vec<String>,

    #[options(help = "file to lex")]
    file: String
}

#[derive(Debug, Options)]
struct ParseOpts {
    #[options(free)]
    free: Vec<String>,

    #[options(help = "file to parse")]
    file: String
}

fn main() {

    let opts = MyOptions::parse_args_default_or_exit();

    match opts.command.expect("No command given") {
        Command::Lex(opts) => {
            let path = Path::new(&opts.file);
            let file_contents = fs::read_to_string(path).expect("Failed to read file");
            let mut lexer = Lexer::new(file_contents);
            match lexer.parse() {
                Err(err) => eprintln!("Error parsing: {err}"),
                Ok(tokens) => {
                    for token in &tokens {
                        println!("{token:?}");
                    }
                }
            }
        }
        Command::Parse(opts) => {
            let path = Path::new(&opts.file);
            let file_contents = fs::read_to_string(path).expect("Failed to read file");
            let mut lexer = Lexer::new(file_contents);
            match lexer.parse() {
                Err(err) => eprintln!("Error parsing: {err}"),
                Ok(tokens) => {}
            }
        }
    }
}

#[derive(Clone, Debug)]
enum Literal {
    String(String),
    Int(isize),
    Uint(usize),
    Float(f32),
    Boolean(bool),
}

#[derive(Clone, Debug)]
enum Identifier {
    Custom(String),
    Let,
    Final,
    Const,
    Int,
    Uint,
    Float,
    Boolean,
    String,
    Type,
    Enum,
    For,
    While,
    Break,
    Continue,
    Return,
    If,
    Match,
    Use,
    Export,
    From,
    Implicit,
    As,
}


#[derive(Clone, Debug)]
enum TokenKind {
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
    
    Literal(Literal),
    Identifier(Identifier),
}

#[derive(Debug, Clone)]
struct Token {
    kind: TokenKind,
    start: usize,
    lexeme: String,
}

#[derive(Debug)]
enum NestedParsingCount {
    None,
    Count(i32)
}

impl NestedParsingCount {
    fn increment(&mut self) {
        match self {
            Self::None => {},
            Self::Count(c) => *c = *c + 1
        }
    }

    fn decrement(&mut self) {
        match self {
            Self::None => {},
            Self::Count(c) => *c = *c - 1
        }
    }
}


struct Lexer {
    source_file: String,
    tokens: Vec<Token>,
    current: usize,
    line: usize,
    line_char: usize,
    lexeme_start: usize,
    parsing_multiline_comment: NestedParsingCount
}

impl Lexer {
    fn new(source_file: String) -> Self {
        Self { 
            source_file,
            tokens: Vec::new(),
            current: 0,
            line: 1,
            line_char: 0,
            lexeme_start: 0,
            parsing_multiline_comment: NestedParsingCount::None
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
                start: self.lexeme_start,
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
                start: self.lexeme_start + 1,
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
            ("const", Identifier::Const),
            ("int", Identifier::Int),
            ("uint", Identifier::Uint),
            ("float", Identifier::Float),
            ("bool", Identifier::Boolean),
            ("type", Identifier::Type),
            ("enum", Identifier::Enum),
            ("string", Identifier::String),
            ("for", Identifier::For),
            ("while", Identifier::While),
            ("break", Identifier::Break),
            ("continue", Identifier::Continue),
            ("return", Identifier::Return),
            ("if", Identifier::If),
            ("match", Identifier::Match),
            ("use", Identifier::Use),
            ("export", Identifier::Export),
            ("from", Identifier::From),
            ("implicit", Identifier::Implicit),
            ("as", Identifier::Implicit),
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
        } else if lexeme == "false" {
            self.add_token(TokenKind::Literal(Literal::Boolean(false)));
        }
        
        if let Some(kind) = keywords.get(lexeme.as_str()) {
            self.add_token(TokenKind::Identifier(kind.clone()));
        } else {
            self.add_token(TokenKind::Identifier(Identifier::Custom(lexeme.to_owned())));
        }
    }
    
    fn parse(&mut self) -> Result<Vec<Token>, String> {
        while !self.is_at_end() {
            self.lexeme_start = self.current;
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
                '\n' => self.add_token(TokenKind::Newline),
                '.' => self.add_token(TokenKind::Dot),
                '&' => self.add_token(TokenKind::Ampersand),
                '^' => self.add_token(TokenKind::Caret),
                '~' => self.add_token(TokenKind::Tilde),
                '$' => self.add_token(TokenKind::Dollar),
                '"' => self.parse_string()?,
                c if c.is_numeric() => self.parse_number(),
                c if c.is_ascii_alphabetic() || c == '_' => self.parse_identifier(),
                c if c.is_ascii_whitespace() => {},
                c => return Err(format!("Unexpected char at {}:{} - {c}", self.line, self.line_char))
            }
        }

        return Ok(self.tokens.clone())
    }
} 
