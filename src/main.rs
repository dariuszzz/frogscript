use std::{path::Path, fs::{File, self}, io::Read, collections::HashMap};

use gumdrop::Options;

mod lexer;
mod parser;

use lexer::*;
use parser::*;

#[derive(Debug, Options)]
struct MyOptions {
    #[options(command)]
    command: Option<Command>
}

#[derive(Debug, Options)]
enum Command {
    #[options(help = "transpile a file")]
    Transpile(TranspileOpts),
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

#[derive(Debug, Options)]
struct TranspileOpts {
    #[options(free)]
    free: Vec<String>,

    #[options(help = "file to transpile")]
    file: String
}

fn main() -> Result<(), String> {

    let opts = MyOptions::parse_args_default_or_exit();

    match opts.command.expect("No command given") {
        Command::Lex(opts) => {
            let path = Path::new(&opts.file);
            let file_contents = fs::read_to_string(path).expect("Failed to read file");
            let mut lexer = Lexer::new(file_contents);
            match lexer.parse() {
                Ok(tokens) => {
                    for token in &tokens {
                        println!("{token:?}");
                    }
                },
                Err(err) => return Err(err),
            }
        }
        Command::Parse(opts) => {
            let path = Path::new(&opts.file);
            let file_contents = fs::read_to_string(path).expect("Failed to read file");
            let mut lexer = Lexer::new(file_contents);
            let tokens = lexer.parse()?;
            
            let mut parser = Parser::new(tokens);
            let filename = path.file_stem().unwrap().to_str().unwrap().to_owned();
            let module = parser.parse_file(filename)?;

            println!("{module:#?}");
        }
        Command::Transpile(opts) => {
            let path = Path::new(&opts.file);
            let file_contents = fs::read_to_string(path).expect("Failed to read file");
            let mut lexer = Lexer::new(file_contents);
            let tokens = lexer.parse()?;
            
            let mut parser = Parser::new(tokens);
            let filename = path.file_stem().unwrap().to_str().unwrap().to_owned();
            let ast = parser.parse_file(filename)?;

            // let mut transpiler = Transpiler::new(ast);
            // let js_ast = transpiler.transpile()?;
            // let js_source = js_ast.to_string();
        }
    }

    Ok(())
}