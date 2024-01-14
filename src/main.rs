#![feature(path_file_prefix)]
use std::{
    collections::HashMap,
    fs::{self, File},
    io::Read,
    path::Path,
};

use gumdrop::Options;

mod ast;
mod lexer;
mod parser;
mod semantics;
mod transpiler;

use ast::*;
use lexer::*;
use parser::*;
use semantics::*;
use transpiler::*;

#[derive(Debug, Options)]
struct MyOptions {
    #[options(command)]
    command: Option<Command>,

    #[options(help = "print help message")]
    help: bool,
}

#[derive(Debug, Options)]
enum Command {
    #[options(help = "transpile a file")]
    Transpile(TranspileOpts),
    #[options(help = "parse a file")]
    Parse(ParseOpts),
    #[options(help = "lex a file")]
    Lex(LexOpts),
}

#[derive(Debug, Options)]
struct LexOpts {
    #[options(help = "file to lex")]
    file: String,
}

#[derive(Debug, Options)]
struct ParseOpts {
    #[options(help = "file to parse")]
    file: String,
}

#[derive(Debug, Options)]
struct TranspileOpts {
    #[options(help = "file to transpile")]
    file: String,

    #[options(help = "output")]
    output: Option<String>,

    #[options(help = "create a dot graph of the ast")]
    graph: bool,
}

fn main() -> Result<(), String> {
    let opts = MyOptions::parse_args_default_or_exit();

    match opts.command.expect("No command given") {
        Command::Lex(opts) => {
            let path = Path::new(&opts.file);
            let mut lexer = Lexer::new(path);
            match lexer.parse() {
                Ok(tokens) => {
                    for token in &tokens {
                        println!("{token:?}");
                    }
                }
                Err(err) => return Err(err),
            }
        }
        Command::Parse(opts) => {
            let path = Path::new(&opts.file);

            let path_parent = path.canonicalize().unwrap();
            let path_parent = path_parent.parent().unwrap();

            let mut parser = Parser::new(path_parent.to_owned());
            let file_name = path.file_prefix().unwrap().to_str().unwrap().to_owned();
            let modules = parser.parse_file(file_name)?;

            println!("{:#?}", modules);
        }
        Command::Transpile(opts) => {
            let path = Path::new(&opts.file);

            let path_parent = path.canonicalize().unwrap();
            let path_parent = path_parent.parent().unwrap();

            let mut parser = Parser::new(path_parent.to_owned());
            let file_name = path.file_prefix().unwrap().to_str().unwrap().to_owned();
            let modules = parser.parse_file(file_name.clone())?;

            let mut program = Program { modules };

            let mut semantic = SemanticAnalyzer::default();
            semantic.resolve_names(&mut program)?;

            let mut transpiler = Transpiler::new(program);
            let out_filename = opts.output.unwrap_or_else(|| format!("{file_name}_out.js"));

            let out_path = path_parent.join(&out_filename);

            let js_ast = transpiler.transpile(&out_path)?;
        }
    }

    Ok(())
}
