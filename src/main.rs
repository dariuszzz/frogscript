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
    #[options(free)]
    free: Vec<String>,

    #[options(help = "file to lex")]
    file: String,
}

#[derive(Debug, Options)]
struct ParseOpts {
    #[options(free)]
    free: Vec<String>,

    #[options(help = "file to parse")]
    file: String,
}

#[derive(Debug, Options)]
struct TranspileOpts {
    #[options(free)]
    free: Vec<String>,

    #[options(help = "file to transpile")]
    file: String,

    #[options(help = "file to transpile")]
    output: Option<String>,
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
            let mut lexer = Lexer::new(path);
            let tokens = lexer.parse()?;

            let mut parser = Parser::new(tokens);
            let filename = path.file_stem().unwrap().to_str().unwrap().to_owned();
            let module = parser.parse_module(filename)?;

            println!("{module:#?}");
        }
        Command::Transpile(opts) => {
            let path = Path::new(&opts.file);
            let mut lexer = Lexer::new(path);
            let tokens = lexer.parse()?;

            let mut parser = Parser::new(tokens);
            let filename = path.file_stem().unwrap().to_str().unwrap().to_owned();
            let module = parser.parse_module(filename.clone())?;

            let mut modules = Vec::<Module>::new();

            // for import in &module.imports {
            //     if modules.iter().any(|m| m.module_name == import.module_name) {
            //         continue;
            //     }

            //     let path = path
            //         .parent()
            //         .unwrap()
            //         .join(format!("{}.fr", import.module_name));
            //     let mut lexer = Lexer::new(&path);
            //     let tokens = lexer.parse()?;

            //     let tokens = tokens
            //         .into_iter()
            //         .filter(|t| {
            //             t.kind != TokenKind::MultilineComment && t.kind != TokenKind::Comment
            //         })
            //         .collect::<Vec<_>>();

            //     let mut parser = Parser::new(tokens);
            //     let imported_module = parser.parse_module(import.module_name.clone())?;

            //     modules.push(imported_module);
            // }

            let mut program = Program {
                main_module: module,
                imported_modules: modules,
            };

            SemanticAnalyzer::resolve_names(&mut program)?;

            let mut transpiler = Transpiler::new(program);
            let path_parent = path.canonicalize().unwrap();
            let path_parent = path_parent.parent().unwrap();
            let out_filename = opts.output.unwrap_or_else(|| format!("{filename}_out.js"));

            let out_path = path_parent.join(&out_filename);

            let js_ast = transpiler.transpile(&out_path)?;
        }
    }

    Ok(())
}
