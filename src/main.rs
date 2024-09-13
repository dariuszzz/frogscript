#![feature(path_file_prefix)]
use std::{
    collections::HashMap,
    fs::{self, File},
    io::{Read, Write},
    path::{Path, PathBuf},
};

use gumdrop::Options;

mod arena;
mod ast;
mod lexer;
mod parser;
mod pond;
mod semantics;
mod transpiler;

use arena::*;
use ast::*;
use kdl::KdlDocument;
use lexer::*;
use parser::*;
use pond::{find_pond_path, Pond, Target};
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
    #[options(help = "run a target")]
    Run(RunOpts),
    #[options(help = "transpile a target")]
    Transpile(TranspileOpts),
    #[options(help = "parse a file/project")]
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
    #[options(help = "file to dump the parsed ast to")]
    output: Option<String>,

    #[options(free, help = "path to parse")]
    path: Vec<String>,
}

#[derive(Debug, Options)]
struct TranspileOpts {
    #[options(help = "target to transpile")]
    target: String,

    #[options(help = "output")]
    output: Option<String>,

    #[options(help = "create a dot graph of the ast")]
    graph: bool,

    #[options(free, help = "path to project")]
    path: Vec<String>,
}

#[derive(Debug, Options)]
struct RunOpts {
    #[options(help = "target to run")]
    target: String,

    #[options(free, help = "path to project")]
    path: Vec<String>,
}

fn find_project(initial_path: &Path) -> Result<Pond, String> {
    let pond_path = find_pond_path(initial_path)?;
    let pond = Pond::try_from_path(&pond_path)?;

    Ok(pond)
}

fn parse_project(pond: &Pond) -> Result<Program, String> {
    let mut ponds_to_parse = pond.dependency_ponds()?;
    ponds_to_parse.push(pond.clone());

    let mut modules = Vec::new();
    for pond in &ponds_to_parse {
        let mut parser = Parser::new();
        let mut pond_modules = parser.parse_pond(&pond)?;
        modules.append(&mut pond_modules);
    }

    let program = Program {
        modules: modules.clone(),
    };

    Ok(program)
}

fn transpile_project(
    program: Program,
    target: &Target,
    output: Option<String>,
) -> Result<(), String> {
    let mut transpiler = Transpiler::new(program);

    let file_name = target
        .file
        .file_stem()
        .unwrap()
        .to_string_lossy()
        .to_string();

    let out_path = if let Some(output_path) = output {
        PathBuf::from(output_path)
    } else {
        target.outfile.clone()
    };

    transpiler.transpile(&out_path, &target.func)?;

    Ok(())
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
            if opts.path.len() != 1 {
                return Err("Invalid path".to_string());
            }
            let path = opts.path.get(0).unwrap();
            let path = Path::new(&path);

            let pond = find_project(&path)?;

            let mut program = parse_project(&pond)?;

            let mut semantic = SemanticAnalyzer::default();
            semantic.perform_analysis(&mut program)?;

            if let Some(output) = opts.output {
                println!(
                    "dumping parsed modules to {:?}",
                    std::env::current_dir().unwrap().join(&output)
                );
                let mut outfile =
                    std::fs::File::create(output).map_err(|_| format!("Cannot open out file"))?;

                _ = outfile.write(format!("{:#?}", program.modules).as_bytes());
            }
        }
        Command::Run(opts) => {
            let path = if opts.path.len() == 1 {
                let path = opts.path.get(0).unwrap();
                PathBuf::from(&path)
            } else {
                std::env::current_dir().expect("Invalid cwd")
            };

            let pond = find_project(&path)?;
            let target = pond.targets.get(&opts.target).expect("Invalid target");

            let mut program = parse_project(&pond)?;

            let mut semantic = SemanticAnalyzer::default();
            semantic.perform_analysis(&mut program)?;

            transpile_project(program, target, None)?;

            println!("-- Running `{}`, target `{}`", pond.name, opts.target);

            let mut handle = std::process::Command::new("node")
                .args([target.outfile.to_str().unwrap()])
                .spawn()
                .expect("Failed to run program");

            handle.wait().expect("Program quit unexpectedly");
        }
        Command::Transpile(opts) => {
            let path = if opts.path.len() == 1 {
                let path = opts.path.get(0).unwrap();
                PathBuf::from(&path)
            } else {
                std::env::current_dir().expect("Invalid cwd")
            };

            let pond = find_project(&path)?;
            let target = pond.targets.get(&opts.target).expect("Invalid target");

            let mut program = parse_project(&pond)?;

            let mut semantic = SemanticAnalyzer::default();
            semantic.perform_analysis(&mut program)?;

            transpile_project(program, target, opts.output)?;
        }
    }

    Ok(())
}
