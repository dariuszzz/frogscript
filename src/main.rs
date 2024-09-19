#![feature(path_file_prefix)]
use std::{
    collections::HashMap,
    fs::{self, File},
    io::{Read, Write},
    path::{Path, PathBuf},
    time::Instant,
};

use gumdrop::Options;

mod arena;
mod ast;
mod lexer;
mod parser;
mod pond;
mod semantics;
mod symbol_table;
mod transpiler;

use arena::*;
use ast::*;
use lexer::*;
use parser::*;
use pond::{find_pond_path, Pond, Target};
use semantics::*;
use transpiler::*;

#[derive(Debug, Options)]
struct MyOptions {
    #[options(command)]
    command: Option<Command>,

    #[options(help = "print perfomance stats")]
    perf: bool,

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

    #[options(free, help = "path to parse (defaults to cwd)")]
    path: Vec<String>,
}

#[derive(Debug, Options)]
struct TranspileOpts {
    #[options(help = "target to transpile (defaults to target 'main')")]
    target: Option<String>,

    #[options(help = "output")]
    output: Option<String>,

    #[options(help = "create a dot graph of the ast")]
    graph: bool,

    #[options(free, help = "path to project (defaults to cwd)")]
    path: Vec<String>,
}

#[derive(Debug, Options)]
struct RunOpts {
    #[options(help = "target to run (defaults to target 'main')")]
    target: Option<String>,

    #[options(free, help = "path to project (defaults to cwd)")]
    path: Vec<String>,
}

fn find_project(initial_path: &Path) -> Result<Pond, String> {
    let pond_path = find_pond_path(initial_path)?;
    let pond = Pond::try_from_path(&pond_path)?;

    Ok(pond)
}

fn parse_project(pond: &Pond, perf: bool) -> Result<Program, String> {
    let mut ponds_to_parse = pond.dependency_ponds()?;
    ponds_to_parse.push(pond.clone());

    let mut modules = Vec::new();

    for pond in &ponds_to_parse {
        if perf {
            println!("{:?}", pond.name);
        }
        let mut parser = Parser::new(perf);
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
    perf: bool,
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

    let transp_start = Instant::now();
    transpiler.transpile(&out_path, &target.func)?;
    if perf {
        println!(
            "Transpilation: {}us",
            Instant::now().duration_since(transp_start).as_micros()
        );
    }

    Ok(())
}

fn main() -> Result<(), String> {
    let i_opts = MyOptions::parse_args_default_or_exit();

    let start = Instant::now();
    match i_opts.command.expect("No command given") {
        Command::Lex(opts) => {
            let path = Path::new(&opts.file);
            let source_file = fs::read_to_string(path)
                .expect(&format!("Module does not exist: {:?}", path.to_str()));
            let mut lexer = Lexer::new(&source_file, &path, i_opts.perf);
            match lexer.parse() {
                Ok(tokens) => {
                    for token in &tokens {
                        println!("{token:?}");
                    }
                }
                Err(err) => return Err(err),
            }
            if i_opts.perf {
                println!(
                    "Total: {}ms",
                    Instant::now().duration_since(start).as_millis()
                );
            }
        }
        Command::Parse(opts) => {
            let path = if opts.path.len() == 1 {
                let path = opts.path.get(0).unwrap();
                PathBuf::from(&path)
            } else {
                std::env::current_dir().expect("Invalid cwd")
            };

            let pond = find_project(&path)?;

            let mut program = parse_project(&pond, i_opts.perf)?;

            let mut semantic = SemanticAnalyzer::default();
            let symbol_table = semantic.perform_analysis(&mut program, i_opts.perf)?;

            if let Some(output) = opts.output {
                println!(
                    "dumping parsed modules to {:?}",
                    std::env::current_dir().unwrap().join(&output)
                );
                let mut outfile =
                    std::fs::File::create(output).map_err(|_| format!("Cannot open out file"))?;

                _ = outfile.write(format!("{:#?}", program.modules).as_bytes());
            }
            if i_opts.perf {
                println!(
                    "Total: {}ms",
                    Instant::now().duration_since(start).as_millis()
                );
            }
        }
        Command::Run(opts) => {
            let path = if opts.path.len() == 1 {
                let path = opts.path.get(0).unwrap();
                PathBuf::from(&path)
            } else {
                std::env::current_dir().expect("Invalid cwd")
            };

            let target_name = opts.target.unwrap_or("main".to_string());
            let pond = find_project(&path)?;
            let target = pond.targets.get(&target_name).expect("Invalid target");

            let mut program = parse_project(&pond, i_opts.perf)?;

            let mut semantic = SemanticAnalyzer::default();
            let symbol_table = semantic.perform_analysis(&mut program, i_opts.perf)?;

            transpile_project(program, target, None, i_opts.perf)?;
            if i_opts.perf {
                println!(
                    "Total: {}ms",
                    Instant::now().duration_since(start).as_millis()
                );
            }
            println!("-- Running `{}`, target `{}`", pond.name, target_name);

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

            let target_name = opts.target.unwrap_or("main".to_string());
            let pond = find_project(&path)?;
            let target = pond.targets.get(&target_name).expect("Invalid target");

            let mut program = parse_project(&pond, i_opts.perf)?;

            let mut semantic = SemanticAnalyzer::default();
            semantic.perform_analysis(&mut program, i_opts.perf)?;

            transpile_project(program, target, opts.output, i_opts.perf)?;
            if i_opts.perf {
                println!(
                    "Total: {}ms",
                    Instant::now().duration_since(start).as_millis()
                );
            }
        }
    }

    Ok(())
}
