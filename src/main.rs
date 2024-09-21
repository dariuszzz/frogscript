#![feature(path_file_prefix)]
use std::{
    collections::{HashMap, VecDeque},
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
use symbol_table::SymbolTable;
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
    #[options(help = "run tests")]
    Test(TestOpts),
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
struct TestOpts {
    #[options(help = "show only failed tests")]
    failed: bool,

    #[options(help = "terminate early")]
    early: bool,

    #[options(free, help = "path to tests (defaults to cwd)")]
    path: Vec<String>,
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

fn compile_file_for_testing(source: &str, path: &Path, file_name: &Path) -> Result<Program, String> {
    let mut lexer = Lexer::new(&source, path, false);
    let tokens = lexer.parse().map_err(|e| format!("Lexer: {e:?}"))?;

    let tokens = tokens
        .into_iter()
        .filter(|t| t.kind != TokenKind::MultilineComment && t.kind != TokenKind::Comment)
        .collect::<Vec<_>>();

    let mut parser = Parser::new(false);
    let modules = parser
        .parse_tokens(tokens, "test")
        .map_err(|e| format!("Parser: {e:?}"))?;

    let mut program = Program { modules };
    let mut semantic = SemanticAnalyzer::default();
    let symbol_table = semantic
        .perform_analysis(&mut program, false)
        .map_err(|e| format!("Semantics: {e:?}"))?;

    let mut transpiler = Transpiler::new(program.clone());


    transpiler
        .transpile(&file_name, "main", &symbol_table)
        .map_err(|e| format!("Transpiler: {e:?}"))?;

    Ok(program)
}

fn test_file(path: &Path) -> Result<(), String> {
    let source = fs::read_to_string(path).unwrap();

    let expectations = {
        if source.starts_with("/*") {
            let start = 2;
            let mut end = 2;


            loop {
                match source.get(end..end+2) {
                    None => break None,
                    Some("*/") => break source.get(start..end),
                    a => {}
                }

                end += 1
            }
        } else {
            None
        }
    };

    let file_name = path.parent().unwrap().join("out/out.js");
    let program = compile_file_for_testing(&source, path, &file_name);

    if let Some(expectations) = expectations {
        let string = expectations
            .trim()
            .replace("\r\n", "\n");

        let expectations = string
            .split("-- ")
            .filter_map(|exp| exp.split_once(":"))
            .map(|(exp, val)| (exp.trim(), val.trim()))
            .collect::<Vec<_>>();

        for (exp, val) in expectations.clone() {
            match exp {
                "fails" if val == "true" => {
                    if program.is_ok() {
                        return Err(format!("Expected to not compile but did"));
                    } else {
                        return Ok(())
                    }
                }
                _ => {}
            }
        }

        if let Ok(program) = program {
            let output = std::process::Command::new("node")
                .args([file_name])
                .output()
                .expect("Failed to run program");

            let exit = output.status;
            let out = String::from_utf8(output.stdout).unwrap();
            let out = out.trim();
            let err = String::from_utf8(output.stderr).unwrap();
            let err = err.trim();

            if !err.is_empty() {
                return Err(format!("Executable failed with: {err:?}"));
            }


            for (exp, val) in expectations {
                match exp {
                    "output" => {
                        if val != out {
                            return Err(format!("Wrong output: {val:?} != {out:?}"));
                        }
                    }
                    "ast" => {
                        if format!("{:#?}", program.modules[0]) != val {
                            return Err(format!("Wrong ast: {val:?} != {out:?}"));
                        }
                    }
                    _ => {}
                }
            }
        } else {
            return Err(program.unwrap_err())
        }
    }


    Ok(())
}

fn transpile_project(
    program: Program,
    target: &Target,
    output: Option<String>,
    symbol_table: &SymbolTable,
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
    transpiler.transpile(&out_path, &target.func, symbol_table)?;
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

            transpile_project(program, target, None, &symbol_table, i_opts.perf)?;
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
        Command::Test(opts) => {
            let path = if opts.path.len() == 1 {
                let path = opts.path.get(0).unwrap();
                PathBuf::from(&path)
            } else {
                std::env::current_dir().expect("Invalid cwd")
            };

            let mut dirs_to_check = VecDeque::new();
            dirs_to_check.push_back(path);

            let mut files_to_test = Vec::new();

            while let Some(dir) = dirs_to_check.pop_front() {
                let paths = fs::read_dir(&dir).unwrap();
                for path in paths {
                    let path = path.unwrap().path();

                    if path.is_file() && path.extension().unwrap() == "fr" {
                        files_to_test.push(path);
                    } else if path.is_dir() {
                        dirs_to_check.push_back(path);
                    }
                }
            }

            files_to_test.sort();

            for file in &files_to_test {
                match test_file(file) {
                    Ok(()) if !opts.failed => println!("PASSED: {file:?}"),
                    Ok(()) => {}
                    Err(e) => {
                        println!("FAILED: {file:?}\nREASON: {e:?}");
                        if opts.early {
                            return Ok(());
                        }
                    }
                }
            }
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
            let symbol_table = semantic.perform_analysis(&mut program, i_opts.perf)?;

            transpile_project(program, target, opts.output, &symbol_table, i_opts.perf)?;
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
