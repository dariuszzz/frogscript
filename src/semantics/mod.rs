pub mod name_resolver;
pub mod symbol_table_populator;
pub mod typechecker;
use std::time::Instant;

use crate::{
    parser::Program,
    semantics::{
        name_resolver::NameResolver, symbol_table_populator::SymbolTablePopulator,
        typechecker::Typechecker,
    },
    GenericOptions,
};

use crate::symbol_table::*;

pub fn perform_analysis(
    program: &mut Program,
    opts: &GenericOptions,
) -> Result<SymbolTable, String> {
    let start = Instant::now();

    let mut symbol_table = SymbolTable::default();

    let mut populator = SymbolTablePopulator::new(&mut symbol_table);
    populator.populate(program)?;

    let mut resolver = NameResolver::new(&mut symbol_table);
    resolver.resolve_names(program)?;

    let mut typechecker = Typechecker::new(&mut symbol_table);
    typechecker.typecheck(program)?;

    if opts.perf {
        println!(
            "Semantics (total): {}us",
            Instant::now().duration_since(start).as_micros()
        );
    }

    Ok(symbol_table)
}
