use crate::{
    backend::{
        ir_gen::IRGen,
        ssa_ir::{IRVariable, SSAIR},
    },
    parser::Program,
    pond::Target,
    symbol_table::SymbolTable,
};

pub mod arm64;
pub mod ir_gen;
pub mod liveness;
pub mod ssa_ir;

pub fn generate_ir(
    program: Program,
    target: Option<&Target>,
    symbol_table: &SymbolTable,
) -> Result<SSAIR, String> {
    let mut ir_gen = IRGen::default();
    let ssa_ir = ir_gen.generate_ir(program, target, symbol_table)?;

    Ok(ssa_ir)
}
