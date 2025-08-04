use crate::{
    backend::ssa_ir::{self, SSAIR},
    symbol_table::{self, SymbolTable},
};
use ssa_ir::IRInstr;
use std::fmt::Write;

#[derive(Debug, Default)]
pub struct ARM64Backend {}

impl ARM64Backend {
    pub fn compile_ir(
        &mut self,
        ssa_ir: SSAIR,
        symbol_table: &SymbolTable,
    ) -> Result<String, String> {
        let mut out = r#"
.globl _main

_main:
"#
        .to_string();

        for block in ssa_ir.blocks.iter().rev() {
            write!(out, "{}:\n", block.name).unwrap();

            for instr in &block.instructions {
                write!(out, "\t").unwrap();
                match instr {
                    IRInstr::InlineTarget(instrs) => {
                        write!(out, "{}\n", instrs).unwrap();
                    }
                    _ => {
                        write!(out, "\n").unwrap();
                    }
                }
            }
        }

        Ok(out)
    }
}
