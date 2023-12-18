use std::io::Write;

use crate::ast::*;

pub trait ToJS {
    fn to_js(&self) -> String;
}

pub struct Transpiler {

}

impl Transpiler {
    pub fn new() -> Self {
        Self {

        }
    }

    pub fn transpile_module(&mut self, module: Module, path: &std::path::Path) -> Result<(), String> {

        dbg!(path);
        let mut outfile = std::fs::File::create(path)
            .map_err(|_| format!("Cannot open out file"))?;

        for funcdef in module.function_defs {
            _ = outfile.write(funcdef.to_js().as_bytes());
        }

        _ = outfile.write(module.toplevel_scope.to_js().as_bytes());

        Ok(())
    }
}