use std::{io::Write, collections::{HashMap, hash_map::{OccupiedEntry, Entry}}, fmt::Binary};

use crate::{ast::*, parser::Program};

pub trait ToJS {
    fn to_js(&self) -> String;
}

pub struct Transpiler {
    pub ast: Program,
}

impl Transpiler {
    pub fn new(ast: Program) -> Self {
        Self {
            ast
        }
    }

    pub fn replace_names_in_expr(mapped_names: &HashMap<String, String>, expr: &mut Expression) {
        match expr {
            Expression::VariableDecl(_) => unreachable!("no nested blocks as of now so this just panics"),
            Expression::Literal(_) => { /* whatever */ },
            Expression::BinaryOp(op) => {
                let BinaryOp { op, lhs, rhs } = op;
                Transpiler::replace_names_in_expr(mapped_names, lhs.as_mut());
                Transpiler::replace_names_in_expr(mapped_names, rhs.as_mut());
            },
            Expression::UnaryOp(op) => {
                let UnaryOp { op, operand } = op;
                Transpiler::replace_names_in_expr(mapped_names, operand.as_mut());
            },
            Expression::FunctionCall(func) => {
                let FunctionCall { func_name, arguments } = func;
                for arg in arguments {
                    Transpiler::replace_names_in_expr(mapped_names, arg)
                }
            },
            Expression::Variable(var) => {
                let Variable { name } = var;
                if let Some(new_name) = mapped_names.get(name) {
                    *name = new_name.clone()
                }
            },
            Expression::Return(ret) => {
                Transpiler::replace_names_in_expr(mapped_names, ret.as_mut())
            },
            Expression::Assignment(assignment) => {
                let Assignment { lhs, rhs } = assignment;
                Transpiler::replace_names_in_expr(mapped_names, lhs);
                Transpiler::replace_names_in_expr(mapped_names, rhs);
            },
            Expression::AnonStruct(anon) => {
                let AnonStruct { fields } = anon;
                todo!("ADD SUPPORT FOR STRUCTS")
            },
            Expression::ArrayLiteral(_) => todo!(),
            Expression::ArrayAccess(_) => todo!(),
            Expression::FieldAccess(_) => todo!(),
            Expression::NamedStruct(_) => todo!(),
            Expression::Range(_) => todo!(),
            Expression::JS(_) => todo!(),
            Expression::If(_) => todo!(),
            Expression::For(_) => todo!(),
            Expression::Placeholder => todo!(),
            Expression::Break => todo!(),
            Expression::Continue => todo!(),
        }
    }

    pub fn fix_scopes_codeblock(codeblock: &mut CodeBlock) {
        let mut mapped_var_names = HashMap::<String, String>::new();

        for expr in &mut codeblock.expressions {
            match expr {
                Expression::VariableDecl(VariableDecl { 
                    var_name, 
                    ..
                }) => {
                    match mapped_var_names.entry(var_name.clone()) {
                        Entry::Occupied(mut entry) => {
                            let mapped_name = entry.get_mut();
                            mapped_name.push_str("_FIXED_NAME_SIEMA_320");
                        }
                        Entry::Vacant(entry) => {
                            entry.insert(var_name.to_owned());
                        }
                    }
                }
                _ => {
                    Transpiler::replace_names_in_expr(&mapped_var_names, &mut expr)
                }
            }
        }
    }

    pub fn fix_scopes(&mut self) -> Result<(), String> {

        for module in &mut self.ast.modules {
            for func in &mut module.function_defs {
                
                Transpiler::fix_scopes_codeblock(&mut func.function_body);
            }
        }

        Ok(())
    }

    pub fn transpile(&mut self, path: &std::path::Path) -> Result<(), String> {

        self.fix_scopes()?;

        let mut outfile = std::fs::File::create(path)
            .map_err(|_| format!("Cannot open out file"))?;

        // todo dupa
        for module in &self.ast.modules {

            for funcdef in &module.function_defs {
                _ = outfile.write(funcdef.to_js().as_bytes());
            }

            _ = outfile.write(module.toplevel_scope.to_js().as_bytes());
        }


        Ok(())
    }
}