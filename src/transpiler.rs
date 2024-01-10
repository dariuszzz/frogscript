use std::{
    collections::{hash_map::Entry, HashMap},
    io::Write,
};

use crate::{ast::*, parser::Program};

pub trait ToJS {
    fn to_js(&self) -> String;
}

pub struct Transpiler {
    pub ast: Program,
}

impl Transpiler {
    pub fn new(ast: Program) -> Self {
        Self { ast }
    }

    pub fn replace_names_in_expr(mapped_names: &HashMap<String, String>, expr: &mut Expression) {
        match expr {
            Expression::VariableDecl(_) => {
                unreachable!("no nested blocks as of now")
            }
            Expression::Literal(_) => { /* whatever */ }
            Expression::BinaryOp(op) => {
                let BinaryOp { op, lhs, rhs } = op;
                Transpiler::replace_names_in_expr(mapped_names, lhs);
                Transpiler::replace_names_in_expr(mapped_names, rhs);
            }
            Expression::UnaryOp(op) => {
                let UnaryOp { op, operand } = op;
                Transpiler::replace_names_in_expr(mapped_names, operand);
            }
            Expression::FunctionCall(func) => {
                let FunctionCall {
                    func_module,
                    func_name,
                    arguments,
                } = func;
                for arg in arguments {
                    Transpiler::replace_names_in_expr(mapped_names, arg)
                }
            }
            Expression::Variable(var) => {
                let Variable { var_module, name } = var;
                if let Some(new_name) = mapped_names.get(name) {
                    *name = new_name.clone()
                }
            }
            Expression::Return(ret) => Transpiler::replace_names_in_expr(mapped_names, ret),
            Expression::Assignment(assignment) => {
                let Assignment { lhs, rhs } = assignment;
                Transpiler::replace_names_in_expr(mapped_names, lhs);
                Transpiler::replace_names_in_expr(mapped_names, rhs);
            }
            Expression::AnonStruct(anon) => {
                let AnonStruct { fields } = anon;
                for (name, val) in fields.iter_mut() {
                    Transpiler::replace_names_in_expr(mapped_names, val);
                }
            }
            Expression::ArrayLiteral(array) => {
                let ArrayLiteral { elements } = array;

                for elem in elements {
                    Transpiler::replace_names_in_expr(mapped_names, elem);
                }
            }
            Expression::ArrayAccess(array_access) => {
                let ArrayAccess { expr, index } = array_access;

                Transpiler::replace_names_in_expr(mapped_names, expr);
                Transpiler::replace_names_in_expr(mapped_names, index);
            }
            Expression::FieldAccess(field_access) => {
                let FieldAccess { expr, field } = field_access;

                Transpiler::replace_names_in_expr(mapped_names, expr);
            }
            Expression::NamedStruct(named) => {
                let NamedStruct {
                    casted_to,
                    struct_literal,
                } = named;

                for (field, expr) in &mut struct_literal.fields {
                    Transpiler::replace_names_in_expr(mapped_names, expr);
                }
            }
            Expression::Range(range) => {
                let Range {
                    start,
                    end,
                    step,
                    inclusive,
                } = range;

                Transpiler::replace_names_in_expr(mapped_names, start);
                Transpiler::replace_names_in_expr(mapped_names, end);
                Transpiler::replace_names_in_expr(mapped_names, step);
            }
            Expression::JS(_) => {}
            Expression::If(if_block) => {
                let If {
                    cond,
                    true_branch,
                    else_branch,
                } = if_block;

                Transpiler::replace_names_in_expr(mapped_names, cond);

                Transpiler::fix_scopes_codeblock(true_branch, &mut mapped_names.clone());
                if let Some(else_branch) = else_branch {
                    Transpiler::fix_scopes_codeblock(else_branch, &mut mapped_names.clone());
                }
            }
            Expression::For(for_block) => {
                let For {
                    binding,
                    iterator,
                    body,
                } = for_block;

                Transpiler::replace_names_in_expr(mapped_names, iterator);
                Transpiler::fix_scopes_codeblock(body, &mut mapped_names.clone());
            }
            Expression::Placeholder => {}
            Expression::Break => {}
            Expression::Continue => {}
        }
    }

    pub fn fix_scopes_codeblock(
        codeblock: &mut CodeBlock,
        mapped_names: &mut HashMap<String, String>,
    ) {
        for expr in &mut codeblock.expressions {
            match expr {
                Expression::VariableDecl(VariableDecl { var_name, .. }) => {
                    match mapped_names.entry(var_name.clone()) {
                        Entry::Occupied(mut entry) => {
                            let mapped_name = entry.get_mut();
                            mapped_name.push_str("_unique");

                            *var_name = mapped_name.clone();
                        }
                        Entry::Vacant(entry) => {
                            entry.insert(var_name.to_owned());
                        }
                    }
                }
                _ => Transpiler::replace_names_in_expr(&mapped_names, expr),
            }
        }
    }

    pub fn fix_scopes(&mut self) -> Result<(), String> {
        for module in &mut self.ast.imported_modules {
            let mut mapped_var_names = HashMap::<String, String>::new();
            Transpiler::fix_scopes_codeblock(&mut module.toplevel_scope, &mut mapped_var_names);

            for func in &mut module.function_defs {
                Transpiler::fix_scopes_codeblock(
                    &mut func.function_body,
                    &mut mapped_var_names.clone(),
                );
            }
        }

        Ok(())
    }

    pub fn transpile(&mut self, path: &std::path::Path) -> Result<(), String> {
        self.fix_scopes()?;

        let mut outfile =
            std::fs::File::create(path).map_err(|_| format!("Cannot open out file"))?;

        // for module in &self.ast.imported_modules {
        //     for funcdef in &module.function_defs {
        //         _ = outfile.write(funcdef.to_js().as_bytes());
        //     }

        //     _ = outfile.write(module.toplevel_scope.to_js().as_bytes());
        // }

        for funcdef in &self.ast.main_module.function_defs {
            _ = outfile.write(funcdef.to_js().as_bytes());
        }

        _ = outfile.write(self.ast.main_module.toplevel_scope.to_js().as_bytes());

        Ok(())
    }
}
