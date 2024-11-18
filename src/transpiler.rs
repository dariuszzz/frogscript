use std::{
    collections::{hash_map::Entry, HashMap},
    io::Write,
};

use crate::{
    ast::*,
    parser::Program,
    symbol_table::{SymbolTable, SymbolType},
    FStringPart, Literal,
};

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

    pub fn replace_names_in_expr(
        module_name: &str,
        mapped_names: &HashMap<String, String>,
        expr: &mut Expression,
    ) {
        match &mut expr.kind {
            ExprKind::BuiltinType(expr) => {
                Transpiler::replace_names_in_expr(module_name, mapped_names, expr);
            }
            ExprKind::Import(_) => {}
            ExprKind::Lambda(lambda) => {
                let Lambda {
                    argument_list,
                    return_type,
                    function_body,
                } = lambda;

                let mut mapped_names = mapped_names.clone();

                for arg in argument_list {
                    arg.arg_name = format!("{}::{}", module_name, arg.arg_name);
                    mapped_names.insert(arg.arg_name.clone(), arg.arg_name.clone());
                }

                Transpiler::fix_scopes_codeblock(module_name, function_body, &mut mapped_names)
            }
            ExprKind::VariableDecl(var_decl) => {
                unreachable!("this is done in fix_codeblock")
            }
            ExprKind::BinaryOp(op) => {
                let BinaryOp { op, lhs, rhs } = op;
                Transpiler::replace_names_in_expr(module_name, mapped_names, lhs);
                Transpiler::replace_names_in_expr(module_name, mapped_names, rhs);
            }
            ExprKind::UnaryOp(op) => {
                let UnaryOp { op, operand } = op;
                Transpiler::replace_names_in_expr(module_name, mapped_names, operand);
            }
            ExprKind::FunctionCall(func) => {
                let FunctionCall {
                    func_expr,
                    arguments,
                } = func;

                if let ExprKind::Variable(Variable { name }) = &mut func_expr.kind {
                    if name.split("::").count() == 1 {
                        *name = format!("{}::{}", module_name, name.clone());
                    }
                } else {
                    Transpiler::replace_names_in_expr(module_name, mapped_names, func_expr)
                }

                for arg in arguments {
                    Transpiler::replace_names_in_expr(module_name, mapped_names, arg)
                }
            }
            ExprKind::Variable(var) => {
                let Variable { name } = var;

                // is not qualified
                if name.split("::").count() == 1 {
                    let qualified_name = format!("{}::{}", module_name, name.clone());
                    let new_name = if let Some(new_name) = mapped_names.get(&qualified_name) {
                        new_name.clone()
                    } else {
                        qualified_name
                    };
                    *name = new_name;
                }
            }
            ExprKind::Return(ret) => {
                Transpiler::replace_names_in_expr(module_name, mapped_names, ret)
            }
            ExprKind::Assignment(assignment) => {
                let Assignment { lhs, rhs } = assignment;
                Transpiler::replace_names_in_expr(module_name, mapped_names, lhs);
                Transpiler::replace_names_in_expr(module_name, mapped_names, rhs);
            }
            ExprKind::AnonStruct(anon) => {
                let AnonStruct { fields } = anon;
                for (name, val) in fields.iter_mut() {
                    Transpiler::replace_names_in_expr(module_name, mapped_names, val);
                }
            }
            ExprKind::ArrayLiteral(array) => {
                let ArrayLiteral { elements } = array;

                for elem in elements {
                    Transpiler::replace_names_in_expr(module_name, mapped_names, elem);
                }
            }
            ExprKind::ArrayAccess(array_access) => {
                let ArrayAccess { expr, index } = array_access;

                Transpiler::replace_names_in_expr(module_name, mapped_names, expr);
                Transpiler::replace_names_in_expr(module_name, mapped_names, index);
            }
            ExprKind::FieldAccess(field_access) => {
                let FieldAccess { expr, field } = field_access;

                Transpiler::replace_names_in_expr(module_name, mapped_names, expr);
            }
            ExprKind::NamedStruct(named) => {
                let NamedStruct {
                    casted_to,
                    struct_literal,
                } = named;

                for (field, expr) in &mut struct_literal.fields {
                    Transpiler::replace_names_in_expr(module_name, mapped_names, expr);
                }
            }
            ExprKind::Range(range) => {
                let Range {
                    start,
                    end,
                    inclusive,
                } = range;

                Transpiler::replace_names_in_expr(module_name, mapped_names, start);
                Transpiler::replace_names_in_expr(module_name, mapped_names, end);
            }
            ExprKind::If(if_block) => {
                let If {
                    cond,
                    true_branch,
                    else_branch,
                } = if_block;

                Transpiler::replace_names_in_expr(module_name, mapped_names, cond);

                Transpiler::fix_scopes_codeblock(
                    module_name,
                    true_branch,
                    &mut mapped_names.clone(),
                );
                if let Some(else_branch) = else_branch {
                    Transpiler::fix_scopes_codeblock(
                        module_name,
                        else_branch,
                        &mut mapped_names.clone(),
                    );
                }
            }
            ExprKind::For(for_block) => {
                let For {
                    binding,
                    binding_type,
                    iterator,
                    body,
                } = for_block;

                *binding = format!("{}::{}", module_name, binding);

                Transpiler::replace_names_in_expr(module_name, mapped_names, iterator);
                Transpiler::fix_scopes_codeblock(module_name, body, &mut mapped_names.clone());
            }
            ExprKind::Placeholder => {}
            ExprKind::Break => {}
            ExprKind::Continue => {}
            ExprKind::Literal(lit) => {
                if let Literal::String(parts) = lit {
                    for part in parts {
                        if let FStringPart::Code(expr) = part {
                            Transpiler::replace_names_in_expr(module_name, mapped_names, expr);
                        }
                    }
                }
            }
            ExprKind::JS(expr) => {
                Transpiler::replace_names_in_expr(module_name, mapped_names, expr);
            }
        }
    }

    pub fn fix_scopes_codeblock(
        module_name: &str,
        codeblock: &mut CodeBlock,
        mapped_names: &mut HashMap<String, String>,
    ) {
        for expr in &mut codeblock.expressions {
            match &mut expr.kind {
                ExprKind::VariableDecl(VariableDecl {
                    var_name,
                    var_value,
                    ..
                }) => {
                    // First replace the names in rhs
                    Transpiler::replace_names_in_expr(module_name, mapped_names, var_value);

                    // Then redeclare
                    *var_name = format!("{}::{}", module_name, var_name);
                    match mapped_names.entry(var_name.clone()) {
                        Entry::Occupied(mut entry) => {
                            let mapped_name = entry.get_mut();
                            mapped_name.push_str("_unique");

                            *var_name = mapped_name.clone();
                        }
                        Entry::Vacant(entry) => {
                            entry.insert(var_name.clone());
                        }
                    }
                }
                _ => Transpiler::replace_names_in_expr(module_name, &mapped_names, expr),
            }
        }
    }

    pub fn fix_scopes(&mut self) -> Result<(), String> {
        for module in &mut self.ast.modules {
            let mut mapped_var_names = HashMap::<String, String>::new();
            Transpiler::fix_scopes_codeblock(
                &module.module_name,
                &mut module.toplevel_scope,
                &mut mapped_var_names,
            );

            for func in &mut module.function_defs {
                func.func_name = format!("{}::{}", module.module_name, func.func_name);

                let mut mapped_var_names = mapped_var_names.clone();
                for arg in &mut func.argument_list {
                    arg.arg_name = format!("{}::{}", module.module_name, arg.arg_name);
                    mapped_var_names.insert(arg.arg_name.clone(), arg.arg_name.clone());
                }

                Transpiler::fix_scopes_codeblock(
                    &module.module_name,
                    &mut func.function_body,
                    &mut mapped_var_names.clone(),
                );
            }
        }

        Ok(())
    }

    fn wrap_in_copy(expr: &mut Expression, scope: &usize, symbol_table: &SymbolTable) {
        let curr_expr = expr.clone();
        if let ExprKind::Variable(var) = &curr_expr.kind {
            if let Ok(symbol) =
                symbol_table.find_symbol_rec(*scope, &var.name, SymbolType::Identifier)
            {
                match symbol.value_type {
                    Type::Function(_) => {}
                    _ => {
                        expr.kind = ExprKind::FunctionCall(FunctionCall {
                            func_expr: Box::new(Expression {
                                kind: ExprKind::Variable(Variable {
                                    name: "core::deep_copy".to_string(),
                                }),
                                ty: Type::Any, // TODO: do something with this
                            }),
                            arguments: vec![curr_expr],
                        })
                    }
                }
            }
        }
    }

    fn ensure_pass_by_value_expr(
        expr: &mut Expression,
        symbol_table: &SymbolTable,
        scope: &mut usize,
    ) {
        match &mut expr.kind {
            ExprKind::BuiltinType(expr) => {
                Transpiler::ensure_pass_by_value_expr(expr, symbol_table, scope)
            }
            ExprKind::Import(_) => {}
            kind @ ExprKind::Variable(_) => Transpiler::wrap_in_copy(expr, scope, symbol_table),
            ExprKind::VariableDecl(expr) => {
                Transpiler::ensure_pass_by_value_expr(&mut expr.var_value, symbol_table, scope);
            }
            ExprKind::Literal(literal) => match literal {
                Literal::String(parts) => {
                    for part in parts {
                        if let FStringPart::Code(expr) = part {
                            Transpiler::ensure_pass_by_value_expr(expr, symbol_table, scope);
                        }
                    }
                }
                _ => {}
            },
            ExprKind::BinaryOp(expr) => {
                // Transpiler::ensure_pass_by_value_expr(&mut expr.lhs, symbol_table, scope);
                // Transpiler::ensure_pass_by_value_expr(&mut expr.rhs, symbol_table, scope);
            }
            ExprKind::UnaryOp(expr) => {
                Transpiler::ensure_pass_by_value_expr(&mut expr.operand, symbol_table, scope);
            }
            ExprKind::FunctionCall(expr) => {
                Transpiler::ensure_pass_by_value_expr(&mut expr.func_expr, symbol_table, scope);
                for arg in &mut expr.arguments {
                    Transpiler::ensure_pass_by_value_expr(arg, symbol_table, scope);
                }
            }
            ExprKind::Return(expr) => {
                Transpiler::ensure_pass_by_value_expr(expr, symbol_table, scope);
            }
            ExprKind::Assignment(expr) => {
                // Transpiler::ensure_pass_by_value_expr(&mut expr.lhs, symbol_table, scope);
                Transpiler::ensure_pass_by_value_expr(&mut expr.rhs, symbol_table, scope);
            }
            ExprKind::AnonStruct(expr) => {
                for (_, expr) in &mut expr.fields {
                    Transpiler::ensure_pass_by_value_expr(expr, symbol_table, scope);
                }
            }
            ExprKind::ArrayLiteral(expr) => {
                for elem in &mut expr.elements {
                    Transpiler::ensure_pass_by_value_expr(elem, symbol_table, scope);
                }
            }
            ExprKind::ArrayAccess(expr) => {
                Transpiler::ensure_pass_by_value_expr(&mut expr.expr, symbol_table, scope);
                Transpiler::ensure_pass_by_value_expr(&mut expr.index, symbol_table, scope);
            }
            ExprKind::FieldAccess(expr) => {
                Transpiler::ensure_pass_by_value_expr(&mut expr.expr, symbol_table, scope);
            }
            ExprKind::NamedStruct(expr) => {
                for (_, expr) in &mut expr.struct_literal.fields {
                    Transpiler::ensure_pass_by_value_expr(expr, symbol_table, scope);
                }
            }
            ExprKind::Lambda(expr) => {
                *scope += 1;
                Transpiler::ensure_pass_by_value_codeblock(
                    &mut expr.function_body,
                    symbol_table,
                    scope,
                );
            }
            ExprKind::Range(expr) => {
                Transpiler::ensure_pass_by_value_expr(&mut expr.start, symbol_table, scope);
                Transpiler::ensure_pass_by_value_expr(&mut expr.end, symbol_table, scope);
            }
            ExprKind::If(expr) => {
                Transpiler::ensure_pass_by_value_expr(&mut expr.cond, symbol_table, scope);
                *scope += 1;
                Transpiler::ensure_pass_by_value_codeblock(
                    &mut expr.true_branch,
                    symbol_table,
                    scope,
                );
                if let Some(else_branch) = &mut expr.else_branch {
                    *scope += 1;
                    Transpiler::ensure_pass_by_value_codeblock(else_branch, symbol_table, scope);
                }
            }
            ExprKind::For(expr) => {
                Transpiler::ensure_pass_by_value_expr(&mut expr.iterator, symbol_table, scope);
                *scope += 1;
                Transpiler::ensure_pass_by_value_codeblock(&mut expr.body, symbol_table, scope);
            }
            ExprKind::JS(expr) => {
                // JS semantics in @js blocks
                // Transpiler::ensure_pass_by_value_expr(expr, symbol_table, scope);
            }
            ExprKind::Placeholder => {}
            ExprKind::Break => {}
            ExprKind::Continue => {}
        }
    }

    fn ensure_pass_by_value_codeblock(
        codeblock: &mut CodeBlock,
        symbol_table: &SymbolTable,
        scope: &mut usize,
    ) {
        for expr in &mut codeblock.expressions {
            Transpiler::ensure_pass_by_value_expr(expr, symbol_table, scope);
        }
    }

    fn ensure_pass_by_value(&mut self, symbol_table: &SymbolTable) -> Result<(), String> {
        let mut scope = 0;
        for module in &mut self.ast.modules {
            Transpiler::ensure_pass_by_value_codeblock(
                &mut module.toplevel_scope,
                symbol_table,
                &mut scope,
            );

            for func in &mut module.function_defs {
                scope += 1;
                Transpiler::ensure_pass_by_value_codeblock(
                    &mut func.function_body,
                    symbol_table,
                    &mut scope,
                );
            }

            scope += 1;
        }

        Ok(())
    }

    pub fn transpile(
        &mut self,
        path: &std::path::Path,
        entrypoint: &str,
        symbol_table: &SymbolTable,
    ) -> Result<(), String> {
        // self.ensure_pass_by_value(symbol_table)?;
        self.fix_scopes()?;

        // let mapped_entrypoint = symbol_table.mapped_names.get(entrypoint).unwrap();

        if let Some(entrypoint) = self
            .ast
            .modules
            .last()
            .unwrap()
            .function_defs
            .iter()
            .cloned()
            .find(|f| f.func_name.split("::").last().unwrap() == entrypoint)
        {
            self.ast
                .modules
                .first_mut()
                .unwrap()
                .toplevel_scope
                .expressions
                .push(Expression {
                    kind: ExprKind::FunctionCall(FunctionCall {
                        func_expr: Box::new(Expression {
                            kind: ExprKind::Variable(Variable {
                                name: entrypoint.func_name.clone(),
                            }),
                            ty: Type::Function(FunctionType {
                                env_args: Vec::new(),
                                args: Vec::new(),
                                ret: Box::new(Type::Any),
                            }),
                        }),
                        arguments: Vec::new(),
                    }),
                    ty: entrypoint.return_type,
                });
        } else {
            return Err(format!(
                "No main function in {:?}",
                self.ast.modules.last().unwrap().module_name
            ));
        }

        std::fs::create_dir_all(path.parent().unwrap()).expect("Failed to create out dir");
        let mut outfile =
            std::fs::File::create(path).map_err(|_| format!("Cannot open out file {:?}", path))?;

        for module in self.ast.modules.iter().rev() {
            // println!("transpiling {:?}", module.module_name);
            _ = outfile.write(format!("\n // {} \n", module.module_name).as_bytes());
            for funcdef in &module.function_defs {
                _ = outfile.write(funcdef.to_js().as_bytes());
            }

            _ = outfile.write(module.toplevel_scope.to_js().as_bytes());
        }
        Ok(())
    }
}
