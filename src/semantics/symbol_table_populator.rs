use crate::{
    ast::*,
    lexer::{FStringPart, Literal},
    parser::Program,
};

use crate::symbol_table::*;

#[derive(Debug)]
pub struct SymbolTablePopulator<'a> {
    pub symbol_table: &'a mut SymbolTable,
}

impl<'a> SymbolTablePopulator<'a> {
    pub fn new(symbol_table: &'a mut SymbolTable) -> Self {
        Self { symbol_table }
    }

    pub fn populate(&mut self, program: &mut Program) -> Result<(), String> {
        for module in &mut program.modules {
            let module_scope = self.symbol_table.table.insert(Scope::default());
            let curr_module_name = &module.module_name;

            self.symbol_table
                .module_to_scope
                .insert(module.module_name.clone(), module_scope);

            for type_def in &mut module.type_defs {
                let idx = self.symbol_table.add_symbol_to_scope(
                    module_scope,
                    Symbol {
                        qualified_name: format!("{}::{}", module.module_name, type_def.name),
                        name: type_def.name.clone(),
                        symbol_type: SymbolType::Type,
                        value_type: type_def.underlying_ty.clone(),
                        exported: type_def.export,
                        mutable: false,
                    },
                )?;

                type_def.symbol_idx = (module_scope, idx);
            }

            self.populate_symbol_table_codeblock(
                curr_module_name,
                module_scope,
                &mut module.toplevel_scope,
                false, // toplevel scope has no shadowing
            )?;

            for func_def in &mut module.function_defs {
                let func_type = Type::Function(FunctionType {
                    env_args: func_def
                        .argument_list
                        .iter()
                        .filter(|arg| arg.is_env)
                        .map(|arg| arg.arg_type.clone())
                        .collect(),
                    args: func_def
                        .argument_list
                        .iter()
                        .filter(|arg| !arg.is_env)
                        .map(|arg| arg.arg_type.clone())
                        .collect(),
                    ret: Box::new(func_def.return_type.clone()),
                });

                let idx = self.symbol_table.add_symbol_to_scope(
                    module_scope,
                    Symbol {
                        qualified_name: format!("{}::{}", module.module_name, func_def.func_name),
                        name: func_def.func_name.to_string(),
                        symbol_type: SymbolType::Identifier,
                        value_type: func_type,
                        exported: func_def.export,
                        mutable: false,
                    },
                )?;

                func_def.symbol_idx = (module_scope, idx);

                let func_scope = self.symbol_table.new_scope(module_scope)?;

                for arg in &mut func_def.argument_list {
                    let idx = self.symbol_table.add_symbol_to_scope(
                        func_scope,
                        Symbol {
                            qualified_name: arg.arg_name.clone(),
                            name: arg.arg_name.clone(),
                            symbol_type: SymbolType::Identifier,
                            value_type: arg.arg_type.clone(),
                            exported: false,
                            mutable: match arg.arg_type {
                                Type::Reference(_) => false,
                                _ => true,
                            },
                        },
                    )?;

                    arg.symbol_idx = (func_scope, idx);
                }

                self.populate_symbol_table_codeblock(
                    curr_module_name,
                    func_scope,
                    &mut func_def.function_body,
                    true,
                )?;
            }
        }

        Ok(())
    }

    pub fn populate_symbol_table_codeblock(
        &mut self,
        curr_module_name: &str,
        scope: usize,
        codeblock: &mut CodeBlock,
        shadowing: bool,
    ) -> Result<(), String> {
        for expr in &mut codeblock.expressions {
            self.populate_symbol_table_expr(curr_module_name, scope, expr, shadowing)?;
        }

        Ok(())
    }

    pub fn populate_symbol_table_expr(
        &mut self,
        curr_module_name: &str,
        scope: usize,
        expr: &mut Expression,
        shadowing: bool,
    ) -> Result<(), String> {
        match expr {
            Expression::BuiltinType(expr) => {
                self.populate_symbol_table_expr(curr_module_name, scope, expr, shadowing)?;
            }
            Expression::Import(import) => {
                // let imports = self.get_imports_rec(scope)?;

                // let curr_scope = self
                //     .symbol_table
                //     .get_scope_mut(scope)
                //     .ok_or("Scope does not exist")?;

                // let flattened = Self::flatten_import(import, String::new());

                // for flat in flattened {
                //     if imports.contains(&flat) {
                //         return Err(format!(
                //             "Conflicting use statement: {:?} used multiple times",
                //             flat.name
                //         ));
                //     }
                // }

                // curr_scope.use_statements.push(import.clone());

                // for module in self.module_to_scope.keys() {
                //     let mut module_name_in_scope = module.as_str();

                //     for imp in &imports {
                //         module_name_in_scope = module_name_in_scope
                //             .strip_prefix(&format!("{}", imp.module_name))
                //             .unwrap_or(module_name_in_scope);
                //         module_name_in_scope = module_name_in_scope
                //             .strip_prefix("::")
                //             .unwrap_or(module_name_in_scope);
                //     }

                //     modules_in_scope.insert(module_name_in_scope);
                // }

                // println!("In scope: {modules_in_scope:?}");
                // println!("Overall:  {:?}", self.module_to_scope.keys());
                // if modules_in_scope.len() != self.module_to_scope.len() {
                //     return Err(format!(
                //         "Import statement causes ambiguity {:?}",
                //         import.module_name
                //     ));
                // }

                // return Err(format!(
                //     "Module {:?} already imported in this scope",
                //     import.module_name
                // ));
            }
            Expression::Variable(_) => {}
            Expression::VariableDecl(expr) => {
                self.populate_symbol_table_expr(
                    curr_module_name,
                    scope,
                    &mut expr.var_value,
                    shadowing,
                )?;

                let og_name = expr.var_name.to_string();
                let unique_name =
                    self.symbol_table
                        .ensure_unique_name(scope, &og_name, SymbolType::Identifier);

                let symbol_idx = self.symbol_table.add_symbol_to_scope(
                    scope,
                    Symbol {
                        name: unique_name.clone(),
                        qualified_name: unique_name.clone(),
                        symbol_type: SymbolType::Identifier,
                        value_type: expr.var_type.clone(),
                        exported: false,
                        mutable: expr.is_mutable,
                    },
                )?;

                expr.var_name = unique_name;

                expr.symbol_idx = (scope, symbol_idx);
            }
            Expression::Literal(lit) => match lit {
                Literal::String(parts) => {
                    for part in parts {
                        if let FStringPart::Code(expr) = part {
                            self.populate_symbol_table_expr(
                                curr_module_name,
                                scope,
                                expr,
                                shadowing,
                            )?
                        }
                    }
                }
                _ => {}
            },
            Expression::BinaryOp(expr) => {
                self.populate_symbol_table_expr(curr_module_name, scope, &mut expr.lhs, shadowing)?;
                self.populate_symbol_table_expr(curr_module_name, scope, &mut expr.rhs, shadowing)?;
            }
            Expression::UnaryOp(expr) => {
                self.populate_symbol_table_expr(
                    curr_module_name,
                    scope,
                    &mut expr.operand,
                    shadowing,
                )?;
            }
            Expression::FunctionCall(expr) => {
                self.populate_symbol_table_expr(
                    curr_module_name,
                    scope,
                    &mut expr.func_expr,
                    shadowing,
                )?;

                for arg in &mut expr.arguments {
                    self.populate_symbol_table_expr(curr_module_name, scope, arg, shadowing)?;
                }
            }
            Expression::Return(expr) => {
                if let Some(expr) = expr {
                    self.populate_symbol_table_expr(curr_module_name, scope, expr, shadowing)?;
                }
            }
            Expression::Assignment(expr) => {
                self.populate_symbol_table_expr(curr_module_name, scope, &mut expr.lhs, shadowing)?;
                self.populate_symbol_table_expr(curr_module_name, scope, &mut expr.rhs, shadowing)?;
            }
            Expression::AnonStruct(expr) => {
                for (_, expr) in &mut expr.fields {
                    self.populate_symbol_table_expr(curr_module_name, scope, expr, shadowing)?;
                }
            }
            Expression::ArrayLiteral(expr) => {
                for elem in &mut expr.elements {
                    self.populate_symbol_table_expr(curr_module_name, scope, elem, shadowing)?;
                }
            }
            Expression::ArrayAccess(expr) => {
                self.populate_symbol_table_expr(
                    curr_module_name,
                    scope,
                    &mut expr.expr,
                    shadowing,
                )?;
                self.populate_symbol_table_expr(
                    curr_module_name,
                    scope,
                    &mut expr.index,
                    shadowing,
                )?;
            }
            Expression::FieldAccess(expr) => {
                self.populate_symbol_table_expr(
                    curr_module_name,
                    scope,
                    &mut expr.expr,
                    shadowing,
                )?;
            }
            Expression::NamedStruct(expr) => {
                for (_, expr) in &mut expr.struct_literal.fields {
                    self.populate_symbol_table_expr(curr_module_name, scope, expr, shadowing)?;
                }
            }
            Expression::Lambda(expr) => {
                let lambda_scope = self.symbol_table.new_scope(scope)?;
                for arg in &mut expr.argument_list {
                    let og_name = arg.arg_name.clone();
                    let unique_name = self.symbol_table.ensure_unique_name(
                        scope,
                        &og_name,
                        SymbolType::Identifier,
                    );

                    let idx = self.symbol_table.add_symbol_to_scope(
                        lambda_scope,
                        Symbol {
                            qualified_name: unique_name,
                            name: og_name,
                            symbol_type: SymbolType::Identifier,
                            value_type: arg.arg_type.clone(),
                            exported: false,
                            mutable: true,
                        },
                    )?;

                    arg.symbol_idx = (lambda_scope, idx);
                }
                self.populate_symbol_table_codeblock(
                    curr_module_name,
                    lambda_scope,
                    &mut expr.function_body,
                    shadowing,
                )?;
            }
            Expression::Range(expr) => {
                self.populate_symbol_table_expr(
                    curr_module_name,
                    scope,
                    &mut expr.start,
                    shadowing,
                )?;
                self.populate_symbol_table_expr(curr_module_name, scope, &mut expr.end, shadowing)?;
            }
            Expression::If(expr) => {
                let true_scope = self.symbol_table.new_scope(scope)?;
                self.populate_symbol_table_codeblock(
                    curr_module_name,
                    true_scope,
                    &mut expr.true_branch,
                    shadowing,
                )?;
                if let Some(else_branch) = &mut expr.else_branch {
                    let else_scope = self.symbol_table.new_scope(scope)?;
                    self.populate_symbol_table_codeblock(
                        curr_module_name,
                        else_scope,
                        else_branch,
                        shadowing,
                    )?;
                }
            }
            Expression::For(expr) => {
                let for_scope = self.symbol_table.new_scope(scope)?;

                let og_name = expr.binding.clone();
                let unique_name =
                    self.symbol_table
                        .ensure_unique_name(scope, &og_name, SymbolType::Identifier);

                let idx = self.symbol_table.add_symbol_to_scope(
                    for_scope,
                    Symbol {
                        qualified_name: unique_name,
                        name: og_name,
                        symbol_type: SymbolType::Identifier,
                        value_type: expr.binding_type.clone(),
                        exported: false,
                        mutable: false,
                    },
                )?;

                expr.symbol_idx = (for_scope, idx);

                self.populate_symbol_table_codeblock(
                    curr_module_name,
                    for_scope,
                    &mut expr.body,
                    shadowing,
                )?;
            }
            Expression::BuiltinTarget(expr) => {
                self.populate_symbol_table_expr(curr_module_name, scope, expr, shadowing)?;
            }
            Expression::Placeholder => {}
            Expression::Break => {}
            Expression::Continue => {}
        }
        Ok(())
    }
}
