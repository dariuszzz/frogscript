use crate::{
    ast::*,
    lexer::{FStringPart, Literal},
    parser::Program,
};

use crate::symbol_table::*;

#[derive(Debug)]
pub struct NameResolver<'a> {
    pub symbol_table: &'a mut SymbolTable,
}

impl<'a> NameResolver<'a> {
    pub fn new(symbol_table: &'a mut SymbolTable) -> Self {
        Self { symbol_table }
    }

    pub fn resolve_names(&mut self, program: &mut Program) -> Result<(), String> {
        let mut scope = 0;
        for module in &mut program.modules {
            let curr_module_name = module.module_name.as_str();
            for type_def in &mut module.type_defs {
                self.resolve_type_name(curr_module_name, &scope, &mut type_def.underlying_ty)?;
            }

            self.resolve_names_codeblock(curr_module_name, &mut scope, &mut module.toplevel_scope)?;

            for func_def in &mut module.function_defs {
                let module_scope = self
                    .symbol_table
                    .get_module_scope(&module.module_name)
                    .unwrap();
                self.resolve_type_name(curr_module_name, &module_scope, &mut func_def.return_type)?;
                for arg in &mut func_def.argument_list {
                    self.resolve_type_name(curr_module_name, &module_scope, &mut arg.arg_type)?;
                }

                scope += 1;

                self.resolve_names_codeblock(
                    curr_module_name,
                    &mut scope,
                    &mut func_def.function_body,
                )?;
            }

            scope += 1;
        }

        Ok(())
    }

    fn resolve_names_codeblock(
        &mut self,
        curr_module_name: &str,
        scope: &mut usize,
        codeblock: &mut CodeBlock,
    ) -> Result<(), String> {
        for expr in &mut codeblock.expressions {
            self.resolve_names_expr(curr_module_name, scope, expr)?;
        }

        Ok(())
    }

    fn resolve_type_name(
        &mut self,
        curr_module_name: &str,
        scope: &usize,
        kind: &mut Type,
    ) -> Result<(), String> {
        match kind {
            Type::Infer => {}
            Type::Void
            | Type::Int
            | Type::Any
            | Type::Uint
            | Type::Float
            | Type::String
            | Type::Boolean => {}
            Type::Custom(custom) => {
                let CustomType { name } = custom;

                let name_parts = name.split("::").collect::<Vec<_>>();
                let module_parts = name_parts
                    .clone()
                    .into_iter()
                    .take(name_parts.len() - 1)
                    .collect::<Vec<_>>();
                let module_name = module_parts.join("::");

                let scope_idx = if name_parts.len() == 1 {
                    scope.clone()
                } else {
                    let scope = self
                        .symbol_table
                        .get_module_scope(&module_name)
                        .expect(&format!("Couldnt resolve module {module_name:?}"));

                    scope.clone()
                };

                match self.symbol_table.find_symbol_rec(
                    scope_idx,
                    &name_parts.last().unwrap(),
                    SymbolType::Type,
                ) {
                    Ok((_idx, _symbol)) => {
                        return Ok(());
                    }
                    Err(_) => return Err(format!("Type not found `{}`", name)),
                };
            }
            Type::Pointer(inner)
            | Type::Reference(inner)
            | Type::Structural(inner)
            | Type::Array(inner) => {
                self.resolve_type_name(curr_module_name, scope, inner)?;
            }
            Type::Function(func) => {
                let FunctionType {
                    env_args,
                    args,
                    ret,
                } = func;

                for env_arg in env_args {
                    self.resolve_type_name(curr_module_name, scope, env_arg)?;
                }
                for arg in args {
                    self.resolve_type_name(curr_module_name, scope, arg)?;
                }

                self.resolve_type_name(curr_module_name, scope, ret)?;
            }
            Type::Struct(struct_type) => {
                let StructDef { fields } = struct_type;

                for field in fields {
                    self.resolve_type_name(curr_module_name, scope, &mut field.field_type)?;
                }
            }
        }

        Ok(())
    }

    fn flatten_import(import: &Import, base: String) -> Vec<Import> {
        let qualified_name = if base.is_empty() {
            import.name.clone()
        } else {
            format!("{}::{}", base, import.name)
        };

        let mut imports = vec![Import {
            name: qualified_name.clone(),
            alias: import.alias.clone(),
            children: Vec::new(),
        }];

        for child in &import.children {
            imports.append(&mut Self::flatten_import(child, qualified_name.clone()));
        }

        return imports;
    }

    fn get_imports_rec(&self, scope: usize) -> Result<Vec<Import>, String> {
        let mut imports = Vec::new();

        let mut scope_idx = Some(scope);
        while let Some(curr_scope_idx) = scope_idx {
            let curr_scope = self.symbol_table.get_scope(curr_scope_idx).unwrap();

            let mut curr_scope_imports: Vec<Import> = curr_scope
                .use_statements
                .iter()
                .map(|i| Self::flatten_import(i, String::new()))
                .flatten()
                .collect();

            curr_scope_imports.reverse();
            imports.append(&mut curr_scope_imports);

            scope_idx = curr_scope.parent_scope;
        }

        imports.reverse();

        Ok(imports)
    }

    fn resolve_names_expr(
        &mut self,
        curr_module_name: &str,
        scope: &mut usize,
        expr: &mut Expression,
    ) -> Result<(), String> {
        match expr {
            Expression::BuiltinType(expr) => {
                self.resolve_names_expr(curr_module_name, scope, expr)?;
            }
            Expression::Import(import) => {
                return Ok(());
            }
            Expression::Variable(var) => {
                let name_parts = var.name.split("::").collect::<Vec<_>>();
                let module_parts = name_parts
                    .clone()
                    .into_iter()
                    .take(name_parts.len() - 1)
                    .collect::<Vec<_>>();
                let module_name = module_parts.join("::");

                let imported_symbols = self.get_imports_rec(scope.clone())?;
                let mut resolved: Vec<String> = Vec::new();

                if name_parts.len() == 1 {
                    match self.symbol_table.find_symbol_rec(
                        scope.clone(),
                        &name_parts.last().unwrap(),
                        SymbolType::Identifier,
                    ) {
                        Ok((idx, _)) => {
                            var.symbol_idx = idx;
                            return Ok(());
                        }
                        Err(_) => {} // println!(
                                     //     "Failed to find symbol {:?} in local scope, looking elsewhere",
                                     //     expr.name
                                     // )},
                    };

                    for import in &imported_symbols {
                        if let Some(alias) = &import.alias {
                            // if the name is not qualified and it matches the alias exactly
                            if name_parts.len() == 1 && var.name == *alias {
                                // replace with the qualified name
                                resolved.push(import.name.clone());
                            } // if there is no alias
                        } else {
                            // if the name matches exactly with the ending of an import
                            // eg. name = `foo`, import = `...::foo`
                            let last_part_of_import = import.name.split("::").last().unwrap();
                            if var.name == last_part_of_import {
                                // replace the name with the full import name
                                resolved.push(import.name.clone());
                            }
                        }
                    }
                } else {
                    match self.symbol_table.get_module_scope(&module_name) {
                        Some(scope) => match self.symbol_table.find_symbol_rec(
                            scope.clone(),
                            &name_parts.last().unwrap(),
                            SymbolType::Identifier,
                        ) {
                            Ok((symbol_idx, _)) => {
                                var.symbol_idx = symbol_idx;
                                return Ok(());
                            }
                            Err(_) => {
                                println!("Couldnt find symbol {:?} looking elsewhere", var.name)
                            }
                        },
                        None => {}
                    }

                    for import in &imported_symbols {
                        if let Some(alias) = &import.alias {
                            // if the qualified name starts with the alias `alias::foo`
                            if var.name.starts_with(alias) {
                                // replace the name with `import.name::foo`
                                let new_name =
                                    var.name.strip_prefix(&format!("{alias}::")).unwrap();
                                let new_name = format!("{}::{new_name}", import.name);
                                resolved.push(new_name);
                            }
                        } else {
                            let parts_of_import = import.name.split("::");
                            let last_part_of_import = parts_of_import.clone().last().unwrap();
                            // if the first part of the qualified name matches the end of an import
                            // prepend the rest of the import to the identifier
                            // eg. name = `test::foo`, import = `core::test`
                            if name_parts[0] == last_part_of_import {
                                // `test::foo` -> `foo`
                                let ending_of_iden = var
                                    .name
                                    .strip_prefix(&format!("{last_part_of_import}::"))
                                    .unwrap();
                                // `core::test::foo`
                                let new_name = format!("{}::{ending_of_iden}", import.name);
                                resolved.push(new_name);
                            }
                        }
                    }
                };

                match resolved.len() {
                    1 => var.name = resolved[0].clone(),
                    0 => return Err(format!("Identifier not found: {:?}", var.name)),
                    _ => {
                        return Err(format!(
                            "Ambiguous name: {:?}, found these imports: {resolved:?}",
                            var.name
                        ))
                    }
                }
            }
            Expression::VariableDecl(expr) => {
                self.resolve_names_expr(curr_module_name, scope, &mut expr.var_value)?;
                self.resolve_type_name(curr_module_name, scope, &mut expr.var_type)?;
            }
            Expression::Literal(literal) => match literal {
                Literal::String(parts) => {
                    for part in parts {
                        if let FStringPart::Code(expr) = part {
                            self.resolve_names_expr(curr_module_name, scope, expr)?;
                        }
                    }
                }
                _ => {}
            },
            Expression::BinaryOp(expr) => {
                self.resolve_names_expr(curr_module_name, scope, &mut expr.lhs)?;
                self.resolve_names_expr(curr_module_name, scope, &mut expr.rhs)?;
            }
            Expression::UnaryOp(expr) => {
                self.resolve_names_expr(curr_module_name, scope, &mut expr.operand)?;
            }
            Expression::FunctionCall(expr) => {
                self.resolve_names_expr(curr_module_name, scope, &mut expr.func_expr)?;

                for arg in &mut expr.arguments {
                    self.resolve_names_expr(curr_module_name, scope, arg)?;
                }
            }
            Expression::Return(expr) => {
                if let Some(expr) = expr {
                    self.resolve_names_expr(curr_module_name, scope, expr)?;
                }
            }
            Expression::Assignment(expr) => {
                self.resolve_names_expr(curr_module_name, scope, &mut expr.lhs)?;
                self.resolve_names_expr(curr_module_name, scope, &mut expr.rhs)?;
            }
            Expression::AnonStruct(expr) => {
                for (_, expr) in &mut expr.fields {
                    self.resolve_names_expr(curr_module_name, scope, expr)?;
                }
            }
            Expression::ArrayLiteral(expr) => {
                for elem in &mut expr.elements {
                    self.resolve_names_expr(curr_module_name, scope, elem)?;
                }
            }
            Expression::ArrayAccess(expr) => {
                self.resolve_names_expr(curr_module_name, scope, &mut expr.expr)?;
                self.resolve_names_expr(curr_module_name, scope, &mut expr.index)?;
            }
            Expression::FieldAccess(expr) => {
                self.resolve_names_expr(curr_module_name, scope, &mut expr.expr)?;
            }
            Expression::NamedStruct(expr) => {
                for (_, expr) in &mut expr.struct_literal.fields {
                    self.resolve_names_expr(curr_module_name, scope, expr)?;
                }
            }
            Expression::Lambda(expr) => {
                self.resolve_type_name(curr_module_name, scope, &mut expr.return_type)?;
                for arg in &mut expr.argument_list {
                    self.resolve_type_name(curr_module_name, scope, &mut arg.arg_type)?;
                }

                *scope += 1;
                self.resolve_names_codeblock(curr_module_name, scope, &mut expr.function_body)?;
            }
            Expression::Range(expr) => {
                self.resolve_names_expr(curr_module_name, scope, &mut expr.start)?;
                self.resolve_names_expr(curr_module_name, scope, &mut expr.end)?;
            }
            Expression::If(expr) => {
                self.resolve_names_expr(curr_module_name, scope, &mut expr.cond)?;
                *scope += 1;
                self.resolve_names_codeblock(curr_module_name, scope, &mut expr.true_branch)?;
                if let Some(else_branch) = &mut expr.else_branch {
                    *scope += 1;
                    self.resolve_names_codeblock(curr_module_name, scope, else_branch)?;
                }
            }
            Expression::For(expr) => {
                *scope += 1;
                self.resolve_type_name(curr_module_name, scope, &mut expr.binding_type)?;
                self.resolve_names_expr(curr_module_name, scope, &mut expr.iterator)?;
                self.resolve_names_codeblock(curr_module_name, scope, &mut expr.body)?;
            }
            Expression::BuiltinTarget(expr) => {
                self.resolve_names_expr(curr_module_name, scope, expr)?;
            }
            Expression::Placeholder => {}
            Expression::Break => {}
            Expression::Continue => {}
        }

        Ok(())
    }
}
