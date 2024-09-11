use std::{
    collections::HashMap,
    env::{self, vars},
};

use crate::{
    ast::{CodeBlock, Expression, FunctionCall, Variable, VariableDecl},
    parser::Program,
    CustomType, FunctionType, Lambda, StructDef, TypeKind,
};

#[derive(Debug, Clone)]
pub struct Symbol {
    pub original_name: String,
    pub symbol_type: SymbolType,
    pub exported: bool,
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum SymbolType {
    Identifier,
    Type,
}

#[derive(Debug, Clone, Default)]
pub struct SemanticAnalyzer {
    pub symbol_table: Vec<Symbol>,
}

impl SemanticAnalyzer {
    pub fn find_external_symbol(&self, symbol_type: SymbolType, name: &str) -> Vec<&Symbol> {
        self.symbol_table
            .iter()
            .filter(|s| s.symbol_type == symbol_type && s.original_name == name)
            .collect()
    }

    pub fn resolve_type_name(
        &mut self,
        module_name: &String,
        local_symbols: &HashMap<String, Symbol>,
        kind: &mut TypeKind,
    ) -> Result<(), String> {
        match kind {
            TypeKind::Infer => {}
            TypeKind::Void
            | TypeKind::Int
            | TypeKind::Uint
            | TypeKind::Float
            | TypeKind::String
            | TypeKind::Boolean => {}
            TypeKind::Custom(custom) => {
                let CustomType { name } = custom;

                let split_name = name.split("::").collect::<Vec<_>>();
                if split_name.len() == 1 {
                    let local_type = local_symbols.get(name);
                    if let Some(symbol) = local_type {
                        if symbol.symbol_type != SymbolType::Type {
                            return Err(format!("Identifier '{name}' exists, but is not a type"));
                        }
                    } else {
                        return Err(format!("Type '{name}' is not defined"));
                    }
                } else {
                    let type_symbol = self.find_external_symbol(SymbolType::Type, &name);
                    if type_symbol.len() == 1 {
                        if !type_symbol[0].exported {
                            return Err(format!("Type '{name}' is defined but not exported"));
                        }
                    } else if type_symbol.len() == 0 {
                        return Err(format!("Type '{name}' is not defined"));
                    } else {
                        return Err(format!("Type '{name}' is ambiguous"));
                    }
                }
            }
            TypeKind::Array(inner) => {
                self.resolve_type_name(module_name, local_symbols, &mut inner.type_kind)?;
            }
            TypeKind::Function(func) => {
                let FunctionType {
                    env_args,
                    args,
                    ret,
                } = func;

                for env_arg in env_args {
                    self.resolve_type_name(module_name, local_symbols, &mut env_arg.type_kind)?;
                }
                for arg in args {
                    self.resolve_type_name(module_name, local_symbols, &mut arg.type_kind)?;
                }

                self.resolve_type_name(module_name, local_symbols, &mut ret.type_kind)?;
            }
            TypeKind::Struct(struct_type) => {
                let StructDef { fields } = struct_type;

                for field in fields {
                    self.resolve_type_name(
                        module_name,
                        local_symbols,
                        &mut field.field_type.type_kind,
                    )?;
                }
            }
        }

        Ok(())
    }

    pub fn resolve_name_expr(
        &mut self,
        module_name: &String,
        local_symbols: &HashMap<String, Symbol>,
        expr: &mut Expression,
    ) -> Result<(), String> {
        match expr {
            Expression::Lambda(lambda) => {
                let Lambda {
                    argument_list,
                    return_type,
                    function_body,
                } = lambda;

                let mut local_symbols = local_symbols.clone();

                for arg in argument_list {
                    self.resolve_type_name(
                        module_name,
                        &local_symbols,
                        &mut arg.arg_type.type_kind,
                    )?;

                    local_symbols.insert(
                        arg.arg_name.clone(),
                        Symbol {
                            original_name: arg.arg_name.clone(),
                            symbol_type: SymbolType::Identifier,
                            exported: false,
                        },
                    );
                }
                self.resolve_type_name(module_name, &local_symbols, &mut return_type.type_kind)?;
                self.resolve_names_codeblock(module_name, &local_symbols, function_body)?;
            }
            Expression::VariableDecl(var_decl) => {
                self.resolve_type_name(
                    module_name,
                    local_symbols,
                    &mut var_decl.var_type.type_kind,
                )?;
                self.resolve_name_expr(module_name, local_symbols, &mut var_decl.var_value)?;
            }
            Expression::Literal(_) => {}
            Expression::BinaryOp(op) => {
                self.resolve_name_expr(module_name, local_symbols, &mut op.lhs)?;
                self.resolve_name_expr(module_name, local_symbols, &mut op.rhs)?;
            }
            Expression::UnaryOp(op) => {
                self.resolve_name_expr(module_name, local_symbols, &mut op.operand)?;
            }
            Expression::FunctionCall(func_call) => {
                let FunctionCall {
                    func_name,
                    arguments,
                } = func_call;

                //if function comes from another module
                if func_name.split("::").count() > 1 {
                    let identifiers_with_the_same_name =
                        self.find_external_symbol(SymbolType::Identifier, &func_name);

                    if identifiers_with_the_same_name.len() == 1 {
                        let iden = identifiers_with_the_same_name[0];
                        if !iden.exported {
                            return Err(format!("External function '{func_name}' found, but it is not marked as `export`"));
                        }
                        // symbol exists
                    } else if identifiers_with_the_same_name.len() > 1 {
                        return Err(format!("Ambiguous function call '{func_name}'"));
                    } else {
                        return Err(format!("External function '{func_name}' is not defined"));
                    }
                } else {
                    let local_func = local_symbols.get(func_name);
                    if let Some(symbol) = local_func {
                        if symbol.symbol_type == SymbolType::Type {
                            return Err(format!("Function '{func_name}' is not defined"));
                        }
                    } else {
                        return Err(format!("Function '{func_name}' is not defined"));
                    }
                }

                for arg in arguments {
                    self.resolve_name_expr(module_name, local_symbols, arg)?;
                }
            }
            Expression::Variable(var) => {
                let Variable { name } = var;

                if name.split("::").count() > 1 {
                    let identifiers_with_the_same_name =
                        self.find_external_symbol(SymbolType::Identifier, &name);

                    if identifiers_with_the_same_name.len() == 1 {
                        let iden = identifiers_with_the_same_name[0];
                        if !iden.exported {
                            return Err(format!("External variable '{name}' found, but it is not marked as `export`"));
                        }
                        // symbol exists
                    } else if identifiers_with_the_same_name.len() > 1 {
                        return Err(format!("Ambiguous identifier '{name}'"));
                    } else {
                        return Err(format!("External identifier '{name}' is not defined"));
                    }
                } else {
                    let local_func = local_symbols.get(name);
                    if let Some(symbol) = local_func {
                        if symbol.symbol_type != SymbolType::Identifier {
                            return Err(format!("Identifier '{name}' exists, but does not refer to a variable or function"));
                        }
                    } else {
                        return Err(format!("Identifier '{name}' is not defined"));
                    }
                }
            }
            Expression::Return(ret) => self.resolve_name_expr(module_name, local_symbols, ret)?,
            Expression::Assignment(assignment) => {
                self.resolve_name_expr(module_name, local_symbols, &mut assignment.rhs)?;
            }
            Expression::AnonStruct(anon_struct) => {
                for (_, expr) in &mut anon_struct.fields {
                    self.resolve_name_expr(module_name, local_symbols, expr)?
                }
            }
            Expression::ArrayLiteral(arr) => {
                for expr in &mut arr.elements {
                    self.resolve_name_expr(module_name, local_symbols, expr)?;
                }
            }
            Expression::ArrayAccess(arr_access) => {
                self.resolve_name_expr(module_name, local_symbols, &mut arr_access.expr)?;
                self.resolve_name_expr(module_name, local_symbols, &mut arr_access.index)?;
            }
            Expression::FieldAccess(field_access) => {
                self.resolve_name_expr(module_name, local_symbols, &mut field_access.expr)?;
            }
            Expression::NamedStruct(named_struct) => {
                for (_, expr) in &mut named_struct.struct_literal.fields {
                    self.resolve_name_expr(module_name, local_symbols, expr)?;
                }
            }
            Expression::Range(range) => {
                self.resolve_name_expr(module_name, local_symbols, &mut range.start)?;
                self.resolve_name_expr(module_name, local_symbols, &mut range.end)?;
            }
            Expression::JS(_) => {}
            Expression::If(if_expr) => {
                self.resolve_name_expr(module_name, local_symbols, &mut if_expr.cond)?;
                self.resolve_names_codeblock(module_name, local_symbols, &mut if_expr.true_branch)?;

                if let Some(else_branch) = &mut if_expr.else_branch {
                    self.resolve_names_codeblock(module_name, local_symbols, else_branch)?;
                }
            }
            Expression::For(for_expr) => {
                self.resolve_name_expr(module_name, local_symbols, &mut for_expr.iterator)?;

                let mut local_symbols = local_symbols.clone();
                local_symbols.insert(
                    for_expr.binding.clone(),
                    Symbol {
                        original_name: for_expr.binding.clone(),
                        symbol_type: SymbolType::Identifier,
                        exported: false,
                    },
                );

                self.resolve_names_codeblock(module_name, &local_symbols, &mut for_expr.body)?;
            }
            Expression::Placeholder => {}
            Expression::Break => {}
            Expression::Continue => {}
        }

        Ok(())
    }

    pub fn resolve_names_codeblock(
        &mut self,
        module_name: &String,
        local_symbols: &HashMap<String, Symbol>,
        codeblock: &mut CodeBlock,
    ) -> Result<(), String> {
        let mut local_symbols = local_symbols.clone();

        for expr in &mut codeblock.expressions {
            self.resolve_name_expr(module_name, &local_symbols, expr)?;

            if let Expression::VariableDecl(var_decl) = expr {
                local_symbols.insert(
                    var_decl.var_name.clone(),
                    Symbol {
                        original_name: var_decl.var_name.clone(),
                        symbol_type: SymbolType::Identifier,
                        exported: false,
                    },
                );
            }
        }

        Ok(())
    }

    pub fn resolve_names(&mut self, program: &mut Program) -> Result<(), String> {
        let mut local_symbols_by_module: HashMap<String, HashMap<String, Symbol>> = HashMap::new();
        for module in &mut program.modules {
            println!("resolving names in {:?}", module.module_name);
            local_symbols_by_module.insert(module.module_name.clone(), HashMap::new());

            let local_symbols = local_symbols_by_module
                .get_mut(&module.module_name)
                .unwrap();

            for custom_type in &module.type_defs {
                if self
                    .find_external_symbol(SymbolType::Type, &custom_type.name)
                    .len()
                    > 1
                {
                    return Err(format!("Type '{}' is already defined", custom_type.name));
                }

                self.symbol_table.push(Symbol {
                    original_name: format!("{}::{}", module.module_name, custom_type.name),
                    symbol_type: SymbolType::Type,
                    exported: custom_type.export,
                });

                local_symbols.insert(
                    custom_type.name.clone(),
                    Symbol {
                        original_name: custom_type.name.clone(),
                        symbol_type: SymbolType::Type,
                        exported: custom_type.export,
                    },
                );
            }

            for func in &mut module.function_defs {
                if self
                    .find_external_symbol(SymbolType::Identifier, &func.func_name)
                    .len()
                    > 1
                {
                    return Err(format!(
                        "Identifier '{}' is already defined",
                        func.func_name
                    ));
                }

                self.symbol_table.push(Symbol {
                    original_name: format!("{}::{}", module.module_name, func.func_name),
                    symbol_type: SymbolType::Identifier,
                    exported: func.export,
                });

                local_symbols.insert(
                    func.func_name.clone(),
                    Symbol {
                        original_name: func.func_name.clone(),
                        symbol_type: SymbolType::Identifier,
                        exported: func.export,
                    },
                );
            }

            for var in &module.toplevel_scope.expressions {
                if let Expression::VariableDecl(var_decl) = var {
                    if var_decl.var_name != "_"
                        && self
                            .find_external_symbol(SymbolType::Identifier, &var_decl.var_name)
                            .len()
                            > 1
                    {
                        return Err(format!(
                            "Top-level variable '{}' is already defined",
                            var_decl.var_name
                        ));
                    }

                    self.symbol_table.push(Symbol {
                        original_name: format!("{}::{}", module.module_name, var_decl.var_name),
                        symbol_type: SymbolType::Identifier,
                        exported: false,
                    });

                    local_symbols.insert(
                        var_decl.var_name.clone(),
                        Symbol {
                            original_name: var_decl.var_name.clone(),
                            symbol_type: SymbolType::Identifier,
                            exported: false,
                        },
                    );
                }
            }
        }

        for module in &mut program.modules {
            let local_symbols = local_symbols_by_module
                .get(&module.module_name.clone())
                .unwrap();

            for func in &mut module.function_defs {
                let mut local_symbols = local_symbols.clone();
                let mut defined_arguments = Vec::new();

                self.resolve_type_name(
                    &module.module_name,
                    &local_symbols,
                    &mut func.return_type.type_kind,
                )?;

                for arg in &mut func.argument_list {
                    self.resolve_type_name(
                        &module.module_name,
                        &local_symbols,
                        &mut arg.arg_type.type_kind,
                    )?;

                    local_symbols.insert(
                        arg.arg_name.clone(),
                        Symbol {
                            original_name: arg.arg_name.clone(),
                            symbol_type: SymbolType::Identifier,
                            exported: false,
                        },
                    );

                    if defined_arguments.contains(&arg.arg_name) {
                        return Err(format!("Duplicate argument '{}'", arg.arg_name));
                    }

                    defined_arguments.push(arg.arg_name.clone())
                }

                self.resolve_names_codeblock(
                    &module.module_name,
                    &local_symbols,
                    &mut func.function_body,
                )?;
            }

            for var in &mut module.toplevel_scope.expressions {
                match var {
                    Expression::VariableDecl(var_decl) => {
                        let VariableDecl { var_value, .. } = var_decl;

                        let local_symbols = local_symbols.clone();
                        self.resolve_name_expr(&module.module_name, &local_symbols, var_value)?;
                    }
                    // This is always the main() function call inserted by the parser
                    Expression::FunctionCall(func_call) => {
                        func_call.func_name =
                            format!("{}::{}", module.module_name, func_call.func_name);
                    }
                    _ => unreachable!("Invalid toplevel expression only let bindings allowed"),
                }
            }
        }

        Ok(())
    }
}
