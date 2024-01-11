use std::collections::HashMap;

use crate::{
    ast::{CodeBlock, Expression, FunctionCall, Variable, VariableDecl},
    parser::Program,
};

#[derive(Debug, Clone)]
pub struct Symbol {
    pub symbol_type: SymbolType,
    pub exported: bool,
}

#[derive(Debug, Clone)]
pub enum SymbolType {
    Function,
    Variable,
    Type,
}

#[derive(Debug, Clone, Default)]
pub struct SemanticAnalyzer {
    pub symbol_table: HashMap<String, Symbol>,
}

impl SemanticAnalyzer {
    pub fn resolve_name_expr(
        defined_symbols: &HashMap<String, Symbol>,
        expr: &mut Expression,
    ) -> Result<(), String> {
        match expr {
            Expression::VariableDecl(var_decl) => {
                SemanticAnalyzer::resolve_name_expr(defined_symbols, &mut var_decl.var_value)?;
            }
            Expression::Literal(_) => {}
            Expression::BinaryOp(op) => {
                SemanticAnalyzer::resolve_name_expr(defined_symbols, &mut op.lhs)?;
                SemanticAnalyzer::resolve_name_expr(defined_symbols, &mut op.rhs)?;
            }
            Expression::UnaryOp(op) => {
                SemanticAnalyzer::resolve_name_expr(defined_symbols, &mut op.operand)?;
            }
            Expression::FunctionCall(func_call) => {
                let FunctionCall {
                    func_name,
                    arguments,
                } = func_call;

                for arg in arguments {
                    SemanticAnalyzer::resolve_name_expr(defined_symbols, arg)?;
                }

                if !defined_symbols.contains_key(func_name) {
                    return Err(format!("Function '{func_name}' is not defined"));
                }
            }
            Expression::Variable(var) => {
                let Variable { name } = var;

                if !defined_symbols.contains_key(name) {
                    return Err(format!("Identifier '{name}' is not defined"));
                }
            }
            Expression::Return(ret) => SemanticAnalyzer::resolve_name_expr(defined_symbols, ret)?,
            Expression::Assignment(assignment) => {
                SemanticAnalyzer::resolve_name_expr(defined_symbols, &mut assignment.rhs)?;
            }
            Expression::AnonStruct(anon_struct) => {
                for (_, expr) in &mut anon_struct.fields {
                    SemanticAnalyzer::resolve_name_expr(defined_symbols, expr)?
                }
            }
            Expression::ArrayLiteral(arr) => {
                for expr in &mut arr.elements {
                    SemanticAnalyzer::resolve_name_expr(defined_symbols, expr)?;
                }
            }
            Expression::ArrayAccess(arr_access) => {
                SemanticAnalyzer::resolve_name_expr(defined_symbols, &mut arr_access.expr)?;
                SemanticAnalyzer::resolve_name_expr(defined_symbols, &mut arr_access.index)?;
            }
            Expression::FieldAccess(field_access) => {
                SemanticAnalyzer::resolve_name_expr(defined_symbols, &mut field_access.expr)?;
            }
            Expression::NamedStruct(named_struct) => {
                for (_, expr) in &mut named_struct.struct_literal.fields {
                    SemanticAnalyzer::resolve_name_expr(defined_symbols, expr)?;
                }
            }
            Expression::Range(range) => {
                SemanticAnalyzer::resolve_name_expr(defined_symbols, &mut range.start)?;
                SemanticAnalyzer::resolve_name_expr(defined_symbols, &mut range.end)?;
                SemanticAnalyzer::resolve_name_expr(defined_symbols, &mut range.step)?;
            }
            Expression::JS(_) => {}
            Expression::If(if_expr) => {
                SemanticAnalyzer::resolve_name_expr(defined_symbols, &mut if_expr.cond)?;
                SemanticAnalyzer::resolve_names_codeblock(
                    defined_symbols,
                    &mut if_expr.true_branch,
                )?;

                if let Some(else_branch) = &mut if_expr.else_branch {
                    SemanticAnalyzer::resolve_names_codeblock(defined_symbols, else_branch)?;
                }
            }
            Expression::For(for_expr) => {
                SemanticAnalyzer::resolve_name_expr(defined_symbols, &mut for_expr.iterator)?;

                let mut defined_names = defined_symbols.clone();
                defined_names.insert(
                    for_expr.binding.clone(),
                    Symbol {
                        symbol_type: SymbolType::Variable,
                        exported: false,
                    },
                );

                SemanticAnalyzer::resolve_names_codeblock(&defined_names, &mut for_expr.body)?;
            }
            Expression::Placeholder => {}
            Expression::Break => {}
            Expression::Continue => {}
        }

        Ok(())
    }

    pub fn resolve_names_codeblock(
        defined_symbols: &HashMap<String, Symbol>,
        codeblock: &mut CodeBlock,
    ) -> Result<(), String> {
        let mut defined_symbols = defined_symbols.clone();

        for expr in &mut codeblock.expressions {
            SemanticAnalyzer::resolve_name_expr(&defined_symbols, expr)?;

            if let Expression::VariableDecl(var_decl) = expr {
                defined_symbols.insert(
                    var_decl.var_name.clone(),
                    Symbol {
                        symbol_type: SymbolType::Variable,
                        exported: false,
                    },
                );
            }
        }

        Ok(())
    }

    pub fn resolve_names(&mut self, program: &mut Program) -> Result<(), String> {
        for module in &mut program.modules {
            let mut defined_symbols: HashMap<String, Symbol> = HashMap::new();
            for func in &module.function_defs {
                let mut defined_arguments = Vec::new();
                for arg in &func.argument_list {
                    if defined_arguments.contains(&arg.arg_name) {
                        return Err(format!("Duplicate argument '{}'", arg.arg_name));
                    }

                    defined_arguments.push(arg.arg_name.clone())
                }

                if defined_symbols.contains_key(&func.func_name) {
                    return Err(format!(
                        "Identifier '{}' is already defined",
                        func.func_name
                    ));
                }

                defined_symbols.insert(
                    func.func_name.clone(),
                    Symbol {
                        symbol_type: SymbolType::Function,
                        exported: func.export,
                    },
                );
            }

            for var in &module.toplevel_scope.expressions {
                if let Expression::VariableDecl(var_decl) = var {
                    if var_decl.var_name != "_" && defined_symbols.contains_key(&var_decl.var_name)
                    {
                        return Err(format!(
                            "Top-level variable '{}' is already defined",
                            var_decl.var_name
                        ));
                    }

                    defined_symbols.insert(
                        var_decl.var_name.clone(),
                        Symbol {
                            symbol_type: SymbolType::Variable,
                            exported: false,
                        },
                    );
                }
            }

            for func in &mut module.function_defs {
                let mut defined_names = defined_symbols.clone();

                for arg in &func.argument_list {
                    defined_names.insert(
                        arg.arg_name.clone(),
                        Symbol {
                            symbol_type: SymbolType::Variable,
                            exported: false,
                        },
                    );
                }

                SemanticAnalyzer::resolve_names_codeblock(&defined_names, &mut func.function_body)?;
            }

            for var in &mut module.toplevel_scope.expressions {
                match var {
                    Expression::VariableDecl(var_decl) => {
                        let VariableDecl {
                            var_name,
                            var_type,
                            var_value,
                            is_mutable,
                            is_env,
                        } = var_decl;

                        SemanticAnalyzer::resolve_name_expr(&defined_symbols, var_value)?;
                    }
                    _ => unreachable!("Invalid toplevel expression only let bindings allowed"),
                }
            }
        }

        Ok(())
    }
}
