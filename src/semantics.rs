use crate::{
    ast::{CodeBlock, Expression, FunctionCall, Variable, VariableDecl},
    parser::Program,
};

#[derive(Debug, Clone, Default)]
pub struct SemanticAnalyzer {}

impl SemanticAnalyzer {
    pub fn resolve_name_expr(
        defined_names: &Vec<String>,
        expr: &mut Expression,
    ) -> Result<(), String> {
        match expr {
            Expression::VariableDecl(var_decl) => {
                SemanticAnalyzer::resolve_name_expr(defined_names, &mut var_decl.var_value)?;
            }
            Expression::Literal(_) => {}
            Expression::BinaryOp(op) => {
                SemanticAnalyzer::resolve_name_expr(defined_names, &mut op.lhs)?;
                SemanticAnalyzer::resolve_name_expr(defined_names, &mut op.rhs)?;
            }
            Expression::UnaryOp(op) => {
                SemanticAnalyzer::resolve_name_expr(defined_names, &mut op.operand)?;
            }
            Expression::FunctionCall(func_call) => {
                let FunctionCall {
                    func_module,
                    func_name,
                    arguments,
                } = func_call;

                for arg in arguments {
                    SemanticAnalyzer::resolve_name_expr(defined_names, arg)?;
                }

                let mut found = false;
                for func in defined_names {
                    if func == func_name {
                        found = true;
                        break;
                    }
                }

                if !found {
                    return Err(format!("Function '{func_name}' is not defined"));
                }
            }
            Expression::Variable(var) => {
                let Variable { var_module, name } = var;

                let mut found = false;
                for var_name in defined_names {
                    if var_name == name {
                        found = true;
                        break;
                    }
                }

                if !found {
                    return Err(format!("Identifier '{name}' is not defined"));
                }
            }
            Expression::Return(ret) => SemanticAnalyzer::resolve_name_expr(defined_names, ret)?,
            Expression::Assignment(assignment) => {
                SemanticAnalyzer::resolve_name_expr(defined_names, &mut assignment.rhs)?;
            }
            Expression::AnonStruct(anon_struct) => {
                for (_, expr) in &mut anon_struct.fields {
                    SemanticAnalyzer::resolve_name_expr(defined_names, expr)?
                }
            }
            Expression::ArrayLiteral(arr) => {
                for expr in &mut arr.elements {
                    SemanticAnalyzer::resolve_name_expr(defined_names, expr)?;
                }
            }
            Expression::ArrayAccess(arr_access) => {
                SemanticAnalyzer::resolve_name_expr(defined_names, &mut arr_access.expr)?;
                SemanticAnalyzer::resolve_name_expr(defined_names, &mut arr_access.index)?;
            }
            Expression::FieldAccess(field_access) => {
                SemanticAnalyzer::resolve_name_expr(defined_names, &mut field_access.expr)?;
            }
            Expression::NamedStruct(named_struct) => {
                for (_, expr) in &mut named_struct.struct_literal.fields {
                    SemanticAnalyzer::resolve_name_expr(defined_names, expr)?;
                }
            }
            Expression::Range(range) => {
                SemanticAnalyzer::resolve_name_expr(defined_names, &mut range.start)?;
                SemanticAnalyzer::resolve_name_expr(defined_names, &mut range.end)?;
                SemanticAnalyzer::resolve_name_expr(defined_names, &mut range.step)?;
            }
            Expression::JS(_) => {}
            Expression::If(if_expr) => {
                SemanticAnalyzer::resolve_name_expr(defined_names, &mut if_expr.cond)?;
                SemanticAnalyzer::resolve_names_codeblock(defined_names, &mut if_expr.true_branch)?;

                if let Some(else_branch) = &mut if_expr.else_branch {
                    SemanticAnalyzer::resolve_names_codeblock(defined_names, else_branch)?;
                }
            }
            Expression::For(for_expr) => {
                SemanticAnalyzer::resolve_name_expr(defined_names, &mut for_expr.iterator)?;

                let mut defined_names = defined_names.clone();
                defined_names.push(for_expr.binding.clone());

                SemanticAnalyzer::resolve_names_codeblock(&defined_names, &mut for_expr.body)?;
            }
            Expression::Placeholder => {}
            Expression::Break => {}
            Expression::Continue => {}
        }

        Ok(())
    }

    pub fn resolve_names_codeblock(
        defined_names: &Vec<String>,
        codeblock: &mut CodeBlock,
    ) -> Result<(), String> {
        let mut defined_names = defined_names.clone();

        for expr in &mut codeblock.expressions {
            SemanticAnalyzer::resolve_name_expr(&defined_names, expr)?;

            if let Expression::VariableDecl(var_decl) = expr {
                defined_names.push(var_decl.var_name.clone());
            }
        }

        Ok(())
    }

    pub fn resolve_names(program: &mut Program) -> Result<(), String> {
        let mut defined_names = Vec::new();

        for func in &program.main_module.function_defs {
            let mut defined_arguments = Vec::new();
            for arg in &func.argument_list {
                if defined_arguments.contains(&arg.arg_name) {
                    return Err(format!("Duplicate argument '{}'", arg.arg_name));
                }

                defined_arguments.push(arg.arg_name.clone())
            }

            if defined_names.contains(&func.func_name) {
                return Err(format!(
                    "Identifier '{}' is already defined",
                    func.func_name
                ));
            }

            defined_names.push(func.func_name.clone())
        }

        for var in &program.main_module.toplevel_scope.expressions {
            if let Expression::VariableDecl(var_decl) = var {
                if var_decl.var_name != "_" && defined_names.contains(&var_decl.var_name) {
                    return Err(format!(
                        "Top-level variable '{}' is already defined",
                        var_decl.var_name
                    ));
                }
                defined_names.push(var_decl.var_name.clone())
            }
        }

        for func in &mut program.main_module.function_defs {
            let mut defined_names = defined_names.clone();

            for arg in &func.argument_list {
                defined_names.push(arg.arg_name.clone());
            }

            SemanticAnalyzer::resolve_names_codeblock(&defined_names, &mut func.function_body)?;
        }

        for var in &mut program.main_module.toplevel_scope.expressions {
            match var {
                Expression::VariableDecl(var_decl) => {
                    let VariableDecl {
                        var_name,
                        var_type,
                        var_value,
                        is_mutable,
                        is_env,
                    } = var_decl;

                    SemanticAnalyzer::resolve_name_expr(&defined_names, var_value)?;
                }
                _ => unreachable!("Invalid toplevel expression only let bindings allowed"),
            }
        }

        Ok(())
    }
}
