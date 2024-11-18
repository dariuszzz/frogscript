use std::{
    collections::{HashMap, HashSet},
    convert::identity,
    fmt::Debug,
    time::Instant,
};

use crate::{
    ast::{CodeBlock, Expression, FunctionCall, Variable, VariableDecl},
    parser::Program,
    symbol_table::{Scope, Symbol, SymbolTable, SymbolType},
    Arena, BinaryOperation, CustomType, FStringPart, FunctionType, Import, Lambda, Literal, Module,
    NamedStruct, StructDef, StructField, Type, UnaryOp, UnaryOperation,
};

#[derive(Debug, Clone, Default)]
pub struct SemanticAnalyzer {
    pub unique_name_suffix: usize,
    pub symbol_table: SymbolTable,
    pub module_to_scope: HashMap<String, usize>,
}

impl SemanticAnalyzer {
    fn figure_out_unified_type(&mut self, lhs: &Type, rhs: &Type) -> Result<Type, String> {
        let out = match (lhs, rhs) {
            (Type::Infer, Type::Infer) => return Err(format!("Cant infer type")),
            (Type::Reference(lhs), Type::Pointer(rhs)) => {
                Type::Reference(Box::new(self.figure_out_unified_type(lhs, rhs)?))
            }
            (Type::Pointer(lhs), Type::Reference(rhs)) => {
                Type::Reference(Box::new(self.figure_out_unified_type(lhs, rhs)?))
            }
            (Type::Infer, rhs) => rhs.clone(),
            (lhs, Type::Infer) => lhs.clone(),
            (Type::Any, Type::Any) => Type::Any,
            (lhs, Type::Any) => lhs.clone(),
            (Type::Any, rhs) => rhs.clone(),
            (lhs, rhs) if lhs == rhs => lhs.clone(),
            (Type::Array(lhs_inner), Type::Array(rhs_inner)) => Type::Array(Box::new(
                self.figure_out_unified_type(lhs_inner, rhs_inner)?,
            )),
            (
                Type::Function(FunctionType {
                    env_args: lhs_env,
                    args: lhs_args,
                    ret: lhs_ret,
                }),
                Type::Function(FunctionType {
                    env_args: rhs_env,
                    args: rhs_args,
                    ret: rhs_ret,
                }),
            ) => {
                if lhs_env.len() != rhs_env.len() || lhs_args.len() != rhs_args.len() {
                    return Err(format!("Lhs != rhs: {lhs:?} != {rhs:?}"));
                }

                let mut unified_type = FunctionType {
                    env_args: Vec::new(),
                    args: Vec::new(),
                    ret: Box::new(Type::Infer),
                };
                unified_type.ret = Box::new(self.figure_out_unified_type(lhs_ret, rhs_ret)?);

                for (lhs_env, rhs_env) in lhs_env.iter().zip(rhs_env) {
                    let unified_env = self.figure_out_unified_type(lhs_env, rhs_env)?;
                    unified_type.env_args.push(unified_env);
                }

                for (lhs_arg, rhs_arg) in lhs_args.iter().zip(rhs_args) {
                    let unified_arg = self.figure_out_unified_type(lhs_arg, rhs_arg)?;
                    unified_type.args.push(unified_arg);
                }

                Type::Function(unified_type)
            }
            _ => return Err(format!("Lhs != rhs: {lhs:?} != {rhs:?}")),
        };

        return Ok(out);
    }

    fn get_var_scope(&self, scope: usize, identifier: &str) -> (usize, String) {
        let name_parts = identifier.split("::").collect::<Vec<_>>();
        let module_parts = name_parts
            .clone()
            .into_iter()
            .take(name_parts.len() - 1)
            .collect::<Vec<_>>();
        let module_name = module_parts.join("::");
        let var_name = name_parts.last().unwrap().to_string();

        if name_parts.len() == 1 {
            return (scope, var_name);
        } else {
            let scope = self
                .module_to_scope
                .get(&module_name)
                .expect(&format!("Couldnt resolve module {module_name:?}"));

            return (scope.clone(), var_name);
        };
    }

    fn set_type_if_expr_is_var(
        &mut self,
        scope: &usize,
        expr: &Expression,
        ty: Type,
    ) -> Result<(), String> {
        if matches!(ty, Type::Any) {
            return Ok(());
        }

        if let Expression::Variable(var) = expr {
            let (scope, var_name) = self.get_var_scope(*scope, &var.name);
            let symbol = self
                .symbol_table
                .find_symbol_rec_mut(scope, &var_name, SymbolType::Identifier)
                .unwrap();

            symbol.value_type = ty;
        }

        return Ok(());
    }

    fn replace_builtin_type(&mut self, scope: &mut usize, expr: &mut Expression) {
        if let Expression::BuiltinType(expr_copy) = expr {
            if let Ok(inner_ty) = self.typecheck_expr(scope, expr_copy) {
                *expr = Expression::Literal(Literal::String(vec![FStringPart::String(format!(
                    "{inner_ty}"
                ))]));
            };
        }
    }

    fn typecheck_expr(&mut self, scope: &mut usize, expr: &mut Expression) -> Result<Type, String> {
        match expr {
            expr @ Expression::BuiltinType(_) => {
                self.replace_builtin_type(scope, expr);
                return Ok(Type::String);
            }
            //     let inner_ty = self.typecheck_expr(scope, inner.as_mut())?;

            //     *expr = Expression::Literal(Literal::String(vec![FStringPart::String(format!(
            //         "{inner_ty:?}"
            //     ))]));

            //     return Ok(Type::String);
            // }
            Expression::VariableDecl(expr) => {
                let rhs = self.typecheck_expr(scope, &mut expr.var_value)?;
                let unified = self.figure_out_unified_type(&rhs, &expr.var_type)?;
                expr.var_type = unified.clone();
                //no need to use get_var_scope since this is a declaration so its in the local scope
                let symbol = self.symbol_table.find_symbol_rec_mut(
                    *scope,
                    &expr.var_name,
                    SymbolType::Identifier,
                )?;
                symbol.value_type = unified.clone();
                return Ok(unified);
            }
            Expression::Variable(expr) => {
                let (scope, var_name) = self.get_var_scope(*scope, &expr.name);

                match self
                    .symbol_table
                    .find_symbol_rec(scope, &var_name, SymbolType::Identifier)
                {
                    Ok(symbol) => {
                        return Ok(symbol.value_type.clone());
                    }
                    Err(_) => return Err(format!("TC: Couldnt find symbol `{}`", expr.name)),
                }
            }
            Expression::Literal(lit) => {
                let ty = match lit {
                    Literal::String(parts) => {
                        for part in parts {
                            if let FStringPart::Code(expr) = part {
                                self.typecheck_expr(scope, expr)?;
                            }
                        }

                        Type::String
                    }
                    Literal::Int(_) => Type::Int,
                    Literal::Uint(_) => Type::Uint,
                    Literal::Float(_) => Type::Float,
                    Literal::Boolean(_) => Type::Boolean,
                };

                return Ok(ty);
            }
            Expression::BinaryOp(expr) => {
                let lhs = self.typecheck_expr(scope, &mut expr.lhs)?;
                let rhs = self.typecheck_expr(scope, &mut expr.rhs)?;

                let unified_type = self.figure_out_unified_type(&lhs, &rhs)?;

                let expected_types = match expr.op {
                    BinaryOperation::And | BinaryOperation::Or => vec![Type::Boolean],
                    BinaryOperation::Equal | BinaryOperation::NotEqual => vec![
                        Type::Boolean,
                        Type::String,
                        Type::Uint,
                        Type::Int,
                        Type::Float,
                    ],
                    BinaryOperation::Add => vec![Type::Int, Type::Uint, Type::Float, Type::String],
                    BinaryOperation::GreaterEqual
                    | BinaryOperation::Greater
                    | BinaryOperation::LessEqual
                    | BinaryOperation::Less
                    | BinaryOperation::Subtract
                    | BinaryOperation::Divide
                    | BinaryOperation::Multiply
                    | BinaryOperation::Power => {
                        vec![Type::Int, Type::Uint, Type::Float]
                    }
                };

                if !expected_types.contains(&unified_type) {
                    return Err(format!(
                        "Invalid operand types in binary op expected any of {expected_types:?}"
                    ));
                }

                self.set_type_if_expr_is_var(scope, &expr.lhs, unified_type.clone())?;
                self.set_type_if_expr_is_var(scope, &expr.rhs, unified_type.clone())?;

                let expr_ty = match expr.op {
                    BinaryOperation::GreaterEqual
                    | BinaryOperation::Greater
                    | BinaryOperation::LessEqual
                    | BinaryOperation::Less
                    | BinaryOperation::And
                    | BinaryOperation::Or
                    | BinaryOperation::Equal
                    | BinaryOperation::NotEqual => Type::Boolean,
                    BinaryOperation::Add
                    | BinaryOperation::Subtract
                    | BinaryOperation::Divide
                    | BinaryOperation::Multiply
                    | BinaryOperation::Power => unified_type.clone(),
                };

                return Ok(expr_ty);
            }
            Expression::UnaryOp(expr) => {
                let expected = match expr.op {
                    UnaryOperation::Negate => vec![Type::Boolean],
                    UnaryOperation::Negative => vec![Type::Int, Type::Float],
                    UnaryOperation::Dereference => vec![
                        Type::Reference(Box::new(Type::Any)),
                        Type::Pointer(Box::new(Type::Any)),
                    ],
                    UnaryOperation::Reference => vec![Type::Any],
                    UnaryOperation::Pointer => vec![Type::Any],
                };
                let ty = self.typecheck_expr(scope, &mut expr.operand)?;

                if !expected.contains(&ty) {
                    return Err(format!(
                        "Unary op {:?} wrong type {ty:?} expected one of {expected:?}",
                        expr.op
                    ));
                }

                let out_ty = match expr.op {
                    UnaryOperation::Dereference => match ty {
                        Type::Reference(inner) => *inner,
                        Type::Pointer(inner) => *inner,
                        _ => unreachable!(),
                    },
                    UnaryOperation::Reference => Type::Reference(Box::new(ty)),
                    UnaryOperation::Pointer => Type::Pointer(Box::new(ty)),
                    _ => ty,
                };

                return Ok(out_ty);
            }
            Expression::FunctionCall(func) => {
                let call_ty = self.typecheck_expr(scope, &mut func.func_expr)?;

                match call_ty {
                    Type::Function(FunctionType { args, ret, .. }) => {
                        if func.arguments.len() != args.len() {
                            return Err(format!(
                                "Invalid function args {:?}, {:?} != {:?}",
                                func.func_expr, func.arguments, args
                            ));
                        }

                        for (expected_ty, given) in args.iter().zip(func.arguments.iter_mut()) {
                            let given_ty = self.typecheck_expr(scope, given)?;

                            let unified_arg_ty =
                                self.figure_out_unified_type(expected_ty, &given_ty)?;

                            self.set_type_if_expr_is_var(scope, given, unified_arg_ty)?;
                        }

                        return Ok(*ret);
                    }
                    _ => {
                        return Err(format!(
                            "Tried to call a non function? {:?}",
                            func.func_expr
                        ))
                    }
                }
            }
            Expression::Return(expr) => {
                let ty = self.typecheck_expr(scope, expr)?;
                return Ok(ty);
            }
            Expression::Assignment(expr) => {
                let rhs = self.typecheck_expr(scope, &mut expr.rhs)?;
                let lhs = self.typecheck_expr(scope, &mut expr.lhs)?;

                let unified = self.figure_out_unified_type(&rhs, &lhs)?;
                self.set_type_if_expr_is_var(scope, &expr.lhs, unified.clone())?;
                self.set_type_if_expr_is_var(scope, &expr.rhs, unified.clone())?;

                return Ok(Type::Void);
            }
            Expression::AnonStruct(expr) => {
                let mut fields = Vec::new();

                // TODO this will fail because this isnt guaranteed to create the same field order
                for field in &mut expr.fields {
                    fields.push(StructField {
                        field_name: field.0.clone(),
                        field_type: self.typecheck_expr(scope, field.1)?,
                        is_final: false,
                    });
                }

                let ty = Type::Struct(StructDef { fields });

                return Ok(ty);
            }
            Expression::ArrayLiteral(expr) => {
                let mut last_type = None;
                for el in &mut expr.elements {
                    let el_ty = self.typecheck_expr(scope, el)?;
                    match last_type {
                        None => last_type = Some(el_ty),
                        Some(last) if last != el_ty => {
                            return Err(format!("Incosistent array literal types"))
                        }
                        _ => {}
                    }
                }

                let arr_ty = match last_type {
                    None => Type::Infer,
                    Some(ty) => ty,
                };

                return Ok(Type::Array(Box::new(arr_ty)));
            }
            Expression::ArrayAccess(expr) => {
                let arr_ty = self.typecheck_expr(scope, &mut expr.expr)?;
                let index_ty = self.typecheck_expr(scope, &mut expr.index)?;

                let inner_ty = match arr_ty {
                    Type::Array(inner) => *inner,
                    _ => return Err(format!("Tried to index non array: {arr_ty:?}")),
                };

                // check for negative idx
                match index_ty {
                    Type::Int | Type::Uint | Type::Any => {}
                    Type::Infer => {
                        self.set_type_if_expr_is_var(scope, &expr.index, Type::Uint)?;
                    }
                    ty => {
                        return Err(format!(
                            "Invalid index type, must be uint/int, found {ty:?} from {:?}",
                            expr.index
                        ))
                    }
                }

                return Ok(inner_ty);
            }
            Expression::FieldAccess(expr) => {
                let expr_ty = self.typecheck_expr(scope, &mut expr.expr)?;

                let ty = if let Type::Custom(CustomType { name }) = expr_ty {
                    let (scope, type_name) = self.get_var_scope(*scope, &name);
                    let symbol = self
                        .symbol_table
                        .find_symbol_rec(scope, &type_name, SymbolType::Type)
                        .unwrap();
                    symbol.value_type.clone()
                } else {
                    expr_ty
                };

                if let Type::Struct(StructDef { fields }) = &ty {
                    match fields.iter().filter(|f| f.field_name == expr.field).next() {
                        None => {
                            return Err(format!(
                                "Field `{}` doesnt exist on type `{:?}`",
                                expr.field, ty
                            ))
                        }
                        Some(field) => return Ok(field.field_type.clone()),
                    }
                } else {
                    return Err(format!(
                        "Expression `{:?}` is not a struct, you cant access its fields",
                        expr.field
                    ));
                }
            }
            Expression::NamedStruct(expr) => {
                let (ty_scope, type_name) = self.get_var_scope(*scope, &expr.casted_to);
                let casted_ty = self
                    .symbol_table
                    .find_symbol_rec(ty_scope, &type_name, SymbolType::Type)
                    .expect(&format!("Type `{}` doesnt exist", expr.casted_to))
                    .value_type
                    .clone();

                let named_fields = if let Type::Struct(StructDef { fields }) = &casted_ty {
                    fields
                } else {
                    return Err(format!("Type `{}` does not have fields", expr.casted_to));
                };

                if named_fields.len() == expr.struct_literal.fields.len() {
                    for (field_name, field_expr) in &mut expr.struct_literal.fields {
                        let expected_field = if let Some(expected) =
                            named_fields.iter().find(|f| f.field_name == *field_name)
                        {
                            expected
                        } else {
                            return Err(format!(
                                "Field `{field_name:?}` does not exist on type `{}`",
                                expr.casted_to
                            ));
                        };

                        let field_ty = self.typecheck_expr(scope, field_expr)?;
                        let unified_field_ty =
                            self.figure_out_unified_type(&field_ty, &expected_field.field_type)?;

                        self.set_type_if_expr_is_var(scope, field_expr, unified_field_ty)?;
                    }
                } else {
                    return Err(format!(
                        "Invalid amount of fields for type`{:?}`",
                        expr.casted_to
                    ));
                }

                return Ok(Type::Custom(CustomType {
                    name: expr.casted_to.clone(),
                }));
            }
            Expression::Range(expr) => {
                let start_ty = self.typecheck_expr(scope, &mut expr.start)?;
                let end_ty = self.typecheck_expr(scope, &mut expr.end)?;

                if matches!(start_ty, Type::Int | Type::Uint) && start_ty == end_ty {
                    return Ok(Type::Array(Box::new(start_ty.clone())));
                } else {
                    return Err(format!("Range start and end must be uint/int"));
                }
            }
            Expression::Lambda(expr) => {
                *scope += 1;
                let ret_ty = self.typecheck_codeblock(scope, &mut expr.function_body)?;

                let unified_ret_ty = self.figure_out_unified_type(&ret_ty, &expr.return_type)?;

                let mut arg_types = Vec::new();
                for arg in &expr.argument_list {
                    let arg_ty = arg.arg_type.clone();
                    arg_types.push(arg_ty);
                }

                let new_type = Type::Function(FunctionType {
                    env_args: Vec::new(),
                    args: arg_types,
                    ret: Box::new(unified_ret_ty),
                });

                return Ok(new_type);
            }
            Expression::JS(expr) => {
                self.typecheck_expr(scope, expr)?;

                return Ok(Type::Any);
            }
            Expression::If(expr) => {
                let cond_ty = self.typecheck_expr(scope, &mut expr.cond)?;
                if !matches!(cond_ty, Type::Boolean) {
                    return Err(format!("If condition must evaluate to boolean"));
                }

                *scope += 1;
                let true_ty = self.typecheck_codeblock(scope, &mut expr.true_branch)?;
                if let Some(else_branch) = &mut expr.else_branch {
                    *scope += 1;
                    let else_ty = self.typecheck_codeblock(scope, else_branch)?;

                    if else_ty == true_ty {
                        return Ok(true_ty);
                    }
                }

                return Ok(Type::Void);
            }
            Expression::For(expr) => {
                let iter_ty = self.typecheck_expr(scope, &mut expr.iterator)?;
                match iter_ty {
                    Type::Array(inner) => {
                        // local symbol, no need for get_var_scope
                        let symbol = self.symbol_table.find_symbol_rec_mut(
                            *scope + 1,
                            &expr.binding,
                            SymbolType::Identifier,
                        )?;

                        symbol.value_type = *inner;
                    }
                    _ => {
                        return Err(format!(
                            "For iterator must be an array, found {:?} at {:?}",
                            iter_ty, expr.iterator
                        ))
                    }
                }

                *scope += 1;
                let body_ty = self.typecheck_codeblock(scope, &mut expr.body)?;

                return Ok(Type::Void);
            }
            Expression::Placeholder => return Ok(Type::Any),
            _ => {}
        }

        return Ok(Type::Void);
    }

    fn typecheck_codeblock(
        &mut self,
        scope: &mut usize,
        codeblock: &mut CodeBlock,
    ) -> Result<Type, String> {
        let mut last_type = Type::Void;

        for expr in &mut codeblock.expressions {
            last_type = self.typecheck_expr(scope, expr)?;
        }

        Ok(last_type)
    }

    pub fn typecheck(&mut self, program: &mut Program) -> Result<(), String> {
        let mut scope = 0;
        for module in &mut program.modules {
            self.typecheck_codeblock(&mut scope, &mut module.toplevel_scope)?;

            for func in &mut module.function_defs {
                scope += 1;

                let body_ty = self.typecheck_codeblock(&mut scope, &mut func.function_body)?;

                let unified_body_ty = self.figure_out_unified_type(&body_ty, &func.return_type)?;

                if !matches!(unified_body_ty, Type::Any) && matches!(func.return_type, Type::Infer)
                {
                    func.return_type = unified_body_ty.clone();

                    let old_ret_ty = self
                        .symbol_table
                        .find_symbol_rec(scope - 1, &func.func_name, SymbolType::Identifier)
                        .unwrap()
                        .value_type
                        .clone();

                    if let Type::Function(old_ty) = old_ret_ty {
                        let mut new_ret_type = old_ty;
                        new_ret_type.ret = Box::new(body_ty.clone());

                        let symbol = self.symbol_table.find_symbol_rec_mut(
                            scope - 1,
                            &func.func_name,
                            SymbolType::Identifier,
                        )?;

                        symbol.value_type = Type::Function(new_ret_type);
                    }
                }
            }

            scope += 1;
        }

        Ok(())
    }

    fn enforce_mutability_expr(
        &self,
        mutable_vars: &mut HashSet<String>,
        expr: &Expression,
    ) -> Result<(), String> {
        match expr {
            Expression::Literal(Literal::String(parts)) => {
                for part in parts {
                    if let FStringPart::Code(expr) = part {
                        self.enforce_mutability_expr(mutable_vars, &expr)?
                    }
                }
            }
            Expression::UnaryOp(expr) => match expr.op {
                UnaryOperation::Dereference => {
                    self.enforce_mutability_expr(mutable_vars, &expr.operand)?;
                }
                _ => {}
            },
            Expression::Assignment(expr) => {
                self.enforce_mutability_expr(mutable_vars, &expr.lhs)?;
            }
            Expression::Lambda(expr) => {
                for arg in &expr.argument_list {
                    mutable_vars.insert(arg.arg_name.clone());
                }
                self.enforce_mutability_codeblock(mutable_vars, &expr.function_body)?
            }
            Expression::If(expr) => {
                self.enforce_mutability_codeblock(mutable_vars, &expr.true_branch)?;
                if let Some(else_branch) = &expr.else_branch {
                    self.enforce_mutability_codeblock(mutable_vars, else_branch)?;
                }
            }
            Expression::For(expr) => {
                self.enforce_mutability_codeblock(mutable_vars, &expr.body)?;
            }
            Expression::Variable(var) => {
                if !mutable_vars.contains(&var.name) {
                    return Err(format!("Variable `{}` is not mutable", var.name));
                }
            }
            Expression::ArrayAccess(arr) => {
                self.enforce_mutability_expr(mutable_vars, &arr.expr)?
            }
            Expression::FieldAccess(access) => {
                self.enforce_mutability_expr(mutable_vars, &access.expr)?
            }
            Expression::VariableDecl(expr) => {
                if expr.is_mutable {
                    mutable_vars.insert(expr.var_name.clone());
                }
            }
            _ => {}
        }

        Ok(())
    }

    fn enforce_mutability_codeblock(
        &self,
        mutable_vars: &mut HashSet<String>,
        codeblock: &CodeBlock,
    ) -> Result<(), String> {
        for expr in &codeblock.expressions {
            self.enforce_mutability_expr(mutable_vars, &expr)?;
        }

        Ok(())
    }

    // TODO: probably use symbol table for this?
    pub fn enforce_mutability(&mut self, program: &mut Program) -> Result<(), String> {
        for module in &program.modules {
            for func in &module.function_defs {
                let mut mutable_vars: HashSet<String> = HashSet::new();

                for arg in &func.argument_list {
                    match arg.arg_type {
                        Type::Reference(_) => {}
                        _ => {
                            mutable_vars.insert(arg.arg_name.clone());
                        }
                    };
                }
                self.enforce_mutability_codeblock(&mut mutable_vars, &func.function_body)?;
            }
        }

        Ok(())
    }

    // pub fn typecheck_program(&mut self, program: &mut Program) -> Result<(), String> {
    //     for module in &mut program.modules {
    //         let module_clone = module.clone();
    //         self.typecheck_codeblock(&mut module.toplevel_scope, &module_clone)?;
    //         for func in &mut module.function_defs {
    //             self.typecheck_codeblock(&mut func.function_body, &module_clone)?;
    //         }
    //     }

    //     Ok(())
    // }

    pub fn populate_symbol_table_expr(
        &mut self,
        curr_module_name: &str,
        scope: usize,
        expr: &Expression,
    ) -> Result<(), String> {
        match expr {
            Expression::BuiltinType(expr) => {
                self.populate_symbol_table_expr(curr_module_name, scope, expr)?;
            }
            Expression::Import(import) => {
                let imports = self.get_imports_rec(scope)?;

                let curr_scope = self
                    .symbol_table
                    .get_scope_mut(scope)
                    .ok_or("Scope does not exist")?;

                let flattened = Self::flatten_import(import, String::new());

                for flat in flattened {
                    if imports.contains(&flat) {
                        return Err(format!(
                            "Conflicting use statement: {:?} used multiple times",
                            flat.name
                        ));
                    }
                }

                curr_scope.use_statements.push(import.clone());

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
                self.populate_symbol_table_expr(curr_module_name, scope, &expr.var_value)?;

                self.symbol_table.add_symbol_to_scope(
                    scope,
                    Symbol {
                        original_name: expr.var_name.to_string(),
                        name: expr.var_name.to_string(),
                        symbol_type: SymbolType::Identifier,
                        value_type: expr.var_type.clone(),
                        exported: false,
                        mutable: expr.is_mutable,
                    },
                )?;
            }
            Expression::Literal(lit) => match lit {
                Literal::String(parts) => {
                    for part in parts {
                        if let FStringPart::Code(expr) = part {
                            self.populate_symbol_table_expr(curr_module_name, scope, expr)?
                        }
                    }
                }
                _ => {}
            },
            Expression::BinaryOp(expr) => {
                self.populate_symbol_table_expr(curr_module_name, scope, &expr.lhs)?;
                self.populate_symbol_table_expr(curr_module_name, scope, &expr.rhs)?;
            }
            Expression::UnaryOp(expr) => {
                self.populate_symbol_table_expr(curr_module_name, scope, &expr.operand)?;
            }
            Expression::FunctionCall(expr) => {
                self.populate_symbol_table_expr(curr_module_name, scope, &expr.func_expr)?;

                for arg in &expr.arguments {
                    self.populate_symbol_table_expr(curr_module_name, scope, &arg)?;
                }
            }
            Expression::Return(expr) => {
                self.populate_symbol_table_expr(curr_module_name, scope, &expr)?;
            }
            Expression::Assignment(expr) => {
                self.populate_symbol_table_expr(curr_module_name, scope, &expr.lhs)?;
                self.populate_symbol_table_expr(curr_module_name, scope, &expr.rhs)?;
            }
            Expression::AnonStruct(expr) => {
                for (_, expr) in &expr.fields {
                    self.populate_symbol_table_expr(curr_module_name, scope, &expr)?;
                }
            }
            Expression::ArrayLiteral(expr) => {
                for elem in &expr.elements {
                    self.populate_symbol_table_expr(curr_module_name, scope, &elem)?;
                }
            }
            Expression::ArrayAccess(expr) => {
                self.populate_symbol_table_expr(curr_module_name, scope, &expr.expr)?;
                self.populate_symbol_table_expr(curr_module_name, scope, &expr.index)?;
            }
            Expression::FieldAccess(expr) => {
                self.populate_symbol_table_expr(curr_module_name, scope, &expr.expr)?;
            }
            Expression::NamedStruct(expr) => {
                for (_, expr) in &expr.struct_literal.fields {
                    self.populate_symbol_table_expr(curr_module_name, scope, &expr)?;
                }
            }
            Expression::Lambda(expr) => {
                let lambda_scope = self.symbol_table.new_scope(scope)?;
                for arg in &expr.argument_list {
                    self.symbol_table.add_symbol_to_scope(
                        lambda_scope,
                        Symbol {
                            name: arg.arg_name.clone(),
                            original_name: arg.arg_name.clone(),
                            symbol_type: SymbolType::Identifier,
                            value_type: arg.arg_type.clone(),
                            exported: false,
                            mutable: true,
                        },
                    )?;
                }
                self.populate_symbol_table_codeblock(
                    curr_module_name,
                    lambda_scope,
                    &expr.function_body,
                )?;
            }
            Expression::Range(expr) => {
                self.populate_symbol_table_expr(curr_module_name, scope, &expr.start)?;
                self.populate_symbol_table_expr(curr_module_name, scope, &expr.end)?;
            }
            Expression::If(expr) => {
                let true_scope = self.symbol_table.new_scope(scope)?;
                self.populate_symbol_table_codeblock(
                    curr_module_name,
                    true_scope,
                    &expr.true_branch,
                )?;
                if let Some(else_branch) = &expr.else_branch {
                    let else_scope = self.symbol_table.new_scope(scope)?;
                    self.populate_symbol_table_codeblock(
                        curr_module_name,
                        else_scope,
                        &else_branch,
                    )?;
                }
            }
            Expression::For(expr) => {
                let for_scope = self.symbol_table.new_scope(scope)?;
                self.symbol_table.add_symbol_to_scope(
                    for_scope,
                    Symbol {
                        name: expr.binding.clone(),
                        original_name: expr.binding.clone(),
                        symbol_type: SymbolType::Identifier,
                        value_type: expr.binding_type.clone(),
                        exported: false,
                        mutable: false,
                    },
                )?;
                self.populate_symbol_table_codeblock(curr_module_name, for_scope, &expr.body)?;
            }
            Expression::JS(expr) => {
                self.populate_symbol_table_expr(curr_module_name, scope, expr)?;
            }
            Expression::Placeholder => {}
            Expression::Break => {}
            Expression::Continue => {}
        }
        Ok(())
    }

    pub fn populate_symbol_table_codeblock(
        &mut self,
        curr_module_name: &str,
        scope: usize,
        codeblock: &CodeBlock,
    ) -> Result<(), String> {
        for expr in &codeblock.expressions {
            self.populate_symbol_table_expr(curr_module_name, scope, expr)?;
        }

        Ok(())
    }

    pub fn populate_symbol_table(&mut self, program: &Program) -> Result<(), String> {
        for module in &program.modules {
            let module_scope = self.symbol_table.table.insert(Scope::default());
            let curr_module_name = &module.module_name;

            self.module_to_scope
                .insert(module.module_name.clone(), module_scope);

            self.populate_symbol_table_codeblock(
                curr_module_name,
                module_scope,
                &module.toplevel_scope,
            )?;

            for type_def in &module.type_defs {
                self.symbol_table.add_symbol_to_scope(
                    module_scope,
                    Symbol {
                        name: type_def.name.clone(),
                        original_name: type_def.name.clone(),
                        symbol_type: SymbolType::Type,
                        value_type: type_def.underlying_ty.clone(),
                        exported: type_def.export,
                        mutable: false,
                    },
                )?;
            }

            for func_def in &module.function_defs {
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

                self.symbol_table.add_symbol_to_scope(
                    module_scope,
                    Symbol {
                        name: func_def.func_name.to_string(),
                        original_name: func_def.func_name.to_string(),
                        symbol_type: SymbolType::Identifier,
                        value_type: func_type,
                        exported: func_def.export,
                        mutable: false,
                    },
                )?;

                let func_scope = self.symbol_table.new_scope(module_scope)?;

                for arg in &func_def.argument_list {
                    self.symbol_table.add_symbol_to_scope(
                        func_scope,
                        Symbol {
                            name: arg.arg_name.clone(),
                            original_name: arg.arg_name.clone(),
                            symbol_type: SymbolType::Identifier,
                            value_type: arg.arg_type.clone(),
                            exported: false,
                            mutable: match arg.arg_type {
                                Type::Reference(_) => false,
                                _ => true,
                            },
                        },
                    )?;
                }

                self.populate_symbol_table_codeblock(
                    curr_module_name,
                    func_scope,
                    &func_def.function_body,
                )?;
            }
        }

        Ok(())
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
            Expression::Variable(expr) => {
                let name_parts = expr.name.split("::").collect::<Vec<_>>();
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
                        Ok(_) => return Ok(()),
                        Err(_) => {} // println!(
                                     //     "Failed to find symbol {:?} in local scope, looking elsewhere",
                                     //     expr.name
                                     // )},
                    };

                    for import in &imported_symbols {
                        if let Some(alias) = &import.alias {
                            // if the name is not qualified and it matches the alias exactly
                            if name_parts.len() == 1 && expr.name == *alias {
                                // replace with the qualified name
                                resolved.push(import.name.clone());
                            } // if there is no alias
                        } else {
                            // if the name matches exactly with the ending of an import
                            // eg. name = `foo`, import = `...::foo`
                            let last_part_of_import = import.name.split("::").last().unwrap();
                            if expr.name == last_part_of_import {
                                // replace the name with the full import name
                                resolved.push(import.name.clone());
                            }
                        }
                    }
                } else {
                    match self.module_to_scope.get(&module_name) {
                        Some(scope) => match self.symbol_table.find_symbol_rec(
                            scope.clone(),
                            &name_parts.last().unwrap(),
                            SymbolType::Identifier,
                        ) {
                            Ok(_) => return Ok(()),
                            Err(_) => {
                                println!("Couldnt find symbol {:?} looking elsewhere", expr.name)
                            }
                        },
                        None => {}
                    }

                    for import in &imported_symbols {
                        if let Some(alias) = &import.alias {
                            // if the qualified name starts with the alias `alias::foo`
                            if expr.name.starts_with(alias) {
                                // replace the name with `import.name::foo`
                                let new_name =
                                    expr.name.strip_prefix(&format!("{alias}::")).unwrap();
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
                                let ending_of_iden = expr
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
                    1 => expr.name = resolved[0].clone(),
                    0 => return Err(format!("Identifier not found: {:?}", expr.name)),
                    _ => {
                        return Err(format!(
                            "Ambiguous name: {:?}, found these imports: {resolved:?}",
                            expr.name
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
                self.resolve_names_expr(curr_module_name, scope, expr)?;
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
            Expression::JS(expr) => {
                self.resolve_names_expr(curr_module_name, scope, expr)?;
            }
            Expression::Placeholder => {}
            Expression::Break => {}
            Expression::Continue => {}
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
                        .module_to_scope
                        .get(&module_name)
                        .expect(&format!("Couldnt resolve module {module_name:?}"));

                    scope.clone()
                };

                match self.symbol_table.find_symbol_rec(
                    scope_idx,
                    &name_parts.last().unwrap(),
                    SymbolType::Type,
                ) {
                    Ok(_) => return Ok(()),
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

    pub fn resolve_names(&mut self, program: &mut Program) -> Result<(), String> {
        let mut scope = 0;
        for module in &mut program.modules {
            let curr_module_name = module.module_name.as_str();
            for type_def in &mut module.type_defs {
                self.resolve_type_name(curr_module_name, &scope, &mut type_def.underlying_ty)?;
            }

            self.resolve_names_codeblock(curr_module_name, &mut scope, &mut module.toplevel_scope)?;

            for func_def in &mut module.function_defs {
                // should use module scope since you cant define types in other scopes
                // but it doesnt really matter since symbols are searched for recursively
                let module_scope = self
                    .module_to_scope
                    .get(&module.module_name)
                    .unwrap()
                    .clone();
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

    fn map_to_unique_name(
        &mut self,
        shadowed_vars: &mut HashMap<String, String>,
        name: &mut String,
    ) {
        use std::collections::hash_map::Entry;
        match shadowed_vars.entry(name.to_string()) {
            Entry::Occupied(mut entry) => {
                let new_name = format!("_{}", self.unique_name_suffix);
                entry.insert(new_name.clone());
                self.symbol_table
                    .mapped_names
                    .insert(name.clone(), new_name);
            }
            Entry::Vacant(entry) => {
                let new_name = format!("_{}", self.unique_name_suffix);
                entry.insert(new_name.clone());
                self.symbol_table
                    .mapped_names
                    .insert(name.clone(), new_name);
            }
        }
        self.unique_name_suffix += 1;

        *name = shadowed_vars.get(name).unwrap().clone();
    }

    fn enable_shadowing_expr(
        &mut self,
        shadowed_vars: &mut HashMap<String, String>,
        expr: &mut Expression,
    ) -> Result<(), String> {
        match expr {
            Expression::BuiltinType(expr) => {
                self.enable_shadowing_expr(shadowed_vars, expr)?;
            }
            Expression::Import(import) => {}
            Expression::Variable(expr) => {
                expr.name = shadowed_vars.get(&expr.name).unwrap().clone();
            }
            Expression::VariableDecl(expr) => {
                self.enable_shadowing_expr(shadowed_vars, &mut expr.var_value)?;
                self.map_to_unique_name(shadowed_vars, &mut expr.var_name);
            }
            Expression::Literal(literal) => match literal {
                Literal::String(parts) => {
                    for part in parts {
                        if let FStringPart::Code(expr) = part {
                            self.enable_shadowing_expr(shadowed_vars, expr)?;
                        }
                    }
                }
                _ => {}
            },
            Expression::BinaryOp(expr) => {
                self.enable_shadowing_expr(shadowed_vars, &mut expr.lhs)?;
                self.enable_shadowing_expr(shadowed_vars, &mut expr.rhs)?;
            }
            Expression::UnaryOp(expr) => {
                self.enable_shadowing_expr(shadowed_vars, &mut expr.operand)?;
            }
            Expression::FunctionCall(expr) => {
                self.enable_shadowing_expr(shadowed_vars, &mut expr.func_expr)?;

                for arg in &mut expr.arguments {
                    self.enable_shadowing_expr(shadowed_vars, arg)?;
                }
            }
            Expression::Return(expr) => {
                self.enable_shadowing_expr(shadowed_vars, expr)?;
            }
            Expression::Assignment(expr) => {
                self.enable_shadowing_expr(shadowed_vars, &mut expr.lhs)?;
                self.enable_shadowing_expr(shadowed_vars, &mut expr.rhs)?;
            }
            Expression::AnonStruct(expr) => {
                for (_, expr) in &mut expr.fields {
                    self.enable_shadowing_expr(shadowed_vars, expr)?;
                }
            }
            Expression::ArrayLiteral(expr) => {
                for elem in &mut expr.elements {
                    self.enable_shadowing_expr(shadowed_vars, elem)?;
                }
            }
            Expression::ArrayAccess(expr) => {
                self.enable_shadowing_expr(shadowed_vars, &mut expr.expr)?;
                self.enable_shadowing_expr(shadowed_vars, &mut expr.index)?;
            }
            Expression::FieldAccess(expr) => {
                self.enable_shadowing_expr(shadowed_vars, &mut expr.expr)?;
            }
            Expression::NamedStruct(expr) => {
                for (_, expr) in &mut expr.struct_literal.fields {
                    self.enable_shadowing_expr(shadowed_vars, expr)?;
                }
            }
            Expression::Lambda(expr) => {
                for arg in &mut expr.argument_list {
                    self.map_to_unique_name(shadowed_vars, &mut arg.arg_name);
                }
                self.enable_shadowing_codeblock(shadowed_vars, &mut expr.function_body)?;
            }
            Expression::Range(expr) => {
                self.enable_shadowing_expr(shadowed_vars, &mut expr.start)?;
                self.enable_shadowing_expr(shadowed_vars, &mut expr.end)?;
            }
            Expression::If(expr) => {
                self.enable_shadowing_expr(shadowed_vars, &mut expr.cond)?;
                self.enable_shadowing_codeblock(shadowed_vars, &mut expr.true_branch)?;
                if let Some(else_branch) = &mut expr.else_branch {
                    self.enable_shadowing_codeblock(shadowed_vars, else_branch)?;
                }
            }
            Expression::For(expr) => {
                self.enable_shadowing_expr(shadowed_vars, &mut expr.iterator)?;
                self.enable_shadowing_codeblock(shadowed_vars, &mut expr.body)?;
                self.map_to_unique_name(shadowed_vars, &mut expr.binding);
            }
            Expression::JS(expr) => {
                self.enable_shadowing_expr(shadowed_vars, expr)?;
            }
            Expression::Placeholder => {}
            Expression::Break => {}
            Expression::Continue => {}
        }

        Ok(())
    }

    fn enable_shadowing_codeblock(
        &mut self,
        shadowed_vars: &mut HashMap<String, String>,
        codeblock: &mut CodeBlock,
    ) -> Result<(), String> {
        let mut shadowed_vars = shadowed_vars.clone();
        for expr in &mut codeblock.expressions {
            self.enable_shadowing_expr(&mut shadowed_vars, expr)?;
        }

        Ok(())
    }

    pub fn enable_shadowing(&mut self, program: &mut Program) -> Result<(), String> {
        let mut shadowed_vars: HashMap<String, String> = HashMap::new();
        for module in &mut program.modules {
            self.enable_shadowing_codeblock(&mut shadowed_vars, &mut module.toplevel_scope)?;

            for func_def in &mut module.function_defs {
                self.map_to_unique_name(&mut shadowed_vars, &mut func_def.func_name);
                for arg in &mut func_def.argument_list {
                    self.map_to_unique_name(&mut shadowed_vars, &mut arg.arg_name);
                }

                self.enable_shadowing_codeblock(&mut shadowed_vars, &mut func_def.function_body)?;
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

    pub fn perform_analysis(
        &mut self,
        program: &mut Program,
        perf: bool,
    ) -> Result<SymbolTable, String> {
        let start = Instant::now();
        // self.enable_shadowing(program)?;
        self.populate_symbol_table(program)?;
        self.resolve_names(program)?;
        self.enforce_mutability(program)?;
        self.typecheck(program)?;
        // self.eval_builtins(program)?;

        if perf {
            println!(
                "Semantics: {}us",
                Instant::now().duration_since(start).as_micros()
            );
        }

        Ok(self.symbol_table.clone())
    }
}
