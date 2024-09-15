use std::{
    any::Any,
    collections::{HashMap, HashSet},
    f64::consts::PI,
    fmt::Debug,
};

use crate::{
    ast::{CodeBlock, Expression, FunctionCall, Variable, VariableDecl},
    parser::Program,
    Arena, BinaryOperation, CustomType, FunctionType, Lambda, Literal, Module, NamedStruct,
    StructDef, StructField, Type,
};

#[derive(Debug, Clone)]
pub struct Symbol {
    pub original_name: String,
    pub symbol_type: SymbolType,
    pub value_type: Type,
    pub exported: bool,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy)]
pub enum SymbolType {
    Identifier,
    Type,
}

#[derive(Debug, Clone, Default)]
pub struct Scope {
    pub parent_scope: Option<usize>,
    pub children_scopes: Vec<usize>,
    pub symbols: Vec<Symbol>,
    pub used_modules: Vec<String>,
}

impl Scope {
    pub fn with_parent(parent: usize) -> Self {
        Self {
            parent_scope: Some(parent),
            children_scopes: Vec::new(),
            symbols: Vec::new(),
            used_modules: Vec::new(),
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct SemanticAnalyzer {
    pub symbol_table: Arena<Scope>,
    pub module_to_scope: HashMap<String, usize>,
}

impl SemanticAnalyzer {
    fn figure_out_unified_type(&mut self, lhs: &Type, rhs: &Type) -> Result<Type, String> {
        match (lhs, rhs) {
            (Type::Infer, Type::Infer) => return Err(format!("Cant infer type")),
            (lhs, rhs) if lhs == rhs => return Ok(lhs.clone()),
            (Type::Infer, rhs) => return Ok(rhs.clone()),
            (lhs, Type::Infer) => return Ok(lhs.clone()),
            (Type::Array(lhs_inner), Type::Array(rhs_inner)) => {
                return Ok(Type::Array(Box::new(
                    self.figure_out_unified_type(lhs_inner, rhs_inner)?,
                )));
            }
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

                return Ok(Type::Function(unified_type));
            }
            _ => return Err(format!("Lhs != rhs: {lhs:?} != {rhs:?}")),
        }
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
            self.set_symbol_type(*scope, &var.name, SymbolType::Identifier, ty.clone())?;
        }

        return Ok(());
    }

    fn typecheck_expr(&mut self, scope: &mut usize, expr: &mut Expression) -> Result<Type, String> {
        match expr {
            Expression::VariableDecl(expr) => {
                let rhs = self.typecheck_expr(scope, &mut expr.var_value)?;
                let unified = self.figure_out_unified_type(&rhs, &expr.var_type)?;
                expr.var_type = unified.clone();
                self.set_symbol_type(
                    *scope,
                    &expr.var_name,
                    SymbolType::Identifier,
                    unified.clone(),
                )?;
                return Ok(unified);
            }
            Expression::Variable(expr) => {
                let name_parts = expr.name.split("::").collect::<Vec<_>>();
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

                match self.find_symbol_recursive(
                    scope_idx,
                    &name_parts.last().unwrap(),
                    SymbolType::Identifier,
                ) {
                    Some(symbol) => {
                        return Ok(symbol.value_type);
                    }
                    None => return Err(format!("Couldnt find symbol `{}`", expr.name)),
                }
            }
            Expression::Literal(lit) => {
                let ty = match lit {
                    Literal::String(_) => Type::String,
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
                let ty = self.typecheck_expr(scope, &mut expr.operand)?;
                return Ok(ty);
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
                            "Tried to call a non function? {:?}", func.func_expr
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
                    let symbol = self
                        .find_symbol_recursive(*scope, &name, SymbolType::Type)
                        .unwrap();
                    symbol.value_type
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
                let casted_ty = self
                    .find_symbol_recursive(*scope, &expr.casted_to, SymbolType::Type)
                    .expect(&format!("Type `{}` doesnt exist", expr.casted_to))
                    .value_type;

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
                for expr in expr {
                    self.typecheck_expr(scope, expr)?;
                }

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
                        self.set_symbol_type(
                            *scope + 1,
                            &expr.binding,
                            SymbolType::Identifier,
                            *inner,
                        )?;
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
            Expression::Break => {}
            Expression::Continue => {}
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
            println!("Typechecking {:?}", module.module_name);
            self.typecheck_codeblock(&mut scope, &mut module.toplevel_scope)?;

            for func in &mut module.function_defs {
                scope += 1;

                let body_ty = self.typecheck_codeblock(&mut scope, &mut func.function_body)?;

                let unified_body_ty = self.figure_out_unified_type(&body_ty, &func.return_type)?;

                if !matches!(unified_body_ty, Type::Any) {
                    func.return_type = unified_body_ty.clone();

                    let old_ret_ty = self
                        .find_symbol_recursive(scope - 1, &func.func_name, SymbolType::Identifier)
                        .unwrap()
                        .value_type;

                    if let Type::Function(old_ty) = old_ret_ty {
                        let mut new_ret_type = old_ty;
                        new_ret_type.ret = Box::new(body_ty.clone());

                        self.set_symbol_type(
                            scope - 1,
                            &func.func_name,
                            SymbolType::Identifier,
                            Type::Function(new_ret_type),
                        )?;
                    }
                }
            }

            scope += 1;
        }

        Ok(())
    }

    fn resolve_type_name(&mut self, scope: &usize, kind: &mut Type) -> Result<(), String> {
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

                match self.find_symbol_recursive(
                    scope_idx,
                    &name_parts.last().unwrap(),
                    SymbolType::Type,
                ) {
                    Some(_) => return Ok(()),
                    None => return Err(format!("Type not found `{}`", name)),
                };
            }
            Type::Reference(inner) | Type::Structural(inner) | Type::Array(inner) => {
                self.resolve_type_name(scope, inner)?;
            }
            Type::Function(func) => {
                let FunctionType {
                    env_args,
                    args,
                    ret,
                } = func;

                for env_arg in env_args {
                    self.resolve_type_name(scope, env_arg)?;
                }
                for arg in args {
                    self.resolve_type_name(scope, arg)?;
                }

                self.resolve_type_name(scope, ret)?;
            }
            Type::Struct(struct_type) => {
                let StructDef { fields } = struct_type;

                for field in fields {
                    self.resolve_type_name(scope, &mut field.field_type)?;
                }
            }
        }

        Ok(())
    }

    fn enforce_mutability_expr(
        &self,
        mutable_vars: &mut HashSet<String>,
        expr: &Expression,
    ) -> Result<(), String> {
        match expr {
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

    pub fn enforce_mutability(&mut self, program: &mut Program) -> Result<(), String> {
        for module in &program.modules {
            for func in &module.function_defs {
                let mut mutable_vars: HashSet<String> = HashSet::new();

                for arg in &func.argument_list {
                    mutable_vars.insert(arg.arg_name.clone());
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
        scope: usize,
        expr: &Expression,
    ) -> Result<(), String> {
        match expr {
            Expression::Variable(_) => {}
            Expression::VariableDecl(expr) => {
                self.populate_symbol_table_expr(scope, &expr.var_value)?;

                self.add_symbol_to_scope(
                    scope,
                    Symbol {
                        original_name: expr.var_name.to_string(),
                        symbol_type: SymbolType::Identifier,
                        value_type: expr.var_type.clone(),
                        exported: false,
                    },
                )?;
            }
            Expression::Literal(_) => {}
            Expression::BinaryOp(expr) => {
                self.populate_symbol_table_expr(scope, &expr.lhs)?;
                self.populate_symbol_table_expr(scope, &expr.rhs)?;
            }
            Expression::UnaryOp(expr) => {
                self.populate_symbol_table_expr(scope, &expr.operand)?;
            }
            Expression::FunctionCall(expr) => {
                self.populate_symbol_table_expr(scope, &expr.func_expr)?;

                for arg in &expr.arguments {
                    self.populate_symbol_table_expr(scope, &arg)?;
                }
            }
            Expression::Return(expr) => {
                self.populate_symbol_table_expr(scope, &expr)?;
            }
            Expression::Assignment(expr) => {
                self.populate_symbol_table_expr(scope, &expr.lhs)?;
                self.populate_symbol_table_expr(scope, &expr.rhs)?;
            }
            Expression::AnonStruct(expr) => {
                for (_, expr) in &expr.fields {
                    self.populate_symbol_table_expr(scope, &expr)?;
                }
            }
            Expression::ArrayLiteral(expr) => {
                for elem in &expr.elements {
                    self.populate_symbol_table_expr(scope, &elem)?;
                }
            }
            Expression::ArrayAccess(expr) => {
                self.populate_symbol_table_expr(scope, &expr.expr)?;
                self.populate_symbol_table_expr(scope, &expr.index)?;
            }
            Expression::FieldAccess(expr) => {
                self.populate_symbol_table_expr(scope, &expr.expr)?;
            }
            Expression::NamedStruct(expr) => {
                for (_, expr) in &expr.struct_literal.fields {
                    self.populate_symbol_table_expr(scope, &expr)?;
                }
            }
            Expression::Lambda(expr) => {
                let lambda_scope = self.new_scope(scope)?;
                for arg in &expr.argument_list {
                    self.add_symbol_to_scope(
                        lambda_scope,
                        Symbol {
                            original_name: arg.arg_name.clone(),
                            symbol_type: SymbolType::Identifier,
                            value_type: arg.arg_type.clone(),
                            exported: false,
                        },
                    )?;
                }
                self.populate_symbol_table_codeblock(lambda_scope, &expr.function_body)?;
            }
            Expression::Range(expr) => {
                self.populate_symbol_table_expr(scope, &expr.start)?;
                self.populate_symbol_table_expr(scope, &expr.end)?;
            }
            Expression::If(expr) => {
                self.populate_symbol_table_expr(scope, &expr.cond)?;
                let true_scope = self.new_scope(scope)?;
                self.populate_symbol_table_codeblock(true_scope, &expr.true_branch)?;
                if let Some(else_branch) = &expr.else_branch {
                    let else_scope = self.new_scope(scope)?;
                    self.populate_symbol_table_codeblock(else_scope, &else_branch)?;
                }
            }
            Expression::For(expr) => {
                self.populate_symbol_table_expr(scope, &expr.iterator)?;
                let for_scope = self.new_scope(scope)?;
                self.add_symbol_to_scope(
                    for_scope,
                    Symbol {
                        original_name: expr.binding.clone(),
                        symbol_type: SymbolType::Identifier,
                        value_type: expr.binding_type.clone(),
                        exported: false,
                    },
                )?;
                self.populate_symbol_table_codeblock(for_scope, &expr.body)?;
            }
            Expression::JS(expr) => {
                for expr in expr {
                    self.populate_symbol_table_expr(scope, expr)?;
                }
            }
            Expression::Placeholder => {}
            Expression::Break => {}
            Expression::Continue => {}
        }
        Ok(())
    }

    pub fn populate_symbol_table_codeblock(
        &mut self,
        scope: usize,
        codeblock: &CodeBlock,
    ) -> Result<(), String> {
        for expr in &codeblock.expressions {
            self.populate_symbol_table_expr(scope, expr)?;
        }

        Ok(())
    }

    pub fn populate_symbol_table(&mut self, program: &Program) -> Result<(), String> {
        for module in &program.modules {
            let module_scope = self.symbol_table.insert(Scope::default());

            self.module_to_scope
                .insert(module.module_name.clone(), module_scope);

            self.populate_symbol_table_codeblock(module_scope, &module.toplevel_scope)?;

            for type_def in &module.type_defs {
                self.add_symbol_to_scope(
                    module_scope,
                    Symbol {
                        original_name: type_def.name.clone(),
                        symbol_type: SymbolType::Type,
                        value_type: type_def.value.clone(),
                        exported: type_def.export,
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

                self.add_symbol_to_scope(
                    module_scope,
                    Symbol {
                        original_name: func_def.func_name.to_string(),
                        symbol_type: SymbolType::Identifier,
                        value_type: func_type,
                        exported: func_def.export,
                    },
                )?;

                let func_scope = self.new_scope(module_scope)?;

                for arg in &func_def.argument_list {
                    self.add_symbol_to_scope(
                        func_scope,
                        Symbol {
                            original_name: arg.arg_name.clone(),
                            symbol_type: SymbolType::Identifier,
                            value_type: arg.arg_type.clone(),
                            exported: false,
                        },
                    )?;
                }

                self.populate_symbol_table_codeblock(func_scope, &func_def.function_body)?;
            }
        }

        Ok(())
    }

    fn add_symbol_to_scope(&mut self, scope: usize, symbol: Symbol) -> Result<(), String> {
        let curr_scope = self
            .symbol_table
            .get_mut(scope)
            .ok_or("Scope does not exist")?;

        let exists = SemanticAnalyzer::scope_get_symbol(
            &curr_scope,
            &symbol.original_name,
            symbol.symbol_type,
        )
        .is_some();

        if exists {
            return Err(format!("Duplicate symbol `{}`", symbol.original_name));
        } else {
            curr_scope.symbols.push(symbol);
            Ok(())
        }
    }

    fn set_symbol_type(
        &mut self,
        scope: usize,
        symbol_name: &str,
        symbol_type: SymbolType,
        ty: Type,
    ) -> Result<(), String> {
        let mut scope_idx = Some(scope);
        while let Some(curr_scope_idx) = scope_idx {
            let curr_scope = self.symbol_table.get_mut(curr_scope_idx).unwrap();

            match curr_scope
                .symbols
                .iter_mut()
                .filter(|s| s.original_name == symbol_name && s.symbol_type == symbol_type)
                .next()
            {
                Some(symbol) => {
                    symbol.value_type = ty;
                    return Ok(());
                }
                None => scope_idx = curr_scope.parent_scope,
            }
        }

        Err(format!("Symbol `{symbol_name}` doesnt exist in scope"))
    }

    fn find_symbol_recursive(
        &self,
        scope: usize,
        symbol_name: &str,
        symbol_type: SymbolType,
    ) -> Option<Symbol> {
        let mut scope_idx = Some(scope);
        while let Some(curr_scope_idx) = scope_idx {
            let curr_scope = self.symbol_table.get(curr_scope_idx).unwrap();

            match SemanticAnalyzer::scope_get_symbol(&curr_scope, symbol_name, symbol_type) {
                Some(symbol) => return Some(symbol),
                None => scope_idx = curr_scope.parent_scope,
            }
        }

        return None;
    }

    fn resolve_names_expr(
        &mut self,
        scope: &mut usize,
        expr: &mut Expression,
    ) -> Result<(), String> {
        match expr {
            Expression::Variable(expr) => {
                let name_parts = expr.name.split("::").collect::<Vec<_>>();
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

                match self.find_symbol_recursive(
                    scope_idx,
                    &name_parts.last().unwrap(),
                    SymbolType::Identifier,
                ) {
                    Some(_) => return Ok(()),
                    None => return Err(format!("Identifier not found `{}`", expr.name)),
                };
            }
            Expression::VariableDecl(expr) => {
                self.resolve_names_expr(scope, &mut expr.var_value)?;
                self.resolve_type_name(scope, &mut expr.var_type)?;
            }
            Expression::Literal(_) => {}
            Expression::BinaryOp(expr) => {
                self.resolve_names_expr(scope, &mut expr.lhs)?;
                self.resolve_names_expr(scope, &mut expr.rhs)?;
            }
            Expression::UnaryOp(expr) => {
                self.resolve_names_expr(scope, &mut expr.operand)?;
            }
            Expression::FunctionCall(expr) => {
                self.resolve_names_expr(scope, &mut expr.func_expr)?;

                for arg in &mut expr.arguments {
                    self.resolve_names_expr(scope, arg)?;
                }
            }
            Expression::Return(expr) => {
                self.resolve_names_expr(scope, expr)?;
            }
            Expression::Assignment(expr) => {
                self.resolve_names_expr(scope, &mut expr.lhs)?;
                self.resolve_names_expr(scope, &mut expr.rhs)?;
            }
            Expression::AnonStruct(expr) => {
                for (_, expr) in &mut expr.fields {
                    self.resolve_names_expr(scope, expr)?;
                }
            }
            Expression::ArrayLiteral(expr) => {
                for elem in &mut expr.elements {
                    self.resolve_names_expr(scope, elem)?;
                }
            }
            Expression::ArrayAccess(expr) => {
                self.resolve_names_expr(scope, &mut expr.expr)?;
                self.resolve_names_expr(scope, &mut expr.index)?;
            }
            Expression::FieldAccess(expr) => {
                self.resolve_names_expr(scope, &mut expr.expr)?;
            }
            Expression::NamedStruct(expr) => {
                for (_, expr) in &mut expr.struct_literal.fields {
                    self.resolve_names_expr(scope, expr)?;
                }
            }
            Expression::Lambda(expr) => {
                self.resolve_type_name(scope, &mut expr.return_type)?;
                for arg in &mut expr.argument_list {
                    self.resolve_type_name(scope, &mut arg.arg_type)?;
                }

                *scope += 1;
                self.resolve_names_codeblock(scope, &mut expr.function_body)?;
            }
            Expression::Range(expr) => {
                self.resolve_names_expr(scope, &mut expr.start)?;
                self.resolve_names_expr(scope, &mut expr.end)?;
            }
            Expression::If(expr) => {
                self.resolve_names_expr(scope, &mut expr.cond)?;
                *scope += 1;
                self.resolve_names_codeblock(scope, &mut expr.true_branch)?;
                if let Some(else_branch) = &mut expr.else_branch {
                    *scope += 1;
                    self.resolve_names_codeblock(scope, else_branch)?;
                }
            }
            Expression::For(expr) => {
                self.resolve_type_name(scope, &mut expr.binding_type)?;
                self.resolve_names_expr(scope, &mut expr.iterator)?;
                *scope += 1;
                self.resolve_names_codeblock(scope, &mut expr.body)?;
            }
            Expression::JS(expr) => {
                for expr in expr {
                    self.resolve_names_expr(scope, expr)?;
                }
            }
            Expression::Placeholder => {}
            Expression::Break => {}
            Expression::Continue => {}
        }

        Ok(())
    }

    fn resolve_names_codeblock(
        &mut self,
        scope: &mut usize,
        codeblock: &mut CodeBlock,
    ) -> Result<(), String> {
        for expr in &mut codeblock.expressions {
            self.resolve_names_expr(scope, expr)?;
        }

        Ok(())
    }

    pub fn resolve_names(&mut self, program: &mut Program) -> Result<(), String> {
        let mut scope = 0;
        for module in &mut program.modules {
            for type_def in &mut module.type_defs {
                self.resolve_type_name(&scope, &mut type_def.value)?;
            }

            self.resolve_names_codeblock(&mut scope, &mut module.toplevel_scope)?;

            for func_def in &mut module.function_defs {
                // should use module scope since you cant define types in other scopes
                // but it doesnt really matter since symbols are searched for recursively
                let module_scope = self
                    .module_to_scope
                    .get(&module.module_name)
                    .unwrap()
                    .clone();
                self.resolve_type_name(&module_scope, &mut func_def.return_type)?;
                for arg in &mut func_def.argument_list {
                    self.resolve_type_name(&module_scope, &mut arg.arg_type)?;
                }

                scope += 1;

                self.resolve_names_codeblock(&mut scope, &mut func_def.function_body)?;
            }

            scope += 1;
        }

        Ok(())
    }

    fn map_to_unique_name(shadowed_vars: &mut HashMap<String, String>, name: &mut String) {
        use std::collections::hash_map::Entry;
        match shadowed_vars.entry(name.to_string()) {
            Entry::Occupied(mut entry) => {
                let old_name = entry.get().clone();
                entry.insert(format!("{old_name}_unique"));
            }
            Entry::Vacant(entry) => {
                entry.insert(format!("{}_", name.to_string()));
            }
        }

        *name = shadowed_vars.get(name).unwrap().clone();
    }

    fn enable_shadowing_expr(
        &mut self,
        shadowed_vars: &mut HashMap<String, String>,
        expr: &mut Expression,
    ) -> Result<(), String> {
        match expr {
            Expression::Variable(expr) => {
                println!("{}", expr.name);
                println!("{shadowed_vars:?}");
                expr.name = shadowed_vars.get(&expr.name).unwrap().clone();
            }
            Expression::VariableDecl(expr) => {
                self.enable_shadowing_expr(shadowed_vars, &mut expr.var_value)?;
                SemanticAnalyzer::map_to_unique_name(shadowed_vars, &mut expr.var_name);
            }
            Expression::Literal(_) => {}
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
                    SemanticAnalyzer::map_to_unique_name(shadowed_vars, &mut arg.arg_name);
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
                SemanticAnalyzer::map_to_unique_name(shadowed_vars, &mut expr.binding);
            }
            Expression::JS(expr) => {
                for expr in expr {
                    self.enable_shadowing_expr(shadowed_vars, expr)?;
                }
            }
            Expression::Placeholder => todo!(),
            Expression::Break => todo!(),
            Expression::Continue => todo!(),
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
        for module in &mut program.modules {
            let mut shadowed_vars: HashMap<String, String> = HashMap::new();

            self.enable_shadowing_codeblock(&mut shadowed_vars, &mut module.toplevel_scope)?;

            for func_def in &mut module.function_defs {
                SemanticAnalyzer::map_to_unique_name(&mut shadowed_vars, &mut func_def.func_name);
                for arg in &mut func_def.argument_list {
                    SemanticAnalyzer::map_to_unique_name(&mut shadowed_vars, &mut arg.arg_name);
                }

                self.enable_shadowing_codeblock(&mut shadowed_vars, &mut func_def.function_body)?;
            }
        }

        Ok(())
    }

    fn add_child_scope(&mut self, parent: usize, child: usize) -> Result<(), String> {
        let parent = self
            .symbol_table
            .get_mut(parent)
            .ok_or("Parent scope not found".to_string())?;

        parent.children_scopes.push(child);

        Ok(())
    }

    fn new_scope(&mut self, parent: usize) -> Result<usize, String> {
        let child = self.symbol_table.insert(Scope::with_parent(parent));
        self.add_child_scope(parent, child)?;

        Ok(child)
    }

    fn scope_get_symbol(scope: &Scope, name: &str, symbol_type: SymbolType) -> Option<Symbol> {
        scope
            .symbols
            .iter()
            .filter(|s| s.original_name == name && s.symbol_type == symbol_type)
            .next()
            .cloned()
    }

    pub fn perform_analysis(&mut self, program: &mut Program) -> Result<Arena<Scope>, String> {
        // self.enable_shadowing(program)?;
        self.populate_symbol_table(program)?;
        self.resolve_names(program)?;
        self.enforce_mutability(program)?;
        self.typecheck(program)?;

        Ok(self.symbol_table.clone())
    }
}
