use crate::{
    ast::*,
    lexer::{FStringPart, Literal},
    parser::Program,
};

use crate::symbol_table::*;

#[derive(Debug)]
pub struct Typechecker<'a> {
    pub symbol_table: &'a mut SymbolTable,
}

impl<'a> Typechecker<'a> {
    pub fn new(symbol_table: &'a mut SymbolTable) -> Self {
        Self { symbol_table }
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

    // This should be its own pass tbh
    fn replace_builtin_type(&mut self, scope: &mut usize, expr: &mut Expression) {
        if let Expression::BuiltinType(expr_copy) = &mut expr.clone() {
            if let Ok(inner_ty) = self.typecheck_expr(scope, expr_copy) {
                *expr = Expression::Literal(Literal::String(vec![FStringPart::String(format!(
                    "{inner_ty}"
                ))]));
            };
        }
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
                .symbol_table
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

        if let Expression::Variable(var) = &expr {
            let (scope, var_name) = self.get_var_scope(*scope, &var.name);
            let symbol = self
                .symbol_table
                .find_symbol_rec_mut(scope, &var_name, SymbolType::Identifier)
                .unwrap()
                .1;

            symbol.value_type = ty;
        }

        return Ok(());
    }

    fn typecheck_expr(&mut self, scope: &mut usize, expr: &mut Expression) -> Result<Type, String> {
        match expr {
            expr @ Expression::BuiltinType(_) => {
                self.replace_builtin_type(scope, expr);
                return Ok(Type::String);
            }
            //     let inner_ty = self.typecheck_expr(scope, inner.as_mut())?;

            //     *expr = ExprKind::Literal(Literal::String(vec![FStringPart::String(format!(
            //         "{inner_ty:?}"
            //     ))]));

            //     return Ok(Type::String);
            // }
            Expression::VariableDecl(expr) => {
                let rhs = self.typecheck_expr(scope, &mut expr.var_value)?;
                let unified = self.figure_out_unified_type(&rhs, &expr.var_type)?;
                expr.var_type = unified.clone();
                //no need to use get_var_scope since this is a declaration so its in the local scope
                let symbol = self
                    .symbol_table
                    .find_symbol_rec_mut(*scope, &expr.var_name, SymbolType::Identifier)?
                    .1;
                symbol.value_type = unified.clone();
                return Ok(unified);
            }
            Expression::Variable(expr) => {
                let (scope, var_name) = self.get_var_scope(*scope, &expr.name);

                match self
                    .symbol_table
                    .find_symbol_rec(scope, &var_name, SymbolType::Identifier)
                {
                    Ok((_, symbol)) => {
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
                if let Some(expr) = expr {
                    let ty = self.typecheck_expr(scope, expr)?;
                    return Ok(ty);
                } else {
                    return Ok(Type::Void);
                }
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

                let ty = if let Type::Custom(CustomType { name, .. }) = expr_ty {
                    let (scope, type_name) = self.get_var_scope(*scope, &name);
                    let (_, symbol) = self
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
                let (casted_symbol_idx, casted_ty_sym) = self
                    .symbol_table
                    .find_symbol_rec(ty_scope, &type_name, SymbolType::Type)
                    .expect(&format!("Type `{}` doesnt exist", expr.casted_to));

                let casted_ty = casted_ty_sym.value_type.clone();

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
            Expression::BuiltinTarget(expr) => {
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
                        let binding = self
                            .symbol_table
                            .find_symbol_rec_mut(*scope + 1, &expr.binding, SymbolType::Identifier)?
                            .1;

                        expr.binding_type = *inner.clone();
                        binding.value_type = *inner;
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

                    // update function's return type in symbol table
                    let old_ret_ty = self
                        .symbol_table
                        .find_symbol_rec(scope - 1, &func.func_name, SymbolType::Identifier)
                        .unwrap()
                        .1
                        .value_type
                        .clone();

                    if let Type::Function(old_ty) = old_ret_ty {
                        let mut new_ret_type = old_ty;
                        new_ret_type.ret = Box::new(body_ty.clone());

                        let symbol = self
                            .symbol_table
                            .find_symbol_rec_mut(
                                scope - 1,
                                &func.func_name,
                                SymbolType::Identifier,
                            )?
                            .1;

                        symbol.value_type = Type::Function(new_ret_type);
                    }
                }
            }

            scope += 1;
        }

        Ok(())
    }
}
