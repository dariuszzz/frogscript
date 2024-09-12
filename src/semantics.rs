use std::{
    collections::{HashMap, HashSet},
    f64::consts::PI,
    fmt::Debug,
};

use crate::{
    ast::{CodeBlock, Expression, FunctionCall, Variable, VariableDecl},
    parser::Program,
    Arena, BinaryOperation, CustomType, FunctionType, Lambda, Module, NamedStruct, StructDef,
    StructField, Type, TypeKind,
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
}

impl Scope {
    pub fn with_parent(parent: usize) -> Self {
        Self {
            parent_scope: Some(parent),
            children_scopes: Vec::new(),
            symbols: Vec::new(),
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct SemanticAnalyzer {
    pub symbol_table: Arena<Scope>,
    pub module_to_scope: HashMap<String, usize>,
}

impl SemanticAnalyzer {
    /*

    pub fn typecheck(&mut self, expr: &mut Expression, module: &Module) -> Result<Type, String> {
        match expr {
            Expression::VariableDecl(var_decl) => {
                let rhs_type = self.typecheck(&mut var_decl.var_value, module)?;

                if let TypeKind::Infer = var_decl.var_type.type_kind {
                    var_decl.var_type = rhs_type.clone();
                } else if var_decl.var_type != rhs_type {
                    return Err(format!("Invalid rhs type in var decl"));
                }

                Ok(rhs_type)
            }
            Expression::Literal(literal) => {
                let type_kind = match literal {
                    crate::Literal::String(_) => TypeKind::String,
                    crate::Literal::Int(_) => TypeKind::Int,
                    crate::Literal::Uint(_) => TypeKind::Uint,
                    crate::Literal::Float(_) => TypeKind::Float,
                    crate::Literal::Boolean(_) => TypeKind::Boolean,
                };

                Ok(Type {
                    type_kind,
                    is_reference: false,
                    is_structural: false,
                })
            }
            Expression::BinaryOp(bin_op) => {
                let lhs_type = self.typecheck(&mut bin_op.lhs, module)?;
                let rhs_type = self.typecheck(&mut bin_op.rhs, module)?;

                let int_type = Type {
                    type_kind: TypeKind::Int,
                    is_reference: false,
                    is_structural: false,
                };
                let uint_type = Type {
                    type_kind: TypeKind::Uint,
                    is_reference: false,
                    is_structural: false,
                };
                let float_type = Type {
                    type_kind: TypeKind::Float,
                    is_reference: false,
                    is_structural: false,
                };
                let bool_type = Type {
                    type_kind: TypeKind::Boolean,
                    is_reference: false,
                    is_structural: false,
                };

                match bin_op.op {
                    BinaryOperation::Add
                    | BinaryOperation::Subtract
                    | BinaryOperation::Multiply
                    | BinaryOperation::Divide
                    | BinaryOperation::Less
                    | BinaryOperation::LessEqual
                    | BinaryOperation::Greater
                    | BinaryOperation::GreaterEqual
                    | BinaryOperation::Power => {
                        if lhs_type != int_type && lhs_type != uint_type && lhs_type != float_type {
                            return Err(format!(
                                "Operands to this binary operation must be int/float/uint"
                            ));
                        }
                    }
                    BinaryOperation::Equal
                    | BinaryOperation::And
                    | BinaryOperation::Or
                    | BinaryOperation::NotEqual => {
                        if lhs_type != bool_type {
                            return Err(format!("Operands to this binary operation must be bool"));
                        }
                    }
                }

                if lhs_type != rhs_type {
                    return Err(format!("Binary op operands are of different types"));
                }

                Ok(lhs_type.clone())
            }
            Expression::UnaryOp(unary) => self.typecheck(&mut unary.operand, module),
            Expression::FunctionCall(func_call) => {
                let FunctionCall {
                    func_expr,
                    arguments,
                } = func_call;

                let function_symbol = self.typecheck(func_expr, module)?;

                let func_arg_types =
                    if let TypeKind::Function(func_type) = function_symbol.type_kind.clone() {
                        func_type.args.clone()
                    } else {
                        unreachable!()
                    };

                for (i, arg) in arguments.iter_mut().enumerate() {
                    let arg_type = self.typecheck(arg, module)?;

                    if arg_type != func_arg_types[i] {
                        return Err(format!("Invalid arg type in function call"));
                    }
                }

                Ok(function_symbol)
            }
            Expression::Variable(variable) => {
                println!("{:?}", variable.name);
                println!("{:?}", self.symbol_table);
                let var_type = self.find_external_symbol(SymbolType::Identifier, &variable.name)[0]
                    .value_type
                    .clone();

                Ok(var_type)
            }
            Expression::Return(ret) => self.typecheck(ret, module),
            Expression::Assignment(assignment) => {
                let lhs_type = self.typecheck(&mut assignment.lhs, module)?;
                let rhs_type = self.typecheck(&mut assignment.rhs, module)?;

                if lhs_type != rhs_type {
                    return Err(format!("Assignment operands are of different types"));
                }

                Ok(lhs_type.clone())
            }
            Expression::AnonStruct(anon) => {
                let mut struct_type = StructDef { fields: Vec::new() };

                for (name, field) in &mut anon.fields {
                    struct_type.fields.push(StructField {
                        field_name: name.clone(),
                        field_type: self.typecheck(field, module)?,
                        is_final: false,
                    });
                }

                Ok(Type {
                    type_kind: TypeKind::Struct(struct_type),
                    is_reference: false,
                    is_structural: false,
                })
            }
            Expression::ArrayLiteral(arr) => {
                if arr.elements.len() > 0 {
                    let arr_type = self.typecheck(&mut arr.elements[0], module)?;

                    for elem in &mut arr.elements {
                        let elem_type = self.typecheck(elem, module)?;

                        if arr_type != elem_type {
                            return Err(format!("Elements in array arent all of the same type"));
                        }
                    }

                    Ok(arr_type)
                } else {
                    return Err(format!("Cannot infer type of array"));
                    // Ok(Type {
                    //     type_kind: TypeKind::Infer,
                    //     is_reference: false,
                    //     is_structural: false,
                    // })
                }
            }
            Expression::ArrayAccess(arr_access) => {
                if let TypeKind::Array(inner) =
                    self.typecheck(&mut arr_access.expr, module)?.type_kind
                {
                    let valid_index_type = Type {
                        type_kind: TypeKind::Uint,
                        is_reference: false,
                        is_structural: false,
                    };
                    if self.typecheck(&mut arr_access.index, module)? != valid_index_type {
                        return Err(format!("Array access index must be a uint"));
                    }

                    Ok(inner.as_ref().clone())
                } else {
                    return Err(format!("Array access operator is used on non-array type"));
                }
            }
            Expression::FieldAccess(field_access) => {
                if let TypeKind::Struct(struct_type) =
                    self.typecheck(&mut field_access.expr, module)?.type_kind
                {
                    let mut field_type = None;
                    for field in &struct_type.fields {
                        if field.field_name == field_access.field {
                            field_type = Some(field.field_type.clone());
                            break;
                        }
                    }

                    if field_type.is_none() {
                        return Err(format!("Field {} doesn't exist", field_access.field));
                    }

                    Ok(field_type.unwrap())
                } else {
                    return Err(format!("Field access is only possible on structs"));
                }
            }
            Expression::NamedStruct(named_struct) => {
                let precast_type = self.typecheck(
                    &mut Expression::AnonStruct(named_struct.struct_literal.clone()),
                    module,
                )?;

                let casted_type = self
                    .find_external_symbol(SymbolType::Type, &named_struct.casted_to)[0]
                    .value_type
                    .clone();

                match (precast_type.type_kind, casted_type.type_kind.clone()) {
                    (TypeKind::Struct(precast), TypeKind::Struct(casted)) => {
                        for field in &precast.fields {
                            if !casted.fields.contains(field) {
                                return Err(format!(
                                    "Field {} does not exist on {}",
                                    field.field_name, named_struct.casted_to
                                ));
                            }
                        }

                        for field in &casted.fields {
                            if !precast.fields.contains(field) {
                                return Err(format!(
                                    "Field {} is missing from struct literal",
                                    field.field_name
                                ));
                            }
                        }
                    }
                    _ => {
                        return Err(format!(
                            "Named struct doesn't consist of a struct type and a struct literal"
                        ))
                    }
                }

                Ok(casted_type)
            }
            Expression::Lambda(lambda) => {
                let mut lambda_type = FunctionType {
                    env_args: Vec::new(),
                    args: Vec::new(),
                    ret: Box::new(lambda.return_type.clone()),
                };

                for arg in &lambda.argument_list {
                    let arg_type = arg.arg_type.clone();
                    if arg.is_env {
                        lambda_type.env_args.push(arg_type);
                    } else {
                        lambda_type.args.push(arg_type);
                    }
                }

                Ok(Type {
                    type_kind: TypeKind::Function(lambda_type),
                    is_reference: false,
                    is_structural: false,
                })
            }
            Expression::Range(range) => {
                let lhs_type = self.typecheck(&mut range.start, module)?;
                let rhs_type = self.typecheck(&mut range.end, module)?;

                let int_type = Type {
                    type_kind: TypeKind::Int,
                    is_reference: false,
                    is_structural: false,
                };

                let uint_type = Type {
                    type_kind: TypeKind::Uint,
                    is_reference: false,
                    is_structural: false,
                };

                if lhs_type != int_type && lhs_type != uint_type {
                    return Err(format!("Range start and end must be ints or uints"));
                }

                if lhs_type != rhs_type {
                    return Err(format!("Assignment operands are of different types"));
                }

                Ok(lhs_type.clone())
            }
            Expression::If(if_expr) => {
                let bool_type = Type {
                    type_kind: TypeKind::Boolean,
                    is_reference: false,
                    is_structural: false,
                };

                if self.typecheck(&mut if_expr.cond, module)? != bool_type {
                    return Err(format!("If condition must be a boolean"));
                }

                let true_type = self.typecheck_codeblock(&mut if_expr.true_branch, module)?;
                if let Some(else_branch) = &mut if_expr.else_branch {
                    let false_type = self.typecheck_codeblock(else_branch, module)?;

                    if true_type != false_type {
                        return Err(format!("True and else branches must have the same type"));
                    }
                }

                Ok(true_type)
            }
            Expression::For(for_expr) => {
                let iterator_type = if let TypeKind::Array(inner) =
                    self.typecheck(&mut for_expr.iterator, module)?.type_kind
                {
                    inner.as_ref().clone()
                } else {
                    return Err(format!("For expression iterator must be an array"));
                };

                if let TypeKind::Infer = for_expr.binding_type.type_kind {
                    for_expr.binding_type = iterator_type.clone();
                } else if iterator_type != for_expr.binding_type {
                    return Err(format!(
                        "For expression iterator must be the same type as binding"
                    ));
                }

                let body_type = self.typecheck_codeblock(&mut for_expr.body, module)?;

                Ok(body_type)
            }
            Expression::JS(_) => todo!(),
            Expression::Placeholder => todo!(),
            Expression::Break => todo!(),
            Expression::Continue => todo!(),
        }
    }
    fn typecheck_codeblock(
        &mut self,
        codeblock: &mut CodeBlock,
        module: &Module,
    ) -> Result<Type, String> {
        let mut last_type = Type {
            type_kind: TypeKind::Void,
            is_reference: false,
            is_structural: false,
        };

        for expr in &mut codeblock.expressions {
            last_type = self.typecheck(expr, module)?;
        }

        Ok(last_type)
    }

    */
    // pub fn resolve_type_name(
    //     &mut self,
    //     module_name: &String,
    //     local_symbols: &HashMap<String, Symbol>,
    //     kind: &mut TypeKind,
    // ) -> Result<(), String> {
    //     match kind {
    //         TypeKind::Infer => {}
    //         TypeKind::Void
    //         | TypeKind::Int
    //         | TypeKind::Uint
    //         | TypeKind::Float
    //         | TypeKind::String
    //         | TypeKind::Boolean => {}
    //         TypeKind::Custom(custom) => {
    //             let CustomType { name } = custom;

    //             let split_name = name.split("::").collect::<Vec<_>>();
    //             if split_name.len() == 1 {
    //                 let local_type = local_symbols.get(name);
    //                 if let Some(symbol) = local_type {
    //                     if symbol.symbol_type != SymbolType::Type {
    //                         return Err(format!("Identifier '{name}' exists, but is not a type"));
    //                     }
    //                 } else {
    //                     return Err(format!("Type '{name}' is not defined"));
    //                 }
    //             } else {
    //                 let type_symbol = self.find_external_symbol(SymbolType::Type, &name);
    //                 if type_symbol.len() == 1 {
    //                     if !type_symbol[0].exported {
    //                         return Err(format!("Type '{name}' is defined but not exported"));
    //                     }
    //                 } else if type_symbol.len() == 0 {
    //                     return Err(format!("Type '{name}' is not defined"));
    //                 } else {
    //                     return Err(format!("Type '{name}' is ambiguous"));
    //                 }
    //             }
    //         }
    //         TypeKind::Array(inner) => {
    //             self.resolve_type_name(module_name, local_symbols, &mut inner.type_kind)?;
    //         }
    //         TypeKind::Function(func) => {
    //             let FunctionType {
    //                 env_args,
    //                 args,
    //                 ret,
    //             } = func;

    //             for env_arg in env_args {
    //                 self.resolve_type_name(module_name, local_symbols, &mut env_arg.type_kind)?;
    //             }
    //             for arg in args {
    //                 self.resolve_type_name(module_name, local_symbols, &mut arg.type_kind)?;
    //             }

    //             self.resolve_type_name(module_name, local_symbols, &mut ret.type_kind)?;
    //         }
    //         TypeKind::Struct(struct_type) => {
    //             let StructDef { fields } = struct_type;

    //             for field in fields {
    //                 self.resolve_type_name(
    //                     module_name,
    //                     local_symbols,
    //                     &mut field.field_type.type_kind,
    //                 )?;
    //             }
    //         }
    //     }

    //     Ok(())
    // }

    // pub fn resolve_name_expr(
    //     &mut self,
    //     module_name: &String,
    //     local_symbols: &HashMap<String, Symbol>,
    //     expr: &mut Expression,
    // ) -> Result<(), String> {
    //     match expr {
    //         Expression::Lambda(lambda) => {
    //             let Lambda {
    //                 argument_list,
    //                 return_type,
    //                 function_body,
    //             } = lambda;

    //             let mut local_symbols = local_symbols.clone();

    //             for arg in argument_list {
    //                 self.resolve_type_name(
    //                     module_name,
    //                     &local_symbols,
    //                     &mut arg.arg_type.type_kind,
    //                 )?;

    //                 local_symbols.insert(
    //                     arg.arg_name.clone(),
    //                     Symbol {
    //                         original_name: arg.arg_name.clone(),
    //                         symbol_type: SymbolType::Identifier,
    //                         value_type: arg.arg_type.clone(),
    //                         exported: false,
    //                     },
    //                 );
    //             }
    //             self.resolve_type_name(module_name, &local_symbols, &mut return_type.type_kind)?;
    //             self.resolve_names_codeblock(module_name, &local_symbols, function_body)?;
    //         }
    //         Expression::VariableDecl(var_decl) => {
    //             self.resolve_type_name(
    //                 module_name,
    //                 local_symbols,
    //                 &mut var_decl.var_type.type_kind,
    //             )?;
    //             self.resolve_name_expr(module_name, local_symbols, &mut var_decl.var_value)?;
    //         }
    //         Expression::Literal(_) => {}
    //         Expression::BinaryOp(op) => {
    //             self.resolve_name_expr(module_name, local_symbols, &mut op.lhs)?;
    //             self.resolve_name_expr(module_name, local_symbols, &mut op.rhs)?;
    //         }
    //         Expression::UnaryOp(op) => {
    //             self.resolve_name_expr(module_name, local_symbols, &mut op.operand)?;
    //         }
    //         Expression::FunctionCall(func_call) => {
    //             let FunctionCall {
    //                 func_expr,
    //                 arguments,
    //             } = func_call;

    //             //if function comes from another module
    //             match func_expr.as_mut() {
    //                 Expression::Variable(Variable { name: func_name }) => {
    //                     if func_name.split("::").count() > 1 {
    //                         let identifiers_with_the_same_name =
    //                             self.find_external_symbol(SymbolType::Identifier, &func_name);

    //                         if identifiers_with_the_same_name.len() == 1 {
    //                             let iden = identifiers_with_the_same_name[0];
    //                             if !iden.exported {
    //                                 return Err(format!("External function '{func_name}' found, but it is not marked as `export`"));
    //                             }
    //                             // symbol exists
    //                         } else if identifiers_with_the_same_name.len() > 1 {
    //                             return Err(format!("Ambiguous function call '{func_name}'"));
    //                         } else {
    //                             return Err(format!(
    //                                 "External function '{func_name}' is not defined"
    //                             ));
    //                         }
    //                     } else {
    //                         let local_func = local_symbols.get(func_name);
    //                         if let Some(symbol) = local_func {
    //                             if symbol.symbol_type == SymbolType::Type {
    //                                 return Err(format!("Function '{func_name}' is not defined"));
    //                             }
    //                         } else {
    //                             return Err(format!("Function '{func_name}' is not defined"));
    //                         }
    //                     }
    //                 }
    //                 expr => self.resolve_name_expr(module_name, local_symbols, expr)?,
    //             }

    //             for arg in arguments {
    //                 self.resolve_name_expr(module_name, local_symbols, arg)?;
    //             }
    //         }
    //         Expression::Variable(var) => {
    //             let Variable { name } = var;

    //             if name.split("::").count() > 1 {
    //                 let identifiers_with_the_same_name =
    //                     self.find_external_symbol(SymbolType::Identifier, &name);

    //                 if identifiers_with_the_same_name.len() == 1 {
    //                     let iden = identifiers_with_the_same_name[0];
    //                     if !iden.exported {
    //                         return Err(format!("External variable '{name}' found, but it is not marked as `export`"));
    //                     }
    //                     // symbol exists
    //                 } else if identifiers_with_the_same_name.len() > 1 {
    //                     return Err(format!("Ambiguous identifier '{name}'"));
    //                 } else {
    //                     return Err(format!("External identifier '{name}' is not defined"));
    //                 }
    //             } else {
    //                 let local_func = local_symbols.get(name);
    //                 if let Some(symbol) = local_func {
    //                     if symbol.symbol_type != SymbolType::Identifier {
    //                         return Err(format!("Identifier '{name}' exists, but does not refer to a variable or function"));
    //                     }
    //                 } else {
    //                     return Err(format!("Identifier '{name}' is not defined"));
    //                 }
    //             }
    //         }
    //         Expression::Return(ret) => self.resolve_name_expr(module_name, local_symbols, ret)?,
    //         Expression::Assignment(assignment) => {
    //             self.resolve_name_expr(module_name, local_symbols, &mut assignment.rhs)?;
    //         }
    //         Expression::AnonStruct(anon_struct) => {
    //             for (_, expr) in &mut anon_struct.fields {
    //                 self.resolve_name_expr(module_name, local_symbols, expr)?
    //             }
    //         }
    //         Expression::ArrayLiteral(arr) => {
    //             for expr in &mut arr.elements {
    //                 self.resolve_name_expr(module_name, local_symbols, expr)?;
    //             }
    //         }
    //         Expression::ArrayAccess(arr_access) => {
    //             self.resolve_name_expr(module_name, local_symbols, &mut arr_access.expr)?;
    //             self.resolve_name_expr(module_name, local_symbols, &mut arr_access.index)?;
    //         }
    //         Expression::FieldAccess(field_access) => {
    //             self.resolve_name_expr(module_name, local_symbols, &mut field_access.expr)?;
    //         }
    //         Expression::NamedStruct(named_struct) => {
    //             for (_, expr) in &mut named_struct.struct_literal.fields {
    //                 self.resolve_name_expr(module_name, local_symbols, expr)?;
    //             }
    //         }
    //         Expression::Range(range) => {
    //             self.resolve_name_expr(module_name, local_symbols, &mut range.start)?;
    //             self.resolve_name_expr(module_name, local_symbols, &mut range.end)?;
    //         }
    //         Expression::JS(expr) => {
    //             for expr in expr {
    //                 self.resolve_name_expr(module_name, local_symbols, expr)?;
    //             }
    //         }
    //         Expression::If(if_expr) => {
    //             self.resolve_name_expr(module_name, local_symbols, &mut if_expr.cond)?;
    //             self.resolve_names_codeblock(module_name, local_symbols, &mut if_expr.true_branch)?;

    //             if let Some(else_branch) = &mut if_expr.else_branch {
    //                 self.resolve_names_codeblock(module_name, local_symbols, else_branch)?;
    //             }
    //         }
    //         Expression::For(for_expr) => {
    //             self.resolve_name_expr(module_name, local_symbols, &mut for_expr.iterator)?;

    //             self.resolve_type_name(
    //                 module_name,
    //                 &local_symbols,
    //                 &mut for_expr.binding_type.type_kind,
    //             )?;

    //             let mut local_symbols = local_symbols.clone();
    //             local_symbols.insert(
    //                 for_expr.binding.clone(),
    //                 Symbol {
    //                     original_name: for_expr.binding.clone(),
    //                     symbol_type: SymbolType::Identifier,
    //                     value_type: for_expr.binding_type.clone(),
    //                     exported: false,
    //                 },
    //             );

    //             self.resolve_names_codeblock(module_name, &local_symbols, &mut for_expr.body)?;
    //         }
    //         Expression::Placeholder => {}
    //         Expression::Break => {}
    //         Expression::Continue => {}
    //     }

    //     Ok(())
    // }

    // pub fn resolve_names_codeblock(
    //     &mut self,
    //     module_name: &String,
    //     local_symbols: &HashMap<String, Symbol>,
    //     codeblock: &mut CodeBlock,
    // ) -> Result<(), String> {
    //     let mut local_symbols = local_symbols.clone();

    //     for expr in &mut codeblock.expressions {
    //         self.resolve_name_expr(module_name, &local_symbols, expr)?;

    //         if let Expression::VariableDecl(var_decl) = expr {
    //             local_symbols.insert(
    //                 var_decl.var_name.clone(),
    //                 Symbol {
    //                     original_name: var_decl.var_name.clone(),
    //                     symbol_type: SymbolType::Identifier,
    //                     value_type: var_decl.var_type.clone(),
    //                     exported: false,
    //                 },
    //             );
    //         }
    //     }

    //     Ok(())
    // }

    // pub fn resolve_names(&mut self, program: &mut Program) -> Result<(), String> {
    //     let mut local_symbols_by_module: HashMap<String, HashMap<String, Symbol>> = HashMap::new();
    //     for module in &mut program.modules {
    //         println!("resolving names in {:?}", module.module_name);
    //         local_symbols_by_module.insert(module.module_name.clone(), HashMap::new());

    //         let local_symbols = local_symbols_by_module
    //             .get_mut(&module.module_name)
    //             .unwrap();

    //         for custom_type in &module.type_defs {
    //             if self
    //                 .find_external_symbol(SymbolType::Type, &custom_type.name)
    //                 .len()
    //                 > 1
    //             {
    //                 return Err(format!("Type '{}' is already defined", custom_type.name));
    //             }

    //             self.symbol_table.push(Symbol {
    //                 original_name: format!("{}::{}", module.module_name, custom_type.name),
    //                 symbol_type: SymbolType::Type,
    //                 value_type: custom_type.value.clone(),
    //                 exported: custom_type.export,
    //             });

    //             local_symbols.insert(
    //                 custom_type.name.clone(),
    //                 Symbol {
    //                     original_name: custom_type.name.clone(),
    //                     symbol_type: SymbolType::Type,
    //                     value_type: custom_type.value.clone(),
    //                     exported: custom_type.export,
    //                 },
    //             );
    //         }

    //         for func in &mut module.function_defs {
    //             if self
    //                 .find_external_symbol(SymbolType::Identifier, &func.func_name)
    //                 .len()
    //                 > 1
    //             {
    //                 return Err(format!(
    //                     "Identifier '{}' is already defined",
    //                     func.func_name
    //                 ));
    //             }

    //             let mut func_type = FunctionType {
    //                 env_args: Vec::new(),
    //                 args: Vec::new(),
    //                 ret: Box::new(func.return_type.clone()),
    //             };

    //             for arg in &func.argument_list {
    //                 let arg_type = arg.arg_type.clone();
    //                 if arg.is_env {
    //                     func_type.env_args.push(arg_type);
    //                 } else {
    //                     func_type.args.push(arg_type);
    //                 }
    //             }

    //             self.symbol_table.push(Symbol {
    //                 original_name: format!("{}::{}", module.module_name, func.func_name),
    //                 symbol_type: SymbolType::Identifier,
    //                 value_type: Type {
    //                     type_kind: TypeKind::Function(func_type.clone()),
    //                     is_reference: false,
    //                     is_structural: false,
    //                 },
    //                 exported: func.export,
    //             });

    //             local_symbols.insert(
    //                 func.func_name.clone(),
    //                 Symbol {
    //                     original_name: func.func_name.clone(),
    //                     symbol_type: SymbolType::Identifier,
    //                     value_type: Type {
    //                         type_kind: TypeKind::Function(func_type),
    //                         is_reference: false,
    //                         is_structural: false,
    //                     },
    //                     exported: func.export,
    //                 },
    //             );
    //         }

    //         for var in &module.toplevel_scope.expressions {
    //             if let Expression::VariableDecl(var_decl) = var {
    //                 if var_decl.var_name != "_"
    //                     && self
    //                         .find_external_symbol(SymbolType::Identifier, &var_decl.var_name)
    //                         .len()
    //                         > 1
    //                 {
    //                     return Err(format!(
    //                         "Top-level variable '{}' is already defined",
    //                         var_decl.var_name
    //                     ));
    //                 }

    //                 self.symbol_table.push(Symbol {
    //                     original_name: format!("{}::{}", module.module_name, var_decl.var_name),
    //                     symbol_type: SymbolType::Identifier,
    //                     value_type: var_decl.var_type.clone(),
    //                     exported: false,
    //                 });

    //                 local_symbols.insert(
    //                     var_decl.var_name.clone(),
    //                     Symbol {
    //                         original_name: var_decl.var_name.clone(),
    //                         symbol_type: SymbolType::Identifier,
    //                         value_type: var_decl.var_type.clone(),
    //                         exported: false,
    //                     },
    //                 );
    //             }
    //         }
    //     }

    //     for module in &mut program.modules {
    //         let local_symbols = local_symbols_by_module
    //             .get(&module.module_name.clone())
    //             .unwrap();

    //         for func in &mut module.function_defs {
    //             let mut local_symbols = local_symbols.clone();
    //             let mut defined_arguments = Vec::new();

    //             self.resolve_type_name(
    //                 &module.module_name,
    //                 &local_symbols,
    //                 &mut func.return_type.type_kind,
    //             )?;

    //             for arg in &mut func.argument_list {
    //                 self.resolve_type_name(
    //                     &module.module_name,
    //                     &local_symbols,
    //                     &mut arg.arg_type.type_kind,
    //                 )?;

    //                 local_symbols.insert(
    //                     arg.arg_name.clone(),
    //                     Symbol {
    //                         original_name: arg.arg_name.clone(),
    //                         symbol_type: SymbolType::Identifier,
    //                         value_type: arg.arg_type.clone(),
    //                         exported: false,
    //                     },
    //                 );

    //                 if defined_arguments.contains(&arg.arg_name) {
    //                     return Err(format!("Duplicate argument '{}'", arg.arg_name));
    //                 }

    //                 defined_arguments.push(arg.arg_name.clone())
    //             }

    //             self.resolve_names_codeblock(
    //                 &module.module_name,
    //                 &local_symbols,
    //                 &mut func.function_body,
    //             )?;
    //         }

    //         for var in &mut module.toplevel_scope.expressions {
    //             match var {
    //                 Expression::VariableDecl(var_decl) => {
    //                     let VariableDecl { var_value, .. } = var_decl;

    //                     let local_symbols = local_symbols.clone();
    //                     self.resolve_name_expr(&module.module_name, &local_symbols, var_value)?;
    //                 }
    //                 // This is always the main() function call inserted by the parser
    //                 Expression::FunctionCall(func_call) => {
    //                     if let Expression::Variable(Variable { name }) =
    //                         func_call.func_expr.as_mut()
    //                     {
    //                         *name = format!("{}::{}", module.module_name, name.clone());
    //                     }
    //                 }
    //                 _ => unreachable!("Invalid toplevel expression only let bindings allowed"),
    //             }
    //         }
    //     }

    //     Ok(())
    // }

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
            Expression::Placeholder => todo!(),
            Expression::Break => todo!(),
            Expression::Continue => todo!(),
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
                        value_type: Type {
                            type_kind: TypeKind::Custom(CustomType {
                                name: type_def.name.clone(),
                            }),
                            is_reference: false,
                            is_structural: false,
                        },
                        exported: type_def.export,
                    },
                )?;
            }

            for func_def in &module.function_defs {
                let func_type = Type {
                    type_kind: TypeKind::Function(FunctionType {
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
                    }),
                    is_reference: false,
                    is_structural: false,
                };

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

    fn resolve_names_expr(&mut self, scope: &mut usize, expr: &Expression) -> Result<(), String> {
        match expr {
            Expression::Variable(expr) => {
                let name_parts = expr.name.split("::").collect::<Vec<_>>();

                let mut scope_idx = if name_parts.len() == 1 {
                    Some(scope.clone())
                } else {
                    let scope = self
                        .module_to_scope
                        .get(name_parts[0])
                        .expect("Symbol table not built");

                    Some(scope.clone())
                };

                while let Some(curr_scope_idx) = scope_idx {
                    let curr_scope = self.symbol_table.get(curr_scope_idx).unwrap();

                    if SemanticAnalyzer::scope_get_symbol(
                        &curr_scope,
                        &name_parts.last().unwrap(),
                        SymbolType::Identifier,
                    )
                    .is_none()
                    {
                        scope_idx = curr_scope.parent_scope
                    } else {
                        return Ok(());
                    }
                }

                return Err(format!("Identifier not found `{}`", expr.name));
            }
            Expression::VariableDecl(expr) => {
                self.resolve_names_expr(scope, &expr.var_value)?;
            }
            Expression::Literal(_) => {}
            Expression::BinaryOp(expr) => {
                self.resolve_names_expr(scope, &expr.lhs)?;
                self.resolve_names_expr(scope, &expr.rhs)?;
            }
            Expression::UnaryOp(expr) => {
                self.resolve_names_expr(scope, &expr.operand)?;
            }
            Expression::FunctionCall(expr) => {
                self.resolve_names_expr(scope, &expr.func_expr)?;

                for arg in &expr.arguments {
                    self.resolve_names_expr(scope, &arg)?;
                }
            }
            Expression::Return(expr) => {
                self.resolve_names_expr(scope, &expr)?;
            }
            Expression::Assignment(expr) => {
                self.resolve_names_expr(scope, &expr.lhs)?;
                self.resolve_names_expr(scope, &expr.rhs)?;
            }
            Expression::AnonStruct(expr) => {
                for (_, expr) in &expr.fields {
                    self.resolve_names_expr(scope, &expr)?;
                }
            }
            Expression::ArrayLiteral(expr) => {
                for elem in &expr.elements {
                    self.resolve_names_expr(scope, &elem)?;
                }
            }
            Expression::ArrayAccess(expr) => {
                self.resolve_names_expr(scope, &expr.expr)?;
                self.resolve_names_expr(scope, &expr.index)?;
            }
            Expression::FieldAccess(expr) => {
                self.resolve_names_expr(scope, &expr.expr)?;
            }
            Expression::NamedStruct(expr) => {
                for (_, expr) in &expr.struct_literal.fields {
                    self.resolve_names_expr(scope, &expr)?;
                }
            }
            Expression::Lambda(expr) => {
                *scope += 1;
                self.resolve_names_codeblock(scope, &expr.function_body)?;
            }
            Expression::Range(expr) => {
                self.resolve_names_expr(scope, &expr.start)?;
                self.resolve_names_expr(scope, &expr.end)?;
            }
            Expression::If(expr) => {
                self.resolve_names_expr(scope, &expr.cond)?;
                *scope += 1;
                self.resolve_names_codeblock(scope, &expr.true_branch)?;
                if let Some(else_branch) = &expr.else_branch {
                    *scope += 1;
                    self.resolve_names_codeblock(scope, &else_branch)?;
                }
            }
            Expression::For(expr) => {
                self.resolve_names_expr(scope, &expr.iterator)?;
                *scope += 1;
                self.resolve_names_codeblock(scope, &expr.body)?;
            }
            Expression::JS(expr) => {
                for expr in expr {
                    self.resolve_names_expr(scope, expr)?;
                }
            }
            Expression::Placeholder => todo!(),
            Expression::Break => todo!(),
            Expression::Continue => todo!(),
        }

        Ok(())
    }

    fn resolve_names_codeblock(
        &mut self,
        scope: &mut usize,
        codeblock: &CodeBlock,
    ) -> Result<(), String> {
        for expr in &codeblock.expressions {
            self.resolve_names_expr(scope, expr)?;
        }

        Ok(())
    }

    pub fn resolve_names(&mut self, program: &Program) -> Result<(), String> {
        let mut scope = 0;
        for module in &program.modules {
            self.resolve_names_codeblock(&mut scope, &module.toplevel_scope)?;

            for func_def in &module.function_defs {
                scope += 1;
                self.resolve_names_codeblock(&mut scope, &func_def.function_body)?;
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

    pub fn perform_analysis(&mut self, program: &mut Program) -> Result<(), String> {
        // self.enable_shadowing(program)?;
        self.populate_symbol_table(program)?;
        self.resolve_names(program)?;
        self.enforce_mutability(program)?;

        Ok(())
    }
}
