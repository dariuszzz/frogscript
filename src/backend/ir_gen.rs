use super::ssa_ir;
use std::{collections::HashMap, ptr::read};

use crate::{
    ast::{FunctionType, SymbolIdx, UnaryOperation},
    backend::ssa_ir::{IRAddressOffset, IRAddressType, IRData, IRDataLiteral, InlineTargetPart},
    lexer::FStringPart,
    pond::{Dependency, Target},
    ssa_ir::{Block, IRAddress, IRInstr, IRValue, IRVariable, VariableID, SSAIR},
    symbol_table::*,
    Arena, BinaryOperation, CodeBlock, Expression, Literal, Program, Type, Variable, VariableDecl,
};

#[derive(Default)]
pub struct LoopInfo {
    pub start_label: String,
    pub end_label: String,
}

#[derive(Default)]
pub struct IRGen {
    pub ssa_ir: SSAIR,
}

impl IRGen {
    // fn get_type(&self, scope: &mut usize, symbol_table: &SymbolTable, expr: &Expression) {
    //     match expr {
    //         Expression::Variable(var) => symbol_table.scope,
    //     }
    //     symbol_table.scope_get_symbol(scope, name, symbol_type)
    // }

    fn ir_val_ty(&self, ir_val: &IRValue) -> Type {
        match ir_val {
            // idk
            IRValue::Address(v) => Type::Uint,
            IRValue::Variable(v) => self.ssa_ir.vars[*v].ty.clone(),
            IRValue::Literal(lit) => match lit {
                Literal::String(_) => Type::String,
                Literal::Int(_) => Type::Int,
                Literal::Uint(_) => Type::Uint,
                Literal::Float(_) => Type::Float,
                Literal::Boolean(_) => Type::Boolean,
            },
        }
    }

    fn temp_var(&mut self, ty: Type) -> usize {
        let temp_name = self.make_name_unique("_");
        self.ssa_ir.vars.push(IRVariable {
            name: temp_name,
            ty,
        });

        return self.ssa_ir.vars.len() - 1;
    }

    fn symbol_idx_to_name(symbol_idx: &SymbolIdx) -> String {
        format!("s{}i{}", symbol_idx.0, symbol_idx.1)
    }

    fn symbol_idx_to_var(&mut self, symbol_idx: &SymbolIdx, ty: Type) -> usize {
        let name = Self::symbol_idx_to_name(symbol_idx);
        self.ssa_ir.vars.push(IRVariable { name, ty });

        return self.ssa_ir.vars.len() - 1;
    }

    fn named_var(&mut self, name: &str, ty: Type) -> usize {
        self.ssa_ir.vars.push(IRVariable {
            name: name.to_string(),
            ty,
        });

        return self.ssa_ir.vars.len() - 1;
    }

    pub fn generate_ir(
        &mut self,
        program: Program,
        target: Option<&Target>,
        symbol_table: &SymbolTable,
    ) -> Result<SSAIR, String> {
        let mut scope = 0;

        for module in &program.modules {
            let mod_scope_idx = symbol_table
                .module_to_scope
                .get(&module.module_name)
                .unwrap();

            let mod_scope = symbol_table.table.get(*mod_scope_idx).unwrap();

            for func in &module.function_defs {
                scope += 1;

                let func_name = Self::symbol_idx_to_name(&func.symbol_idx);

                if let Some(target) = target {
                    if func.func_name == target.func {
                        self.ssa_ir.entry_block = func_name.clone();
                    }
                }

                // hacky way to get func_symbol
                let func_symbol = mod_scope.symbols.get(func.symbol_idx.1).unwrap();

                self.ssa_ir.func_names.push(func_name.clone());

                self.ssa_ir.vars.push(IRVariable {
                    name: func_name.clone(),
                    ty: func_symbol.value_type.clone(),
                    // Type::Function(FunctionType {
                    //     env_args: vec![],
                    //     args: vec![], // TODO: ADD ARG PARAMS
                    //     ret: Box::new(func.return_type.clone()),
                    // }),
                });
            }
        }

        for module in &program.modules {
            for func in &module.function_defs {
                let func_name = Self::symbol_idx_to_name(&func.symbol_idx);

                let mut parameters = Vec::new();

                let mut renamed_vars = HashMap::new();

                for arg in &func.argument_list {
                    let arg_id = self.symbol_idx_to_var(&arg.symbol_idx, arg.arg_type.clone());
                    let var_name = self.ssa_ir.vars[arg_id].name.clone();
                    parameters.push(arg_id);
                    renamed_vars.insert(arg.arg_name.clone(), var_name.clone());

                    match &arg.arg_type {
                        Type::Array(inner) => {
                            let addr = IRAddress {
                                addr: IRAddressType::Register(format!("{var_name}")),
                                stored_data_type: *inner.clone(),
                                offset: IRAddressOffset::Literal(0),
                            };
                            self.ssa_ir.stack_vars.insert(arg_id, addr);
                        }
                        _ => {}
                    }
                }

                self.ssa_ir.blocks.push(Block {
                    func_name: Some((func.symbol_idx, func.func_name.clone())),
                    name: func_name,
                    parameters,
                    instructions: vec![],
                });
                let block_idx = self.ssa_ir.blocks.len() - 1;

                let instructions = self.generate_ir_codeblock(
                    &mut scope,
                    symbol_table,
                    &mut renamed_vars,
                    &LoopInfo::default(),
                    &func.function_body,
                )?;

                // these are the instructions before any label
                let (remaining_instrs, mut blocks) = ssa_ir::split_labels_into_blocks(instructions);
                self.ssa_ir.blocks.append(&mut blocks);
                let block = self.ssa_ir.blocks.get_mut(block_idx).unwrap();
                block.instructions = remaining_instrs;
                self.ssa_ir
                    .prune_all_instructions_after_first_branch(block_idx);
                self.ssa_ir.figure_out_block_params_for_func(block_idx);
            }

            scope += 1;
        }

        self.ssa_ir.fix_passing_parameters_by_gotos(0);
        self.ssa_ir.build_partial_cf_graph(0);

        Ok(self.ssa_ir.clone())
    }

    pub fn generate_ir_codeblock(
        &mut self,
        scope: &mut usize,
        symbol_table: &SymbolTable,
        renamed_vars: &mut HashMap<String, String>,
        loop_info: &LoopInfo,
        codeblock: &CodeBlock,
    ) -> Result<Vec<IRInstr>, String> {
        let mut instructions = Vec::new();

        for expr in &codeblock.expressions {
            let (res_var, mut instrs, _) =
                self.generate_ir_expr(scope, symbol_table, renamed_vars, loop_info, &expr, None)?;
            instructions.append(&mut instrs);
        }

        Ok(instructions)
    }

    pub fn generate_ir_expr(
        &mut self,
        scope: &mut usize,
        symbol_table: &SymbolTable,
        renamed_vars: &mut HashMap<String, String>,
        loop_info: &LoopInfo,
        expr: &Expression,
        curr_var: Option<usize>,
        // expr result, new instructions, already assigned?
    ) -> Result<(IRValue, Vec<IRInstr>, bool), String> {
        let mut instructions = Vec::new();

        match expr {
            Expression::VariableDecl(variable_decl) => {
                let var_id = self
                    .symbol_idx_to_var(&variable_decl.symbol_idx, variable_decl.var_type.clone());
                let var_name = self.ssa_ir.vars[var_id].name.clone();

                let (value, mut instrs, alr_assigned) = self.generate_ir_expr(
                    scope,
                    symbol_table,
                    renamed_vars,
                    loop_info,
                    &variable_decl.var_value,
                    Some(var_id),
                )?;

                renamed_vars.insert(variable_decl.var_name.clone(), var_name.clone());

                instructions.append(&mut instrs);

                if !alr_assigned {
                    // Similar thing as in Expr::Assign
                    match value {
                        rhs @ IRValue::Variable(_) | rhs @ IRValue::Literal(_) => {
                            instructions.push(IRInstr::Assign(var_id, rhs))
                        }
                        IRValue::Address(addr) => instructions.push(IRInstr::Load(var_id, addr)),
                    }
                }

                return Ok((IRValue::Variable(var_id), instructions, true));
            }
            Expression::Literal(literal) => {
                return Ok((IRValue::Literal(literal.clone()), instructions, false));
            }
            expr @ Expression::BinaryOp(binary_op) => {
                let (lhs, mut lhs_instrs, _) = self.generate_ir_expr(
                    scope,
                    symbol_table,
                    renamed_vars,
                    loop_info,
                    &binary_op.lhs,
                    None,
                )?;
                let (rhs, mut rhs_instrs, _) = self.generate_ir_expr(
                    scope,
                    symbol_table,
                    renamed_vars,
                    loop_info,
                    &binary_op.rhs,
                    None,
                )?;

                instructions.append(&mut lhs_instrs);
                instructions.append(&mut rhs_instrs);

                let ty = self.ir_val_ty(&lhs);
                let var_id = if let Some(curr_var) = curr_var {
                    curr_var
                } else {
                    self.temp_var(ty.clone())
                };
                instructions.push(IRInstr::BinOp(var_id, lhs.clone(), rhs, binary_op.op));

                // let idx_var = if let IRValue::Variable(var) = index {
                //     var
                // } else {
                //     let temp = self.temp_var(self.ir_val_ty(&index));
                //     instructions.push(IRInstr::Assign(temp, index));
                //     temp
                // };

                return Ok((IRValue::Variable(var_id), instructions, curr_var.is_some()));
            }
            Expression::UnaryOp(unary_op) => {
                let (operand, mut operand_instrs, _) = self.generate_ir_expr(
                    scope,
                    symbol_table,
                    renamed_vars,
                    loop_info,
                    &unary_op.operand,
                    None,
                )?;

                instructions.append(&mut operand_instrs);

                let var_id = if let Some(curr_var) = curr_var {
                    curr_var
                } else {
                    self.temp_var(self.ir_val_ty(&operand))
                };

                instructions.push(IRInstr::UnOp(var_id, operand.clone(), unary_op.op));

                return Ok((IRValue::Variable(var_id), instructions, curr_var.is_some()));
            }
            Expression::FunctionCall(function_call) => {
                let (mut func_expr, mut func_instrs, _) = self.generate_ir_expr(
                    scope,
                    symbol_table,
                    renamed_vars,
                    loop_info,
                    &function_call.func_expr,
                    None,
                )?;

                // if let IRValue::IRVariable(func) = &mut func_expr {
                // let func_symbol = symbol_table
                //     .get_scope(func.symbol_idx.0)
                //     .unwrap()
                //     .symbols
                //     .get(func.symbol_idx.1)
                //     .unwrap();

                // func.name = func_symbol.qualified_name.clone();
                // }

                instructions.append(&mut func_instrs);

                let mut args = vec![];
                for arg in &function_call.arguments {
                    let (mut arg_expr, mut arg_instrs, assigned) = self.generate_ir_expr(
                        scope,
                        symbol_table,
                        renamed_vars,
                        loop_info,
                        &arg,
                        None,
                    )?;

                    instructions.append(&mut arg_instrs);

                    args.push(arg_expr);
                }

                let var_id = if let Some(curr_var) = curr_var {
                    curr_var
                } else {
                    // TODO: this should have the return type as type
                    self.temp_var(self.ir_val_ty(&func_expr))
                };
                instructions.push(IRInstr::Call(var_id, func_expr.clone(), args));

                return Ok((IRValue::Variable(var_id), instructions, curr_var.is_some()));
            }
            Expression::Variable(variable) => {
                let name_to_find = if let Some(replaced_name) = renamed_vars.get(&variable.name) {
                    replaced_name
                } else {
                    &Self::symbol_idx_to_name(&variable.symbol_idx)
                };

                for (idx, var) in self.ssa_ir.vars.iter().enumerate() {
                    if var.name == *name_to_find {
                        return Ok((IRValue::Variable(idx), instructions, curr_var.is_some()));
                    }
                }

                unreachable!("{name_to_find}, {}", variable.name)
            }
            Expression::Return(expression) => {
                let expr = if let Some(expr) = expression {
                    let (ret_expr, mut ret_instrs, _) = self.generate_ir_expr(
                        scope,
                        symbol_table,
                        renamed_vars,
                        loop_info,
                        &expr,
                        None,
                    )?;

                    instructions.append(&mut ret_instrs);
                    Some(ret_expr)
                } else {
                    None
                };

                instructions.push(IRInstr::Return(expr));

                return Ok((IRValue::Literal(Literal::Int(0)), instructions, true));
            }
            Expression::Assignment(assignment) => {
                let (lhs, mut lhs_instrs, lhs_assigned) = self.generate_ir_expr(
                    scope,
                    symbol_table,
                    renamed_vars,
                    loop_info,
                    &assignment.lhs,
                    None,
                )?;

                let ty = self.ir_val_ty(&lhs);

                // This is so we assign rhs directly to lhs if lhs is a variable
                let lhs_var = if let IRValue::Variable(var_id) = lhs.clone() {
                    Some(var_id)
                } else {
                    None
                };

                let (rhs, mut rhs_instrs, rhs_assigned) = self.generate_ir_expr(
                    scope,
                    symbol_table,
                    renamed_vars,
                    loop_info,
                    &assignment.rhs,
                    lhs_var,
                )?;

                instructions.append(&mut lhs_instrs);
                instructions.append(&mut rhs_instrs);

                if !rhs_assigned {
                    // var = addr -> load to lhs
                    // addr = var -> store rhs
                    // var = var -> mov rhs to lhs
                    // addr = addr -> load rhs to temp, store temp to lhs

                    use IRValue::*;

                    // Soo many unneccessary allocs lol, but i think this is the cleanest way
                    let mut instrs = match (lhs, rhs) {
                        (Variable(lhs), rhs @ Variable(_) | rhs @ Literal(_)) => {
                            vec![IRInstr::Assign(lhs, rhs)]
                        }
                        (Variable(lhs), Address(rhs)) => vec![IRInstr::Load(lhs, rhs)],
                        (Address(lhs), rhs @ Variable(_) | rhs @ Literal(_)) => {
                            vec![IRInstr::Store(lhs, rhs)]
                        }
                        (Address(lhs), Address(rhs)) => {
                            let temp = self.temp_var(ty);
                            vec![
                                IRInstr::Load(temp, rhs),
                                IRInstr::Store(lhs, IRValue::Variable(temp)),
                            ]
                        }
                        _ => unreachable!("Assigning to a literal is not allowed duh"),
                    };

                    instructions.append(&mut instrs);
                }

                return Ok((IRValue::Literal(Literal::Int(0)), instructions, true));
            }
            Expression::AnonStruct(anon_struct) => {
                let var_id = self.temp_var(Type::Any);
                return Ok((
                    IRValue::Variable(var_id),
                    vec![IRInstr::Unimplemented(var_id, format!("Anon struct"))],
                    true,
                ));
            }
            Expression::ArrayLiteral(array_literal) => {
                let mut inner_ty = Type::Any;
                let mut offset_size = 0;
                let mut offset = 0;

                for el in &array_literal.elements {
                    let (el, mut el_instrs, _) = self.generate_ir_expr(
                        scope,
                        symbol_table,
                        renamed_vars,
                        loop_info,
                        &el,
                        None,
                    )?;

                    inner_ty = self.ir_val_ty(&el);

                    offset_size = inner_ty.size() as isize;
                    offset -= offset_size;

                    instructions.append(&mut el_instrs);
                    instructions.push(IRInstr::Store(
                        IRAddress {
                            addr: IRAddressType::Register("fp".to_string()),
                            stored_data_type: inner_ty.clone(),
                            offset: IRAddressOffset::Literal(offset),
                        },
                        el,
                    ));
                }

                let array_type = Type::Array(Box::new(inner_ty.clone()));

                let var_id = if let Some(curr_var) = curr_var {
                    curr_var
                } else {
                    self.temp_var(array_type.clone())
                };

                let arr_addr = IRAddress {
                    addr: IRAddressType::Register("fp".to_string()),
                    stored_data_type: array_type,
                    offset: IRAddressOffset::Literal(-offset_size),
                };

                self.ssa_ir.stack_vars.insert(var_id, arr_addr.clone());

                instructions.push(IRInstr::Assign(var_id, IRValue::Address(arr_addr)));

                return Ok((IRValue::Variable(var_id), instructions, curr_var.is_some()));
            }
            Expression::ArrayAccess(array_access) => {
                let (index, mut index_instrs, _) = self.generate_ir_expr(
                    scope,
                    symbol_table,
                    renamed_vars,
                    loop_info,
                    &array_access.index,
                    None,
                )?;

                let (expr, mut expr_instrs, _) = self.generate_ir_expr(
                    scope,
                    symbol_table,
                    renamed_vars,
                    loop_info,
                    &array_access.expr,
                    None,
                )?;

                instructions.append(&mut index_instrs);
                instructions.append(&mut expr_instrs);

                let array_type = self.ir_val_ty(&expr);

                if let Type::Array(inner) = array_type.clone() {
                    let idx_var = if let IRValue::Variable(var) = index {
                        var
                    } else {
                        let temp = self.temp_var(self.ir_val_ty(&index));
                        instructions.push(IRInstr::Assign(temp, index));
                        temp
                    };

                    let expr_var = if let IRValue::Variable(var) = expr {
                        var
                    } else {
                        let temp = self.temp_var(array_type);
                        instructions.push(IRInstr::Assign(temp, expr));
                        temp
                    };

                    let res_var = if let Some(curr_var) = curr_var {
                        curr_var
                    } else {
                        self.temp_var(*inner.clone())
                    };

                    let expr_name = &self.ssa_ir.vars[expr_var].name;
                    let idx_name = &self.ssa_ir.vars[idx_var].name;

                    let expr_addr = &self
                        .ssa_ir
                        .stack_vars
                        .get(&expr_var)
                        .expect(&format!(
                            "FAILED TO FIND STACK VARIABLE IN ARRAY ACCESS FIX {expr_name}"
                        ))
                        .clone();

                    let expr_addr_offset = match expr_addr.offset {
                        IRAddressOffset::Literal(lit) => lit,
                        IRAddressOffset::IRVariable(_) => unreachable!("prob not gonna happen?"),
                    };

                    let el_size = 8;

                    // Multiply the index by the size of each element as we are addressing in bytes
                    instructions.push(IRInstr::BinOp(
                        idx_var,
                        IRValue::Variable(idx_var),
                        IRValue::Literal(Literal::Int(-el_size)),
                        BinaryOperation::Multiply,
                    ));

                    // Shift to expr addr offset
                    instructions.push(IRInstr::BinOp(
                        idx_var,
                        IRValue::Variable(idx_var),
                        IRValue::Literal(Literal::Int(expr_addr_offset)),
                        BinaryOperation::Add,
                    ));

                    let final_addr = IRAddress {
                        addr: expr_addr.addr.clone(),
                        stored_data_type: *inner,
                        offset: ssa_ir::IRAddressOffset::IRVariable(idx_var),
                    };

                    instructions.push(IRInstr::Load(res_var, final_addr.clone()));

                    return Ok((IRValue::Variable(res_var), instructions, curr_var.is_some()));
                } else {
                    unreachable!("Tried to access non-array type?")
                }
            }
            Expression::FieldAccess(field_access) => {
                let res = self.temp_var(Type::Any);
                return Ok((
                    IRValue::Variable(res),
                    vec![IRInstr::Unimplemented(res, format!("Field access"))],
                    true,
                ));
            }
            Expression::NamedStruct(named_struct) => {
                let res = self.temp_var(Type::Any);
                return Ok((
                    IRValue::Variable(res),
                    vec![IRInstr::Unimplemented(res, format!("Named struct"))],
                    true,
                ));
            }
            Expression::Lambda(lambda) => {
                let res = self.temp_var(Type::Any);
                return Ok((
                    IRValue::Variable(res),
                    vec![IRInstr::Unimplemented(res, format!("Lambda"))],
                    true,
                ));
            }
            Expression::Range(range) => {
                let res = self.temp_var(Type::Any);
                return Ok((
                    IRValue::Variable(res),
                    vec![IRInstr::Unimplemented(res, format!("Range"))],
                    true,
                ));
            }
            Expression::BuiltinTarget(expr) => {
                let res = if let Some(curr_var) = curr_var {
                    curr_var
                } else {
                    self.temp_var(Type::Any)
                };

                let mut instrs_parts = Vec::new();
                if let Expression::Literal(Literal::String(parts)) = expr.as_ref() {
                    for part in parts {
                        let part = match part {
                            // TODO: this doesnt work if expr is an if or a for since js doesnt support that
                            FStringPart::Code(expr) => {
                                let (expr, mut instrs, _) = self.generate_ir_expr(
                                    scope,
                                    symbol_table,
                                    renamed_vars,
                                    loop_info,
                                    &expr,
                                    None,
                                )?;

                                if let IRValue::Variable(var) = expr {
                                    InlineTargetPart::SSAIRVarRef(var)
                                } else {
                                    unreachable!()
                                }
                            }
                            FStringPart::String(string) => {
                                InlineTargetPart::String(string.clone().replace("\\", ""))
                            }
                        };
                        instrs_parts.push(part);
                    }
                }

                let mut used_registers = Vec::new();
                let last_part = instrs_parts.last_mut();
                if let Some(InlineTargetPart::String(end)) = last_part {
                    let split: Vec<_> = end.split("|").collect();

                    if split.len() >= 2 {
                        let first_half = split[0].to_string();
                        let used_regs_text = split[1];

                        used_registers = used_regs_text
                            .split(" ")
                            .filter(|l| !l.is_empty())
                            .map(|s| s.trim().to_string())
                            .collect();

                        *end = first_half;
                    }
                }

                return Ok((
                    IRValue::Variable(res),
                    vec![IRInstr::InlineTarget(instrs_parts, used_registers)],
                    true,
                ));
            }
            Expression::BuiltinType(expression) => {
                unreachable!("I think");
                let res = self.temp_var(Type::Any);
                return Ok((
                    IRValue::Variable(res),
                    vec![IRInstr::Unimplemented(res, format!("@type"))],
                    true,
                ));
            }
            Expression::If(if_stmt) => {
                let after_if_label_name = self.make_name_unique("merge");
                let true_branch_label_name = self.make_name_unique("true");
                let false_branch_label_name = self.make_name_unique("false");

                let (cond_expr, mut cond_instrs, _) = self.generate_ir_expr(
                    scope,
                    symbol_table,
                    renamed_vars,
                    loop_info,
                    &if_stmt.cond,
                    None,
                )?;

                instructions.append(&mut cond_instrs);

                // here if instr
                instructions.push(IRInstr::If(
                    if_stmt.cond.clone(),
                    cond_expr,
                    true_branch_label_name.clone(),
                    vec![],
                    if if_stmt.else_branch.is_some() {
                        false_branch_label_name.clone()
                    } else {
                        after_if_label_name.clone()
                    },
                    vec![],
                ));

                instructions.push(IRInstr::Label(true_branch_label_name));

                let mut true_branch_instrs = self.generate_ir_codeblock(
                    scope,
                    symbol_table,
                    &mut renamed_vars.clone(),
                    loop_info,
                    &if_stmt.true_branch,
                )?;

                instructions.append(&mut true_branch_instrs);
                instructions.push(IRInstr::Goto(after_if_label_name.clone(), vec![]));

                if let Some(else_branch) = &if_stmt.else_branch {
                    instructions.push(IRInstr::Label(false_branch_label_name));

                    let mut false_branch_instrs = self.generate_ir_codeblock(
                        scope,
                        symbol_table,
                        &mut renamed_vars.clone(),
                        loop_info,
                        else_branch,
                    )?;

                    instructions.append(&mut false_branch_instrs);
                    instructions.push(IRInstr::Goto(after_if_label_name.clone(), vec![]));
                }
                instructions.push(IRInstr::Label(after_if_label_name));

                return Ok((IRValue::Literal(Literal::Int(0)), instructions, true));
            }
            Expression::For(for_expr) => {
                let loop_cond_label = self.make_name_unique("loop_cond");
                let loop_body_label = self.make_name_unique("loop_body");
                let loop_end_label = self.make_name_unique("loop_end");
                instructions.push(IRInstr::Goto(loop_cond_label.clone(), vec![]));
                instructions.push(IRInstr::Label(loop_cond_label.clone()));

                let binding_var_id =
                    self.symbol_idx_to_var(&for_expr.symbol_idx, for_expr.binding_type.clone());
                let (iterator_expr, mut iterator_instrs, iterator_assigned) = self
                    .generate_ir_expr(
                        scope,
                        symbol_table,
                        renamed_vars,
                        loop_info,
                        &for_expr.iterator,
                        Some(binding_var_id),
                    )?;

                let binding_var_name = self.ssa_ir.vars[binding_var_id].name.clone();
                renamed_vars.insert(for_expr.binding.clone(), binding_var_name);

                instructions.append(&mut iterator_instrs);

                // FIXME: this shouldnt be commented out, breaks on some iterators, redo the whole loop binding thing
                // if !iterator_assigned {
                instructions.push(IRInstr::Assign(binding_var_id, iterator_expr.clone()));
                // }

                // instructions for condition checking here...
                //
                //  ---
                instructions.push(IRInstr::If(
                    for_expr.iterator.clone(),
                    iterator_expr,
                    loop_body_label.clone(),
                    vec![],
                    loop_end_label.clone(),
                    vec![],
                ));
                instructions.push(IRInstr::Label(loop_body_label.clone()));

                let mut loop_body = self.generate_ir_codeblock(
                    scope,
                    symbol_table,
                    &mut renamed_vars.clone(),
                    &LoopInfo {
                        start_label: loop_cond_label.clone(),
                        end_label: loop_end_label.clone(),
                    },
                    &for_expr.body,
                )?;
                instructions.append(&mut loop_body);

                instructions.push(IRInstr::Goto(loop_cond_label.clone(), vec![]));
                instructions.push(IRInstr::Label(loop_end_label.clone()));

                return Ok((IRValue::Literal(Literal::Int(0)), instructions, true));
            }
            Expression::Import(import) => {
                return Ok((IRValue::Literal(Literal::Int(0)), instructions, true));
            }
            Expression::Placeholder => {
                return Ok((IRValue::Literal(Literal::Int(0)), instructions, true));
            }
            Expression::Break => {
                instructions.push(IRInstr::Goto(loop_info.end_label.clone(), vec![]));
                return Ok((IRValue::Literal(Literal::Int(0)), instructions, true));
            }
            Expression::Continue => {
                instructions.push(IRInstr::Goto(loop_info.start_label.clone(), vec![]));
                return Ok((IRValue::Literal(Literal::Int(0)), instructions, true));
            }
        }
    }

    fn make_name_unique(&mut self, smth: &str) -> String {
        self.ssa_ir.make_name_unique(smth)
    }
}
