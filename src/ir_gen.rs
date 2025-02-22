use std::collections::HashMap;

use crate::{
    pond::Target,
    ssa_ir::{Block, BlockParameter, IRInstr, IRValue, SSAIR},
    symbol_table::SymbolTable,
    BinaryOperation, CodeBlock, Expression, Literal, Program, Type, Variable, VariableDecl,
};

#[derive(Default)]
pub struct IRGen {
    pub var_counter: u32,
    pub label_counter: u32,
}

impl IRGen {
    // fn get_type(&self, scope: &mut usize, symbol_table: &SymbolTable, expr: &Expression) {
    //     match expr {
    //         Expression::Variable(var) => symbol_table.scope,
    //     }
    //     symbol_table.scope_get_symbol(scope, name, symbol_type)
    // }

    pub fn generate_ir(
        &mut self,
        program: Program,
        target: &Target,
        symbol_table: &SymbolTable,
    ) -> Result<SSAIR, String> {
        let mut ssa_ir = SSAIR::default();
        let mut scope = 0;

        for module in &program.modules {
            // self.generate_ir_codeblock(&mut scope, &module.toplevel_scope, symbol_table)?;

            for func in &module.function_defs {
                scope += 1;

                let mut parameters = Vec::new();

                for arg in &func.argument_list {
                    parameters.push(BlockParameter {
                        name: arg.arg_name.clone(),
                        ty: arg.arg_type.clone(),
                    });
                }

                ssa_ir.blocks.push(Block {
                    name: func.func_name.clone(),
                    parameters,
                    instructions: vec![],
                });
                let block_idx = ssa_ir.blocks.len() - 1;

                let instructions = self.generate_ir_codeblock(
                    &mut scope,
                    &mut ssa_ir,
                    symbol_table,
                    &mut HashMap::new(),
                    &func.function_body,
                )?;

                // stupid hack to make blocks in the correct order
                let block = ssa_ir.blocks.get_mut(block_idx).unwrap();
                block.instructions = instructions;
            }

            scope += 1;
        }

        self.figure_out_block_params(&mut ssa_ir);

        println!("{ssa_ir}");

        Ok(ssa_ir)
    }

    fn figure_out_block_params(&mut self, ssa: &mut SSAIR) {
        // let mut blocks = ssa.blocks.clone();
        // for curr_block in &mut blocks {
        //     let mut new_params = curr_block.parameters.clone();
        //     let mut local_vars = vec![];

        //     // to make sure already existing params wont get scrambled/added again
        //     for param in &new_params {
        //         local_vars.push(param.name.clone());
        //     }

        //     for instr in &mut curr_block.instructions {
        //         match instr {
        //             IRInstr::Assign(res, irvalue) => {
        //                 local_vars.push(res.clone());
        //                 if let IRValue::Variable(val) = irvalue {
        //                     if !local_vars.contains(&val.name) {
        //                         new_params.push(BlockParameter {
        //                             name: val.name.clone(),
        //                             ty: Type::Any,
        //                         })
        //                     }
        //                 }
        //             }
        //             IRInstr::BinOp(res, irvalue, irvalue1, _) => {
        //                 local_vars.push(res.clone());
        //                 if let IRValue::Variable(val) = irvalue {
        //                     if !local_vars.contains(&val.name) {
        //                         new_params.push(BlockParameter {
        //                             name: val.name.clone(),
        //                             ty: Type::Any,
        //                         })
        //                     }
        //                 }

        //                 if let IRValue::Variable(val) = irvalue1 {
        //                     if !local_vars.contains(&val.name) {
        //                         new_params.push(BlockParameter {
        //                             name: val.name.clone(),
        //                             ty: Type::Any,
        //                         })
        //                     }
        //                 }
        //             }
        //             IRInstr::UnOp(res, irvalue, unary_operation) => {
        //                 local_vars.push(res.clone());
        //                 if let IRValue::Variable(val) = irvalue {
        //                     if !local_vars.contains(&val.name) {
        //                         new_params.push(BlockParameter {
        //                             name: val.name.clone(),
        //                             ty: Type::Any,
        //                         })
        //                     }
        //                 }
        //             }
        //             IRInstr::Call(res, irvalue, args) => {
        //                 local_vars.push(res.clone());
        //                 for arg in args {
        //                     if let IRValue::Variable(val) = arg {
        //                         if !local_vars.contains(&val.name) {
        //                             new_params.push(BlockParameter {
        //                                 name: val.name.clone(),
        //                                 ty: Type::Any,
        //                             })
        //                         }
        //                     }
        //                 }
        //             }
        //             IRInstr::If(irvalue, true_label, true_args, false_label, false_args) => {
        //                 if let IRValue::Variable(val) = irvalue {
        //                     if !local_vars.contains(&val.name) {
        //                         new_params.push(BlockParameter {
        //                             name: val.name.clone(),
        //                             ty: Type::Any,
        //                         })
        //                     }
        //                 }

        //                 // add all params of branches
        //                 let true_block = ssa.blocks.iter().find(|b| b.name == *true_label).unwrap();

        //                 for arg in &true_block.parameters {
        //                     if !local_vars.contains(&arg.name) {
        //                         new_params.push(BlockParameter {
        //                             name: arg.name.clone(),
        //                             ty: Type::Any,
        //                         })
        //                     }
        //                 }

        //                 let false_block =
        //                     ssa.blocks.iter().find(|b| b.name == *false_label).unwrap();

        //                 for arg in &false_block.parameters {
        //                     if !local_vars.contains(&arg.name) {
        //                         new_params.push(BlockParameter {
        //                             name: arg.name.clone(),
        //                             ty: Type::Any,
        //                         })
        //                     }
        //                 }
        //             }
        //             IRInstr::Goto(label, args) => {
        //                 // add all params of goto
        //                 let block = ssa.blocks.iter().find(|b| b.name == *label).unwrap();

        //                 for arg in &block.parameters {
        //                     if !local_vars.contains(&arg.name) {
        //                         new_params.push(BlockParameter {
        //                             name: arg.name.clone(),
        //                             ty: Type::Any,
        //                         })
        //                     }
        //                 }
        //             }
        //             IRInstr::Return(irvalue) => {
        //                 if let IRValue::Variable(val) = irvalue {
        //                     if !local_vars.contains(&val.name) {
        //                         new_params.push(BlockParameter {
        //                             name: val.name.clone(),
        //                             ty: Type::Any,
        //                         })
        //                     }
        //                 }
        //             }
        //             IRInstr::Label(_) => unimplemented!(),
        //         }
        //     }

        //     curr_block.parameters = new_params;
        // }

        // ssa.blocks = blocks;
    }

    fn split_labels_into_blocks(ssa: &mut SSAIR, instructions: Vec<IRInstr>) -> Vec<IRInstr> {
        let mut ret_instrs = vec![];
        let mut curr_block = None;

        for instr in instructions {
            match instr {
                IRInstr::Label(label) => {
                    if let Some(curr_block) = curr_block {
                        ssa.blocks.push(curr_block);
                    }

                    curr_block = Some(Block {
                        name: label,
                        parameters: vec![],
                        instructions: vec![],
                    })
                }
                instr => {
                    if let Some(curr_block) = &mut curr_block {
                        curr_block.instructions.push(instr.clone());
                    } else {
                        ret_instrs.push(instr);
                    }
                }
            }
        }

        if let Some(curr_block) = curr_block {
            ssa.blocks.push(curr_block);
        }

        return ret_instrs;
    }

    pub fn generate_ir_codeblock(
        &mut self,
        scope: &mut usize,
        ssa: &mut SSAIR,
        symbol_table: &SymbolTable,
        renamed_vars: &mut HashMap<String, String>,
        codeblock: &CodeBlock,
    ) -> Result<Vec<IRInstr>, String> {
        let mut instructions = Vec::new();

        for expr in &codeblock.expressions {
            let (res_var, mut instrs) =
                self.generate_ir_expr(scope, ssa, symbol_table, renamed_vars, &expr)?;
            instructions.append(&mut instrs);
        }

        let remaining_instrs = Self::split_labels_into_blocks(ssa, instructions);
        Ok(remaining_instrs)
    }

    pub fn generate_ir_expr(
        &mut self,
        scope: &mut usize,
        ssa: &mut SSAIR,
        symbol_table: &SymbolTable,
        renamed_vars: &mut HashMap<String, String>,
        expr: &Expression,
    ) -> Result<(IRValue, Vec<IRInstr>), String> {
        let mut instructions = Vec::new();

        match expr {
            Expression::VariableDecl(variable_decl) => {
                let var_name = self.get_next_unique_name(&variable_decl.var_name);

                let (value, mut instrs) = self.generate_ir_expr(
                    scope,
                    ssa,
                    symbol_table,
                    renamed_vars,
                    &variable_decl.var_value,
                )?;

                renamed_vars.remove(&variable_decl.var_name);

                instructions.append(&mut instrs);

                instructions.push(IRInstr::Assign(var_name.clone(), value));

                return Ok((
                    IRValue::Variable(Variable {
                        name: var_name,
                        decl_scope: 0,
                        symbol_idx: variable_decl.symbol_idx,
                    }),
                    instructions,
                ));
            }
            Expression::Literal(literal) => {
                let value = match literal {
                    Literal::String(vec) => todo!(),
                    lit => IRValue::Literal(lit.clone()),
                };

                return Ok((value, instructions));
            }
            Expression::BinaryOp(binary_op) => {
                let res = self.get_next_unique_name("_");

                let (lhs, mut lhs_instrs) =
                    self.generate_ir_expr(scope, ssa, symbol_table, renamed_vars, &binary_op.lhs)?;
                let (rhs, mut rhs_instrs) =
                    self.generate_ir_expr(scope, ssa, symbol_table, renamed_vars, &binary_op.rhs)?;

                instructions.append(&mut lhs_instrs);
                instructions.append(&mut rhs_instrs);

                instructions.push(IRInstr::BinOp(res.clone(), lhs, rhs, binary_op.op));

                return Ok((
                    IRValue::Variable(Variable {
                        name: res,
                        decl_scope: 0,
                        symbol_idx: (0, 0),
                    }),
                    instructions,
                ));
            }
            Expression::UnaryOp(unary_op) => {
                let res = self.get_next_unique_name("_");

                let (operand, mut operand_instrs) = self.generate_ir_expr(
                    scope,
                    ssa,
                    symbol_table,
                    renamed_vars,
                    &unary_op.operand,
                )?;

                instructions.append(&mut operand_instrs);

                instructions.push(IRInstr::UnOp(res.clone(), operand, unary_op.op));

                return Ok((
                    IRValue::Variable(Variable {
                        name: res,
                        decl_scope: 0,
                        symbol_idx: (0, 0),
                    }),
                    instructions,
                ));
            }
            Expression::FunctionCall(function_call) => {
                let res = self.get_next_unique_name("_");

                let (func_expr, mut func_instrs) = self.generate_ir_expr(
                    scope,
                    ssa,
                    symbol_table,
                    renamed_vars,
                    &function_call.func_expr,
                )?;

                instructions.append(&mut func_instrs);

                let mut args = vec![];
                for arg in &function_call.arguments {
                    let (arg_expr, mut arg_instrs) =
                        self.generate_ir_expr(scope, ssa, symbol_table, renamed_vars, &arg)?;

                    instructions.append(&mut arg_instrs);

                    args.push(arg_expr);
                }

                instructions.push(IRInstr::Call(res.clone(), func_expr, args));

                return Ok((
                    IRValue::Variable(Variable {
                        name: res,
                        decl_scope: 0,
                        symbol_idx: (0, 0),
                    }),
                    instructions,
                ));
            }
            Expression::Variable(variable) => {
                if let Some(replaced_name) = renamed_vars.get(&variable.name) {
                    let mut var = variable.clone();
                    var.name = replaced_name.clone();
                    return Ok((IRValue::Variable(var), instructions));
                }
                return Ok((IRValue::Variable(variable.clone()), instructions));
            }
            Expression::Return(expression) => {
                let res = self.get_next_unique_name("_");

                let (ret_expr, mut ret_instrs) =
                    self.generate_ir_expr(scope, ssa, symbol_table, renamed_vars, &expression)?;

                instructions.append(&mut ret_instrs);
                instructions.push(IRInstr::Return(ret_expr));

                return Ok((IRValue::Literal(Literal::Int(0)), instructions));
            }
            Expression::Assignment(assignment) => {
                let res = self.get_next_unique_name("_");

                let (lhs, mut lhs_instrs) =
                    self.generate_ir_expr(scope, ssa, symbol_table, renamed_vars, &assignment.lhs)?;
                let (rhs, mut rhs_instrs) =
                    self.generate_ir_expr(scope, ssa, symbol_table, renamed_vars, &assignment.rhs)?;

                instructions.append(&mut lhs_instrs);
                instructions.append(&mut rhs_instrs);

                if let IRValue::Variable(var) = lhs.clone() {
                    instructions.push(IRInstr::Assign(res.clone(), rhs));
                    renamed_vars.insert(var.name, res.clone());
                } else {
                    panic!("Assignment to literal?");
                }

                return Ok((IRValue::Literal(Literal::Int(0)), instructions));
            }
            Expression::AnonStruct(anon_struct) => todo!(),
            Expression::ArrayLiteral(array_literal) => todo!(),
            Expression::ArrayAccess(array_access) => todo!(),
            Expression::FieldAccess(field_access) => todo!(),
            Expression::NamedStruct(named_struct) => todo!(),
            Expression::Lambda(lambda) => todo!(),
            Expression::Range(range) => todo!(),
            Expression::JS(expression) => todo!(),
            Expression::BuiltinType(expression) => todo!(),
            Expression::If(if_stmt) => {
                let res = self.get_next_unique_name("_");

                let (cond_expr, mut cond_instrs) =
                    self.generate_ir_expr(scope, ssa, symbol_table, renamed_vars, &if_stmt.cond)?;

                instructions.append(&mut cond_instrs);

                let after_if_label_name = self.get_next_unique_name("merge");
                let true_branch_label_name = self.get_next_unique_name("true");
                let false_branch_label_name = self.get_next_unique_name("false");

                // here if instr
                instructions.push(IRInstr::If(
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
                    ssa,
                    symbol_table,
                    &mut renamed_vars.clone(),
                    &if_stmt.true_branch,
                )?;

                instructions.append(&mut true_branch_instrs);
                instructions.push(IRInstr::Goto(after_if_label_name.clone(), vec![]));

                if let Some(else_branch) = &if_stmt.else_branch {
                    instructions.push(IRInstr::Label(false_branch_label_name));

                    let mut false_branch_instrs = self.generate_ir_codeblock(
                        scope,
                        ssa,
                        symbol_table,
                        &mut renamed_vars.clone(),
                        else_branch,
                    )?;

                    instructions.append(&mut false_branch_instrs);
                    instructions.push(IRInstr::Goto(after_if_label_name.clone(), vec![]));
                }
                instructions.push(IRInstr::Label(after_if_label_name));

                return Ok((IRValue::Literal(Literal::Int(0)), instructions));
            }
            Expression::For(_) => todo!(),
            Expression::Import(import) => todo!(),
            Expression::Placeholder => todo!(),
            Expression::Break => todo!(),
            Expression::Continue => todo!(),
        }
    }

    fn get_next_unique_name(&mut self, smth: &str) -> String {
        let res = format!("{smth}#{}", self.var_counter);
        self.var_counter += 1;

        return res;
    }
}
