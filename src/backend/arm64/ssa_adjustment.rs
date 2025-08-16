use crate::{
    ast::{BinaryOp, BinaryOperation, Expression, Type},
    backend::{
        arm64::ARM64Backend,
        ssa_ir::{
            self, IRAddress, IRAddressOffset, IRAddressType, IRData, IRDataLiteral, IRInstr,
            IRValue, IRVariable, SSAIR,
        },
    },
    lexer::{FStringPart, Literal},
    symbol_table::SymbolTable,
};

impl ARM64Backend<'_> {
    // Kinda cringe, copying from IRGen
    fn make_name_unique(vars: &mut Vec<IRVariable>, smth: &str) -> String {
        let res = format!("{smth}_{}", vars.len() + 1);

        return res;
    }

    fn temp_var(vars: &mut Vec<IRVariable>, ty: Type) -> usize {
        let temp_name = Self::make_name_unique(vars, "_");
        vars.push(IRVariable {
            name: temp_name,
            ty,
        });

        return vars.len() - 1;
    }

    pub fn move_floats_and_strings_to_data(
        &mut self,
        val: IRValue,
        curr_var: Option<usize>,
        instrs: &mut Vec<IRInstr>,
    ) -> (IRValue, bool) {
        let vars = &mut self.ssa_ir.vars;
        let data = &mut self.ssa_ir.data;

        if let IRValue::Literal(lit) = val {
            match lit {
                Literal::String(parts) => {
                    let var_id = if let Some(curr_var) = curr_var {
                        curr_var
                    } else {
                        Self::temp_var(vars, Type::String)
                    };

                    if parts.len() != 1 {
                        // unimplemented!("FStrings not supported yet (OR EMPTY STRINGS)")
                        instrs.push(IRInstr::Unimplemented(
                            var_id,
                            "Idk how to handle fstrings".to_string(),
                        ))
                    }

                    // FIGURE OUT HOW TO HANDLE EMPTY STRINGS
                    if let FStringPart::String(str) = &parts[0] {
                        let alias = format!("str{}", data.len());

                        data.push(IRData {
                            alias: alias.clone(),
                            value: IRDataLiteral::String(str.clone()),
                        });

                        instrs.push(IRInstr::Load(
                            var_id,
                            IRAddress {
                                addr: IRAddressType::Data(alias),
                                stored_data_type: Type::String,
                                offset: IRAddressOffset::Literal(0),
                                page: None,
                            },
                        ));

                        (IRValue::Variable(var_id), curr_var.is_some())
                    } else {
                        unimplemented!("FStrings not supported yet")
                    }
                }
                Literal::Float(num) => {
                    let alias = format!("fl{}", data.len());

                    data.push(IRData {
                        alias: alias.clone(),
                        value: IRDataLiteral::Float(num),
                    });

                    let var_id = if let Some(curr_var) = curr_var {
                        curr_var
                    } else {
                        Self::temp_var(vars, Type::Float)
                    };

                    instrs.push(IRInstr::Load(
                        var_id,
                        IRAddress {
                            addr: IRAddressType::Data(alias),
                            stored_data_type: Type::Float,
                            offset: IRAddressOffset::Literal(0),
                            page: None,
                        },
                    ));

                    (IRValue::Variable(var_id), curr_var.is_some())
                }
                lit => (IRValue::Literal(lit), false),
            }
        } else {
            (val, true)
        }
    }

    pub fn adjust_ssa_for_target(&mut self, symbol_table: &SymbolTable) {
        let blocks = std::mem::take(&mut self.ssa_ir.blocks);
        let mut new_blocks = Vec::with_capacity(blocks.len() * 2);

        for mut block in blocks {
            let old_instrs = std::mem::take(&mut block.instructions);
            block.instructions = Vec::with_capacity(old_instrs.len());
            let mut new_instrs = Vec::with_capacity(old_instrs.len());
            for instr in old_instrs {
                match instr {
                    IRInstr::Assign(res, irvalue) => {
                        let (val, assigned) = self.move_floats_and_strings_to_data(
                            irvalue,
                            Some(res),
                            &mut new_instrs,
                        );

                        if !assigned {
                            new_instrs.push(IRInstr::Assign(res, val))
                        }
                    }
                    IRInstr::BinOp(res, lhs, rhs, op) => {
                        let (mut lhs_val, lhs_assigned) = self.move_floats_and_strings_to_data(
                            lhs.clone(),
                            None,
                            &mut new_instrs,
                        );

                        let (mut rhs_val, rhs_assigned) = self.move_floats_and_strings_to_data(
                            rhs.clone(),
                            None,
                            &mut new_instrs,
                        );

                        // short circuiting and nested conditions support

                        let faux_if_expr = Box::new(Expression::BinaryOp(BinaryOp {
                            lhs: Box::new(Expression::Placeholder),
                            rhs: Box::new(Expression::Placeholder),
                            op: op.clone(),
                        }));

                        // Handle boolean statements, this is here and not in ir_gen because different targets might need different handling here
                        match op {
                            BinaryOperation::Equal
                            | BinaryOperation::NotEqual
                            | BinaryOperation::Greater
                            | BinaryOperation::GreaterEqual
                            | BinaryOperation::Less
                            | BinaryOperation::LessEqual => {
                                new_instrs.push(IRInstr::BinOp(res, lhs_val, rhs_val, op.clone()));
                                let cmp_is_true = self.ssa_ir.make_name_unique("cond_is_true");
                                let cmp_is_false = self.ssa_ir.make_name_unique("cond_is_false");
                                let cmp_end = self.ssa_ir.make_name_unique("cond_end");

                                new_instrs.push(IRInstr::If(
                                    faux_if_expr,
                                    IRValue::Variable(res),
                                    cmp_is_true.clone(),
                                    vec![],
                                    cmp_is_false.clone(),
                                    vec![],
                                ));
                                new_instrs.push(IRInstr::Label(cmp_is_true.clone()));
                                new_instrs.push(IRInstr::Assign(
                                    res,
                                    IRValue::Literal(Literal::Boolean(true)),
                                ));
                                new_instrs.push(IRInstr::Goto(cmp_end.clone(), vec![]));
                                new_instrs.push(IRInstr::Label(cmp_is_false.clone()));
                                new_instrs.push(IRInstr::Assign(
                                    res,
                                    IRValue::Literal(Literal::Boolean(false)),
                                ));
                                new_instrs.push(IRInstr::Goto(cmp_end.clone(), vec![]));
                                new_instrs.push(IRInstr::Label(cmp_end.clone()));
                            }
                            BinaryOperation::And => {
                                let and_end = self.ssa_ir.make_name_unique("and_end");
                                let and_chk_rhs = self.ssa_ir.make_name_unique("and_chk_rhs");
                                let and_true = self.ssa_ir.make_name_unique("and_true");
                                let and_false = self.ssa_ir.make_name_unique("and_false");

                                // If lhs is true
                                new_instrs.push(IRInstr::If(
                                    faux_if_expr.clone(),
                                    lhs_val,
                                    and_chk_rhs.clone(),
                                    vec![],
                                    and_false.clone(),
                                    vec![],
                                ));

                                new_instrs.push(IRInstr::Label(and_chk_rhs.clone()));

                                // let temp_var = self.temp_var(ty.clone());
                                // instructions.push(IRInstr::UnOp(temp_var, rhs, UnaryOperation::Negate));

                                // If rhs is true
                                new_instrs.push(IRInstr::If(
                                    faux_if_expr.clone(),
                                    rhs_val,
                                    and_true.clone(),
                                    vec![],
                                    and_false.clone(),
                                    vec![],
                                ));

                                new_instrs.push(IRInstr::Label(and_false.clone()));
                                new_instrs.push(IRInstr::Assign(
                                    res,
                                    IRValue::Literal(Literal::Boolean(false)),
                                ));

                                new_instrs.push(IRInstr::Goto(and_end.clone(), vec![]));
                                new_instrs.push(IRInstr::Label(and_true.clone()));

                                new_instrs.push(IRInstr::Assign(
                                    res,
                                    IRValue::Literal(Literal::Boolean(true)),
                                ));

                                new_instrs.push(IRInstr::Goto(and_end.clone(), vec![]));
                                new_instrs.push(IRInstr::Label(and_end.clone()));
                            }
                            BinaryOperation::Or => {
                                let or_end = self.ssa_ir.make_name_unique("or_end");
                                let or_chk_rhs = self.ssa_ir.make_name_unique("or_chk_rhs");
                                let or_false = self.ssa_ir.make_name_unique("or_false");
                                let or_true = self.ssa_ir.make_name_unique("or_true");

                                // If lhs is true
                                new_instrs.push(IRInstr::If(
                                    faux_if_expr.clone(),
                                    lhs_val,
                                    or_true.clone(),
                                    vec![],
                                    or_chk_rhs.clone(),
                                    vec![],
                                ));

                                new_instrs.push(IRInstr::Label(or_chk_rhs.clone()));

                                // If rhs is true
                                new_instrs.push(IRInstr::If(
                                    faux_if_expr.clone(),
                                    rhs_val,
                                    or_true.clone(),
                                    vec![],
                                    or_false.clone(),
                                    vec![],
                                ));

                                new_instrs.push(IRInstr::Label(or_false.clone()));

                                new_instrs.push(IRInstr::Assign(
                                    res,
                                    IRValue::Literal(Literal::Boolean(false)),
                                ));
                                new_instrs.push(IRInstr::Goto(or_end.clone(), vec![]));
                                new_instrs.push(IRInstr::Label(or_true.clone()));
                                new_instrs.push(IRInstr::Assign(
                                    res,
                                    IRValue::Literal(Literal::Boolean(true)),
                                ));

                                new_instrs.push(IRInstr::Goto(or_end.clone(), vec![]));

                                new_instrs.push(IRInstr::Label(or_end.clone()));
                            }
                            _ => {
                                // fix for `op lit reg` - most instrs dont support this order
                                if matches!(lhs, IRValue::Literal(_)) {
                                    // turn it into `op reg lit`
                                    let tmp = lhs_val;
                                    lhs_val = rhs_val;
                                    rhs_val = tmp;

                                    // if its `op lit1 lit2` now then turn into
                                    // `mov temp_reg lit1`
                                    // `op temp_reg lit2`
                                    // fixme: this is stupid sometimes i think
                                    if let IRValue::Literal(ref lit) = rhs {
                                        // hacky but ok
                                        let temp_name = self.ssa_ir.make_name_unique("_");
                                        self.ssa_ir.vars.push(IRVariable {
                                            name: temp_name,
                                            ty: lit.ty().clone(),
                                        });
                                        let temp_var_id = self.ssa_ir.vars.len() - 1;

                                        new_instrs.push(IRInstr::Assign(temp_var_id, lhs_val));

                                        lhs_val = IRValue::Variable(temp_var_id);
                                    }
                                }

                                // multiply doesnt support multiplying by literal
                                if let BinaryOperation::Multiply = op {
                                    if let IRValue::Literal(ref lit) = rhs {
                                        let temp_name = self.ssa_ir.make_name_unique("_");
                                        self.ssa_ir.vars.push(IRVariable {
                                            name: temp_name,
                                            ty: lit.ty().clone(),
                                        });
                                        let temp_var_id = self.ssa_ir.vars.len() - 1;

                                        new_instrs.push(IRInstr::Assign(temp_var_id, rhs_val));
                                        rhs_val = IRValue::Variable(temp_var_id);
                                    }
                                }

                                new_instrs.push(IRInstr::BinOp(res, lhs_val, rhs_val, op));
                            }
                        }
                    }
                    IRInstr::UnOp(res, operand, op) => {
                        let (operand_val, operand_assigned) =
                            self.move_floats_and_strings_to_data(operand, None, &mut new_instrs);

                        new_instrs.push(IRInstr::UnOp(res, operand_val, op))
                    }
                    IRInstr::Call(res, called, args) => {
                        let mut new_args = vec![];
                        for arg in args {
                            let (arg_val, _) =
                                self.move_floats_and_strings_to_data(arg, None, &mut new_instrs);

                            new_args.push(arg_val);
                        }

                        new_instrs.push(IRInstr::Call(res, called, new_args))
                    }
                    _if @ IRInstr::If(..) => new_instrs.push(_if),
                    goto @ IRInstr::Goto(..) => new_instrs.push(goto),
                    IRInstr::Store(addr, val) => {
                        let (mut new_val, _) = self.move_floats_and_strings_to_data(
                            val.clone(),
                            None,
                            &mut new_instrs,
                        );

                        // Store needs a register to read from and not a literal
                        if let IRValue::Literal(ref lit) = val {
                            let temp_name = self.ssa_ir.make_name_unique("_");
                            self.ssa_ir.vars.push(IRVariable {
                                name: temp_name,
                                ty: lit.ty().clone(),
                            });
                            let temp_var_id = self.ssa_ir.vars.len() - 1;

                            new_instrs.push(IRInstr::Assign(temp_var_id, new_val));
                            new_val = IRValue::Variable(temp_var_id);
                        }

                        new_instrs.push(IRInstr::Store(addr, new_val));
                    }
                    load @ IRInstr::Load(..) => new_instrs.push(load),
                    IRInstr::Return(ret) => {
                        if let Some(ret) = ret {
                            let (ret_val, _) =
                                self.move_floats_and_strings_to_data(ret, None, &mut new_instrs);

                            new_instrs.push(IRInstr::Return(Some(ret_val)))
                        } else {
                            new_instrs.push(IRInstr::Return(ret))
                        }
                    }
                    label @ IRInstr::Label(..) => new_instrs.push(label),
                    inline @ IRInstr::InlineTarget(..) => new_instrs.push(inline),
                    unimpl @ IRInstr::Unimplemented(..) => new_instrs.push(unimpl),
                }
            }
            let (instrs, mut blocks) = ssa_ir::split_labels_into_blocks(new_instrs);
            block.instructions = instrs;
            new_blocks.push(block);
            new_blocks.append(&mut blocks);
        }

        self.ssa_ir.blocks = new_blocks;

        // for block_idx in 0..self.ssa_ir.blocks.len() {
        //     let func_name = self.ssa_ir.blocks[block_idx].func_name.clone();
        //     if func_name.is_some() {
        //     }
        // }
        self.ssa_ir.figure_out_block_params_for_func(0);
        self.ssa_ir.fix_passing_parameters_by_gotos(0);
        self.ssa_ir.build_partial_cf_graph(0);
    }
}
