use crate::{
    ast::Type,
    backend::{
        arm64::ARM64Backend,
        ssa_ir::{
            IRAddress, IRAddressOffset, IRAddressType, IRData, IRDataLiteral, IRInstr, IRValue,
            IRVariable, SSAIR,
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
        val: IRValue,
        curr_var: Option<usize>,
        data: &mut Vec<IRData>,
        instrs: &mut Vec<IRInstr>,
        vars: &mut Vec<IRVariable>,
    ) -> (IRValue, bool) {
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
        let SSAIR {
            blocks, data, vars, ..
        } = &mut self.ssa_ir;

        for block in blocks {
            let old_instrs = std::mem::take(&mut block.instructions);
            block.instructions = Vec::with_capacity(old_instrs.len() * 2);
            let block_instrs = &mut block.instructions;
            for instr in old_instrs {
                match instr {
                    IRInstr::Assign(res, irvalue) => {
                        let (val, assigned) = Self::move_floats_and_strings_to_data(
                            irvalue,
                            Some(res),
                            data,
                            block_instrs,
                            vars,
                        );

                        if !assigned {
                            block_instrs.push(IRInstr::Assign(res, val))
                        }
                    }
                    IRInstr::BinOp(res, lhs, rhs, op) => {
                        let (lhs_val, lhs_assigned) = Self::move_floats_and_strings_to_data(
                            lhs,
                            None,
                            data,
                            block_instrs,
                            vars,
                        );

                        let (rhs_val, rhs_assigned) = Self::move_floats_and_strings_to_data(
                            rhs,
                            None,
                            data,
                            block_instrs,
                            vars,
                        );

                        block_instrs.push(IRInstr::BinOp(res, lhs_val, rhs_val, op))
                    }
                    IRInstr::UnOp(res, operand, op) => {
                        let (operand_val, operand_assigned) = Self::move_floats_and_strings_to_data(
                            operand,
                            None,
                            data,
                            block_instrs,
                            vars,
                        );

                        block_instrs.push(IRInstr::UnOp(res, operand_val, op))
                    }
                    IRInstr::Call(res, called, args) => {
                        let mut new_args = vec![];
                        for arg in args {
                            let (arg_val, _) = Self::move_floats_and_strings_to_data(
                                arg,
                                None,
                                data,
                                block_instrs,
                                vars,
                            );

                            new_args.push(arg_val);
                        }

                        block_instrs.push(IRInstr::Call(res, called, new_args))
                    }
                    _if @ IRInstr::If(..) => block_instrs.push(_if),
                    goto @ IRInstr::Goto(..) => block_instrs.push(goto),
                    IRInstr::Store(addr, val) => {
                        let (new_val, _) = Self::move_floats_and_strings_to_data(
                            val,
                            None,
                            data,
                            block_instrs,
                            vars,
                        );

                        block_instrs.push(IRInstr::Store(addr, new_val));
                    }
                    load @ IRInstr::Load(..) => block_instrs.push(load),
                    IRInstr::Return(ret) => {
                        if let Some(ret) = ret {
                            let (ret_val, _) = Self::move_floats_and_strings_to_data(
                                ret,
                                None,
                                data,
                                block_instrs,
                                vars,
                            );

                            block_instrs.push(IRInstr::Return(Some(ret_val)))
                        } else {
                            block_instrs.push(IRInstr::Return(ret))
                        }
                    }
                    label @ IRInstr::Label(..) => block_instrs.push(label),
                    inline @ IRInstr::InlineTarget(..) => block_instrs.push(inline),
                    unimpl @ IRInstr::Unimplemented(..) => block_instrs.push(unimpl),
                }
            }
        }
    }
}
