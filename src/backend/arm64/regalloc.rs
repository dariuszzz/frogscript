use std::collections::{HashMap, HashSet};

use crate::{
    ast::Type,
    backend::{
        arm64::asm_ir::{
            get_instruction_set, get_instruction_set_reg, get_reg_ty, ASMInstr, ASMValue, ASMVar,
            AllocPlace, Register, RegisterType, ASMIR,
        },
        liveness::InstrIndex,
        ssa_ir::{IRAddress, IRAddressOffset, IRAddressType, InlineTargetPart},
    },
};

pub struct RegallocState {
    pub register_to_var: HashMap<Register, usize>,
    pub var_to_register: HashMap<usize, Register>,
    pub possible_registers: Vec<Register>,
}

impl RegallocState {
    pub fn new(available_registers: Vec<Register>) -> Self {
        Self {
            register_to_var: HashMap::new(),
            var_to_register: HashMap::new(),
            possible_registers: available_registers,
        }
    }

    fn mark_registers_storing_dead_values_as_free(&mut self, live_variables: &Vec<usize>) {
        for (var, reg) in self.var_to_register.clone() {
            // Variable is not used -> clear registers storing it
            if !live_variables.contains(&var) {
                self.var_to_register.remove(&var);
                self.register_to_var.remove(&reg);
            }
        }
    }

    fn update_register_cache_and_stack(
        &mut self,
        vars: &Vec<ASMVar>,
        live_variables: &Vec<usize>,
        stack_offset: &mut isize,
        instr_index: InstrIndex,
    ) {
        for var_id in live_variables {
            let alloc_place = vars[*var_id].get_alloc_place(instr_index);
            match alloc_place {
                AllocPlace::Register(register) => {
                    self.register_to_var.insert(register.clone(), *var_id);
                    self.var_to_register.insert(*var_id, register.clone());
                }
                AllocPlace::Stack(offset) => {
                    if offset < *stack_offset {
                        *stack_offset = offset;
                    }
                }
                _ => {}
            }
        }
    }

    fn get_free_registers(&self, ty: &Type, exclude_regs: &Vec<Register>) -> Vec<Register> {
        let mut list = vec![];

        let reg_ty = get_reg_ty(ty);

        for reg in &self.possible_registers {
            if !self.register_to_var.contains_key(reg) {
                if exclude_regs.contains(reg) {
                    continue;
                }
                if reg.ty == reg_ty {
                    list.push(reg.clone());
                }
            }
        }

        list
    }

    fn get_free_register(&self, ty: &Type) -> Option<Register> {
        let reg_ty = get_reg_ty(ty);

        for reg in &self.possible_registers {
            if !self.register_to_var.contains_key(reg) {
                if reg.ty == reg_ty {
                    return Some(reg.clone());
                }
            }
        }

        return None;
    }

    fn alloc_variable_or_get_stack_offset(
        &mut self,
        vars: &mut Vec<ASMVar>,
        var_id: usize,
        stack_offset: &mut isize,
        instr_index: InstrIndex,
        exclude_regs: &Vec<Register>,
    ) -> Option<AllocPlace> {
        let var = &mut vars[var_id];
        let alloc_place = var.get_alloc_place(instr_index);

        match alloc_place {
            AllocPlace::Unallocated => {
                let free_place = self.find_free_alloc_place(&var.ty, stack_offset, exclude_regs);

                match free_place {
                    AllocPlace::Register(reg) => {
                        // Update register cache
                        self.var_to_register.insert(var_id, reg.clone());
                        self.register_to_var.insert(reg.clone(), var_id);
                        var.allocated_to.push((instr_index, free_place.clone()));
                    }
                    AllocPlace::Stack(offset) => {}
                    _ => unreachable!(),
                }
                return Some(free_place);
            }
            alloc_place @ AllocPlace::Stack(offset) => return Some(alloc_place),
            _ => return None,
        }
    }

    fn find_free_alloc_place(
        &mut self,
        ty: &Type,
        stack_offset: &mut isize,
        exclude_regs: &Vec<Register>,
    ) -> AllocPlace {
        let free_registers = self.get_free_registers(ty, exclude_regs);
        if free_registers.len() > 1 {
            return AllocPlace::Register(free_registers[0]);
        }

        // Return spill slot
        let var_size = ty.size() as isize;
        *stack_offset -= var_size;

        return AllocPlace::Stack(*stack_offset);
    }

    pub fn spill(
        &mut self,
        vars: &mut Vec<ASMVar>,
        var_id: usize,
        instr_index: InstrIndex,
        stack_offset: isize,
        instrs: &mut Vec<(usize, ASMInstr)>,
    ) {
        let var = &mut vars[var_id];

        let spill_reg = self.get_free_register(&var.ty).expect("No spill regs");

        var.allocated_to
            .push((instr_index, AllocPlace::Register(spill_reg.clone())));

        let mut next_instr_index = instr_index.clone();
        next_instr_index.instr_idx += 1;
        var.allocated_to
            .push((next_instr_index, AllocPlace::Stack(stack_offset)));

        let instr = "str".to_string();
        let args = vec![
            ASMValue::Register(spill_reg),
            ASMValue::Address(IRAddress {
                addr: IRAddressType::Register("fp".to_string()),
                stored_data_type: var.ty.clone(),
                offset: IRAddressOffset::Literal(stack_offset),
                increment: None,
            }),
        ];

        instrs.push((
            instr_index.instr_idx,
            ASMInstr::Instr {
                instr: instr,
                args: args,
            },
        ));
    }

    pub fn reload(
        &mut self,
        vars: &mut Vec<ASMVar>,
        var_id: usize,
        instr_index: InstrIndex,
        stack_offset: isize,
        instrs: &mut Vec<(usize, ASMInstr)>,
    ) {
        let var = &mut vars[var_id];

        let spill_reg = self.get_free_register(&var.ty).expect("No spill regs");

        var.allocated_to
            .push((instr_index, AllocPlace::Register(spill_reg)));

        self.register_to_var.insert(spill_reg.clone(), var_id);
        self.var_to_register.insert(var_id, spill_reg.clone());

        let instr = "ldr".to_string();
        let args = vec![
            ASMValue::Register(spill_reg),
            ASMValue::Address(IRAddress {
                addr: IRAddressType::Register("fp".to_string()),
                stored_data_type: var.ty.clone(),
                offset: IRAddressOffset::Literal(stack_offset),
                increment: None,
            }),
        ];

        instrs.push((
            instr_index.instr_idx,
            ASMInstr::Instr {
                instr: instr,
                args: args,
            },
        ));
    }

    pub fn allocate_registers(&mut self, asm_ir: &mut ASMIR) {
        let ASMIR {
            blocks,
            vars,
            var_lifespans,
        } = asm_ir;

        for (block_idx, block) in blocks.iter_mut().enumerate() {
            let mut stack_offset = 0;

            let old_instrs = std::mem::take(&mut block.instructions);
            block.instructions = Vec::with_capacity(old_instrs.len());
            let mut new_instrs = Vec::with_capacity(old_instrs.len());

            for (instr_idx, instr) in old_instrs {
                // not sure this is true vv
                // Cant use index based on old_instrs as this process can create new instructions so we settle on the last instruction in new_instrs
                // let instr_idx = new_instrs.len();

                let instr_index = InstrIndex {
                    block_idx,
                    instr_idx,
                };

                let live_vars = asm_ir.var_lifespans.get_live_vars(instr_index);
                self.mark_registers_storing_dead_values_as_free(&live_vars);
                self.update_register_cache_and_stack(
                    vars,
                    &live_vars,
                    &mut stack_offset,
                    instr_index,
                );

                match instr {
                    ASMInstr::InlineAsm(parts, clobbered, _) => {
                        // save and restore registers if they were in use earlier
                        // let mut registers_to_reload = vec![];
                        let mut saved_vars = HashMap::new();

                        let regs = self.register_to_var.clone();

                        let exclude_regs = self
                            .possible_registers
                            .iter()
                            .filter(|reg| clobbered.contains(&format!("{reg}")))
                            .cloned()
                            .collect::<Vec<_>>();

                        for (reg, var_id) in regs {
                            if clobbered.contains(&format!("{reg}")) {
                                let instr_set = get_instruction_set_reg(&reg.ty);
                                let mov = instr_set["mov"];

                                let var = &mut vars[var_id];

                                let free_place = self.find_free_alloc_place(
                                    &var.ty,
                                    &mut stack_offset,
                                    &exclude_regs,
                                );

                                // idk
                                self.register_to_var.remove(&reg);

                                match free_place {
                                    AllocPlace::Register(new_register) => {
                                        var.allocated_to.push((
                                            instr_index,
                                            AllocPlace::Register(new_register.clone()),
                                        ));

                                        self.register_to_var.insert(new_register.clone(), var_id);
                                        self.var_to_register.insert(var_id, new_register.clone());

                                        new_instrs.push((
                                            instr_idx,
                                            ASMInstr::Instr {
                                                instr: mov.to_string(),
                                                args: vec![
                                                    ASMValue::Register(new_register),
                                                    ASMValue::Register(reg.clone()),
                                                ],
                                            },
                                        ));
                                    }
                                    AllocPlace::Stack(offset) => {
                                        self.spill(
                                            vars,
                                            var_id,
                                            instr_index,
                                            offset,
                                            &mut new_instrs,
                                        );
                                    }
                                    _ => unreachable!(),
                                }
                            }
                        }

                        new_instrs
                            .push((instr_idx, ASMInstr::InlineAsm(parts, clobbered, saved_vars)));

                        // for (reg, var, temp_place) in registers_to_reload {
                        //     vars[var]
                        //         .allocated_to
                        //         .push((instr_index, AllocPlace::Register(reg)));
                        //     match temp_place {
                        //         AllocPlace::Register(temp_reg) => {
                        //             let instr_set = get_instruction_set_reg(&reg.ty);
                        //             let mov = instr_set["mov"];

                        //             new_instrs.push((
                        //                 instr_idx,
                        //                 ASMInstr::Instr {
                        //                     instr: mov.to_string(),
                        //                     args: vec![
                        //                         ASMValue::Register(reg.clone()),
                        //                         ASMValue::Register(temp_reg),
                        //                     ],
                        //                 },
                        //             ));

                        //             self.register_to_var.remove(&temp_reg);

                        //             self.register_to_var.insert(reg.clone(), var);
                        //             self.var_to_register.insert(var, reg.clone());
                        //         }
                        //         AllocPlace::Stack(offset) => {
                        //             // hacky
                        //             let ty = match reg.ty {
                        //                 RegisterType::General => Type::Int,
                        //                 RegisterType::Float32 => Type::Float,
                        //             };

                        //             new_instrs.push((
                        //                 instr_idx,
                        //                 ASMInstr::Instr {
                        //                     instr: "ldr".to_string(),
                        //                     args: vec![
                        //                         ASMValue::Register(reg.clone()),
                        //                         ASMValue::Address(IRAddress {
                        //                             addr: IRAddressType::Register("fp".to_string()),
                        //                             offset: IRAddressOffset::Literal(offset),
                        //                             stored_data_type: ty,
                        //                             increment: None,
                        //                         }),
                        //                     ],
                        //                 },
                        //             ));

                        //             self.register_to_var.insert(reg.clone(), var);
                        //             self.var_to_register.insert(var, reg.clone());
                        //         }
                        //         AllocPlace::Unallocated => unreachable!(),
                        //     }
                        // }
                    }
                    ASMInstr::Instr { instr, args } => {
                        if instr == "bl" {
                            // need to save volatile registers if used,
                            // x0-x15
                            // d0-d7

                            let general_regs = (0..=15)
                                .map(|num| Register {
                                    num,
                                    ty: RegisterType::General,
                                })
                                .collect::<Vec<_>>();

                            let mut float_regs = (0..=7)
                                .map(|num| Register {
                                    num,
                                    ty: RegisterType::Float32,
                                })
                                .collect::<Vec<_>>();

                            let mut volatile_registers = general_regs;
                            volatile_registers.append(&mut float_regs);
                        }

                        let mut spill_store = None;

                        for (arg_idx, arg) in args.iter().enumerate() {
                            match arg {
                                ASMValue::ArbitraryString(_) => {}
                                ASMValue::Label(_) => {}
                                ASMValue::Address(addr) => {
                                    if let IRAddressType::Register(reg) = &addr.addr {
                                        if *reg == "fp".to_string() {
                                            if let IRAddressOffset::Literal(offset) = &addr.offset {
                                                if *offset < stack_offset {
                                                    stack_offset = *offset
                                                }
                                            }
                                        }
                                    }
                                }
                                ASMValue::Literal(_) => {}
                                ASMValue::Register(register) => {}
                                ASMValue::Variable(var_id) => {
                                    //..

                                    let maybe_stack_offset = self
                                        .alloc_variable_or_get_stack_offset(
                                            vars,
                                            *var_id,
                                            &mut stack_offset,
                                            instr_index,
                                            &vec![],
                                        );

                                    if let Some(stack_offset) = maybe_stack_offset {
                                        match stack_offset {
                                            AllocPlace::Register(_) => {}
                                            AllocPlace::Stack(offset) => {
                                                if arg_idx == 0 {
                                                    // Trigger spill
                                                    // spill the result
                                                    spill_store = Some((var_id, offset));
                                                } else {
                                                    // Trigger load
                                                    self.reload(
                                                        vars,
                                                        *var_id,
                                                        instr_index,
                                                        offset,
                                                        &mut new_instrs,
                                                    );
                                                }
                                            }
                                            _ => unreachable!(),
                                        }
                                    }
                                }
                            }
                        }

                        new_instrs.push((
                            instr_idx,
                            ASMInstr::Instr {
                                instr: instr.clone(),
                                args: args.clone(),
                            },
                        ));

                        if let Some((var_id, stack_offset)) = spill_store {
                            self.spill(vars, *var_id, instr_index, stack_offset, &mut new_instrs);
                        }

                        if instr == "bl" {
                            // Restore registers
                        }
                    }
                }
            }

            block.instructions = new_instrs;
        }
    }
}
