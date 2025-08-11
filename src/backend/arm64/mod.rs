use crate::{
    ast::{BinaryOp, BinaryOperation, Expression, Type, UnaryOp, UnaryOperation},
    backend::ssa_ir::{
        self, IRAddress, IRAddressOffset, IRAddressType, IRData, IRDataLiteral, IRValue,
        IRVariable, InlineTargetPart, SSAIR,
    },
    lexer::Literal,
    symbol_table::{self, SymbolTable},
};
use ssa_ir::IRInstr;
use std::{
    cell::OnceCell,
    collections::HashMap,
    fmt::Write,
    sync::{LazyLock, OnceLock},
    thread::current,
};

mod ssa_fix;

#[derive(Eq, PartialEq, Debug, Copy, Clone)]
pub enum RegisterType {
    General,
    Float32,
}

#[derive(Debug, Clone)]
pub struct Register {
    pub ty: RegisterType,
    pub num: usize,
}

impl std::fmt::Display for Register {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let prefix = match self.ty {
            RegisterType::Float32 => "s",
            RegisterType::General => "x",
        };

        f.write_fmt(format_args!("{prefix}{}", self.num))
    }
}

#[derive(Debug)]
pub struct ARM64Backend<'a> {
    ssa_ir: &'a mut SSAIR,
    register_counter: usize,
}

type StoredVariables = HashMap<usize, Register>;
type InstrSet = HashMap<&'static str, &'static str>;

static BASE_INSTR_SET: LazyLock<InstrSet> = LazyLock::new(|| {
    HashMap::from([
        ("mov", "mov"),
        ("add", "add"),
        ("sub", "sub"),
        ("mul", "mul"),
        ("neg", "neg"),
        ("cmp", "cmp"),
    ])
});

impl<'a> ARM64Backend<'a> {
    pub fn new(ssa_ir: &'a mut SSAIR) -> Self {
        Self {
            ssa_ir,
            register_counter: 1,
        }
    }

    pub fn offset_calc_asm(
        &mut self,
        used_registers: &StoredVariables,
        out: &mut String,
        addr: &IRAddress,
    ) -> String {
        let offset = match &addr.offset {
            IRAddressOffset::Literal(offset) => format!("#{offset}"),
            IRAddressOffset::IRVariable(offset_var) => {
                let register = used_registers.get(offset_var);

                if let Some(register) = register {
                    format!("{register}")
                } else {
                    let var_name = &self.ssa_ir.vars[*offset_var].name;
                    format!("`unalloc var {var_name}`")
                }
            }
        };

        match &addr.addr {
            IRAddressType::Data(addr) => unimplemented!("Need to figure this out"),
            IRAddressType::RawAddr(addr) => {
                unimplemented!("Will implement once it shows up somewhere")
            }
            IRAddressType::Register(addr) => {
                if offset == "0" {
                    format!("{addr}") // offset doesnt do anything for now
                } else {
                    // general register is fine here since its an address (uint)
                    let temp_reg = self.temp_register(RegisterType::General);
                    write!(out, "\tadd {temp_reg}, {addr}, {offset}\n").unwrap();
                    format!("{temp_reg}")
                }
            }
        }
    }

    pub fn ir_value_to_asm(
        &mut self,
        used_registers: &StoredVariables,
        out: &mut String,
        ir_value: &IRValue,
    ) -> String {
        match ir_value {
            IRValue::Address(addr) => self.offset_calc_asm(used_registers, out, addr),
            IRValue::Variable(var_id) => {
                let register = used_registers.get(var_id);
                if let Some(register) = register {
                    format!("{register}")
                } else {
                    let var_name = &self.ssa_ir.vars[*var_id].name;
                    format!("`unalloc var {var_name}`")
                    // unreachable!("variable is not in any register");
                }
            }
            IRValue::Literal(lit) => match lit {
                Literal::Int(num) => format!("#{num}"),
                Literal::Uint(num) => format!("#{num}"),
                Literal::Boolean(true) => format!("#1"),
                Literal::Boolean(false) => format!("#0"),
                Literal::Float(num) => unimplemented!("needs to be in the data section lol"),
                Literal::String(num) => unimplemented!("needs to be in the data section lol"),
            },
        }
    }

    // probably change to lru before implementing graph coloring
    pub fn get_free_or_existing_register(
        &mut self,
        used_registers: &mut StoredVariables,
        ir_var: usize,
    ) -> Register {
        let var_ty = self.get_var_type(ir_var);
        let (reg_type, _) = self.get_register_ty_and_instructions(&var_ty);

        if let Some(reg) = used_registers.get(&ir_var) {
            if reg.ty == reg_type {
                return reg.clone();
            }
        }

        let register = Register {
            ty: reg_type,
            num: self.register_counter,
        };
        self.register_counter += 1;
        used_registers.insert(ir_var, register.clone());
        return register;
    }

    pub fn temp_register(&mut self, ty: RegisterType) -> Register {
        let register = Register {
            ty,
            num: self.register_counter,
        };
        self.register_counter += 1;
        return register;
    }

    pub fn get_register_ty_and_instructions(&self, ty: &Type) -> (RegisterType, InstrSet) {
        let mut set = BASE_INSTR_SET.clone();
        let reg_ty = match &ty {
            Type::Float => {
                set.insert("mov", "fmov");
                set.insert("add", "fadd");
                set.insert("sub", "fsub");
                set.insert("mul", "fmul");
                set.insert("div", "fdiv");
                set.insert("neg", "fneg");
                set.insert("cmp", "fcmp");
                RegisterType::Float32
            }
            _ => RegisterType::General,
        };

        (reg_ty, set)
    }

    pub fn get_var_type(&self, var_id: usize) -> Type {
        self.ssa_ir.vars[var_id].ty.clone()
    }

    pub fn get_ir_value_type(&self, ir_val: &IRValue) -> Type {
        let ty = match ir_val {
            IRValue::Address(_) => unreachable!(), // i dont think this shows up
            IRValue::Literal(lit) => lit.ty().clone(),
            IRValue::Variable(var_id) => self.get_var_type(*var_id),
        };

        ty.clone()
    }

    pub fn format_addr_offset(
        &self,
        used_registers: &StoredVariables,
        offset: &IRAddressOffset,
    ) -> String {
        match &offset {
            IRAddressOffset::Literal(offset) => format!("#{offset}"),
            IRAddressOffset::IRVariable(offset_var) => {
                let register = used_registers.get(offset_var);

                if let Some(register) = register {
                    format!("{register}")
                } else {
                    let var_name = &self.ssa_ir.vars[*offset_var].name;
                    format!("`unalloc var {var_name}`")
                }
            }
        }
    }

    pub fn format_addr(&self, used_registers: &StoredVariables, addr: &IRAddress) -> String {
        let offset = self.format_addr_offset(used_registers, &addr.offset);
        match &addr.addr {
            IRAddressType::Data(addr) => unimplemented!("FIX THIS"),
            IRAddressType::RawAddr(addr) => {
                unimplemented!("Will implement once it shows up somewhere")
            }
            IRAddressType::Register(addr) => {
                if offset == "0" {
                    format!("[{addr}]")
                } else {
                    format!("[{addr},{offset}]")
                }
            }
        }
    }

    pub fn compile_ir(&mut self, symbol_table: &SymbolTable) -> Result<String, String> {
        self.adjust_ssa_for_target(symbol_table);

        let mut out = ".text\n.globl _main\n".to_string();

        write!(out, "_main:\n").unwrap();
        let blocks = self.ssa_ir.blocks.clone();

        write!(out, "\tb {}\n", self.ssa_ir.entry_block).unwrap();

        let mut used_registers: StoredVariables = HashMap::new();

        for block in blocks.iter() {
            write!(out, "{}:\n", block.name).unwrap();

            if let Some(_) = block.func_name {
                used_registers.clear();
                // setup stack frame

                write!(out, "\tstp fp, lr, [sp,#-16]!\n").unwrap();
                write!(out, "\tmov fp, sp\n").unwrap();
                write!(out, "\tsub sp, sp, #16\n").unwrap();

                // need to save volatile registers if used,
                // x0-x15
                // d0-d7

                // todo: read off func params
                // FOR NOW:
                // alloc each parameter in a register

                // read them off from x0, ..., xn
                let mut arg_count = 0;
                if block.parameters.len() >= 8 {
                    unimplemented!("CANT PASS MORE THAN 8 PARAMS FOR NOW");
                }
                for arg_id in &block.parameters {
                    let arg_var = &self.ssa_ir.vars[*arg_id];

                    let (reg_type, instr_set) = self.get_register_ty_and_instructions(&arg_var.ty);

                    let dest_register = Register {
                        ty: reg_type,
                        num: arg_count,
                    };

                    let new_arg_reg =
                        self.get_free_or_existing_register(&mut used_registers, *arg_id);

                    let mov = instr_set["mov"];

                    write!(out, "\t{mov} {new_arg_reg}, {dest_register}\n").unwrap();
                    arg_count += 1;
                }
            }

            for instr in &block.instructions {
                match instr {
                    IRInstr::InlineTarget(parts, clobbered_registers) => {
                        let mut registers_to_restore = Vec::new();
                        let currently_used_registers = used_registers.clone();
                        for reg in clobbered_registers {
                            for (var_id, current_reg) in &currently_used_registers {
                                // register is not empty
                                if format!("{current_reg}") == *reg {
                                    // move to new register
                                    used_registers.remove(var_id);

                                    let register = self.get_free_or_existing_register(
                                        &mut used_registers,
                                        *var_id,
                                    );

                                    let var_ty = self.get_var_type(*var_id);
                                    let (_, instr_set) =
                                        self.get_register_ty_and_instructions(&var_ty);

                                    let mov = instr_set["mov"];

                                    write!(out, "\t{mov} {register}, {current_reg}\n").unwrap();
                                    registers_to_restore.push((*var_id, current_reg.clone()))
                                }
                            }
                        }

                        let mut str = String::new();
                        for part in parts {
                            match part {
                                InlineTargetPart::String(text) => str += text,
                                InlineTargetPart::SSAIRVarRef(var_id) => {
                                    let reg = used_registers
                                        .get(var_id)
                                        // Todo: give better error msg
                                        .expect("Variable not allocated in any register");

                                    str += &format!("{reg}");
                                }
                            }
                        }
                        write!(out, "\t{str}\n").unwrap();

                        // not sure if this is necessary since i am changing self.used_registers
                        for (var_id, reg) in registers_to_restore {
                            let temp_reg = used_registers.get(&var_id).unwrap().clone();
                            used_registers.remove(&var_id);
                            used_registers.insert(var_id, reg.clone());
                            write!(out, "\tmov {reg}, {temp_reg}\n").unwrap();
                        }
                    }

                    IRInstr::Assign(var, val) => {
                        let var_ty = self.get_var_type(*var);
                        let (_, instr_set) = self.get_register_ty_and_instructions(&var_ty);

                        let mov = instr_set["mov"];

                        let ir_var_str = self.ir_value_to_asm(&used_registers, &mut out, &val);

                        let register =
                            self.get_free_or_existing_register(&mut used_registers, *var);
                        write!(out, "\t{mov} {register}, {ir_var_str}\n").unwrap();
                    }
                    IRInstr::Return(val) => {
                        if let Some(val) = val {
                            let ir_var_str = self.ir_value_to_asm(&used_registers, &mut out, &val);
                            let var_ty = self.get_ir_value_type(val);
                            let (reg_ty, instr_set) =
                                self.get_register_ty_and_instructions(&var_ty);

                            let mov = instr_set["mov"];

                            let output_reg = Register { num: 0, ty: reg_ty };

                            // Put return value in x0/s0/d0 WHATEVER
                            write!(out, "\t{mov} {output_reg}, {ir_var_str}\n").unwrap();
                        }

                        // destroy stack frame and return
                        write!(out, "\tmov sp, fp\n").unwrap();
                        write!(out, "\tldp fp, lr, [sp], #16\n").unwrap();
                        write!(out, "\tret\n").unwrap();
                    }
                    IRInstr::Call(ret, called, args) => {
                        // Todo: pass in the arguments
                        let mut arg_count = 0;
                        for arg in args {
                            let arg_type = self.get_ir_value_type(arg);

                            let (reg_ty, instr_set) =
                                self.get_register_ty_and_instructions(&arg_type);

                            let register = Register {
                                ty: reg_ty,
                                num: arg_count,
                            };

                            let arg_asm = self.ir_value_to_asm(&used_registers, &mut out, arg);

                            let mov = instr_set["mov"];

                            write!(out, "\t{mov} {register}, {arg_asm}\n").unwrap();
                            arg_count += 1;
                        }

                        // let called_asm = self.ir_value_to_asm(&mut out, &called);
                        match called {
                            IRValue::Variable(var_id) => {
                                let label_name = &self.ssa_ir.vars[*var_id].name;
                                write!(out, "\tbl {label_name}\n").unwrap();
                                used_registers.insert(
                                    *ret,
                                    Register {
                                        ty: RegisterType::General,
                                        num: 0,
                                    },
                                );
                            }
                            _ => unimplemented!(),
                        }
                    }
                    IRInstr::BinOp(res, lhs, rhs, op) => {
                        let ty = self.get_var_type(*res);
                        let (reg_type, instr_set) = self.get_register_ty_and_instructions(&ty);

                        let mov = instr_set["mov"];
                        let add = instr_set["add"];
                        let sub = instr_set["sub"];
                        let mul = instr_set["mul"];
                        let cmp = instr_set["cmp"];

                        let mut lhs_str = self.ir_value_to_asm(&used_registers, &mut out, &lhs);
                        let mut rhs_str = self.ir_value_to_asm(&used_registers, &mut out, &rhs);

                        // eliminate the case where its `op lit reg` since its not allowed
                        if matches!(lhs, IRValue::Literal(_)) {
                            // turn it into `op reg lit`
                            let tmp = lhs_str;
                            lhs_str = rhs_str;
                            rhs_str = tmp;

                            // if its `op lit1 lit2` now then turn into
                            // `mov temp_reg lit1`
                            // `op temp_reg lit2`
                            // fixme: this is stupid sometimes i think
                            if matches!(rhs, IRValue::Literal(_)) {
                                let temp_reg = self.temp_register(reg_type);

                                write!(out, "\t{mov} {temp_reg}, {lhs_str}\n").unwrap();
                                lhs_str = format!("{temp_reg}");
                            }
                        }

                        let register =
                            self.get_free_or_existing_register(&mut used_registers, *res);

                        match op {
                            BinaryOperation::Add => {
                                write!(out, "\t{add} {register}, {lhs_str}, {rhs_str}\n").unwrap();
                            }
                            BinaryOperation::Subtract => {
                                write!(out, "\t{sub} {register}, {lhs_str}, {rhs_str}\n").unwrap();
                            }
                            BinaryOperation::Multiply => {
                                let temp_reg = self.temp_register(reg_type);

                                write!(out, "\t{mov} {temp_reg}, {rhs_str}\n").unwrap();
                                write!(out, "\t{mul} {register}, {lhs_str}, {temp_reg}\n").unwrap();
                            }
                            BinaryOperation::Divide => {
                                // Div is not a thing for non floats so this has to be here
                                let div = instr_set["div"];

                                write!(out, "\t{div} {register}, {lhs_str}, {rhs_str}\n").unwrap();
                            }
                            // idk
                            BinaryOperation::Equal
                            | BinaryOperation::NotEqual
                            | BinaryOperation::Greater
                            | BinaryOperation::GreaterEqual
                            | BinaryOperation::Less
                            | BinaryOperation::LessEqual => {
                                // This will only work correctly for ints and floats and maybe checking equality for addresses
                                write!(out, "\t{cmp} {lhs_str}, {rhs_str}\n").unwrap();
                            }
                            _ => unimplemented!(),
                        }
                    }
                    IRInstr::If(cond, irval, true_label, true_args, false_label, false_args) => {
                        match **cond {
                            Expression::BinaryOp(BinaryOp { op, .. }) => {
                                let true_instr = match op {
                                    BinaryOperation::NotEqual => "b.ne",
                                    BinaryOperation::Equal => "b.eq",
                                    BinaryOperation::Less => "b.lt",
                                    BinaryOperation::LessEqual => "b.le",
                                    BinaryOperation::Greater => "b.gt",
                                    BinaryOperation::GreaterEqual => "b.ge",
                                    _ => unreachable!("tf"),
                                };
                                write!(out, "\t{true_instr} {true_label}\n").unwrap();
                                write!(out, "\tb {false_label}\n").unwrap();
                            }
                            // FIXME: These probably shouldnt be hardcoded?
                            Expression::UnaryOp(UnaryOp { op, ref operand }) => match op {
                                UnaryOperation::Negate => match **operand {
                                    Expression::Literal(Literal::Boolean(boolean)) => {
                                        if !boolean {
                                            write!(out, "\tb {true_label}\n").unwrap();
                                        } else {
                                            write!(out, "\tb {false_label}\n").unwrap();
                                        }
                                    }
                                    _ => unimplemented!("co"),
                                },
                                _ => unimplemented!("co2"),
                            },
                            Expression::Literal(Literal::Boolean(boolean)) => {
                                if boolean {
                                    write!(out, "\tb {true_label}\n").unwrap();
                                } else {
                                    write!(out, "\tb {false_label}\n").unwrap();
                                }
                            }
                            ref cond => unimplemented!("{cond:?}"),
                        };
                    }
                    IRInstr::Goto(label, args) => {
                        write!(out, "\tb {label}\n").unwrap();
                    }
                    IRInstr::UnOp(res, operand, op) => {
                        let ty = self.get_var_type(*res);
                        let (_, instr_set) = self.get_register_ty_and_instructions(&ty);

                        let register =
                            self.get_free_or_existing_register(&mut used_registers, *res);

                        let ir_var_str = self.ir_value_to_asm(&used_registers, &mut out, &operand);

                        let mov = instr_set["mov"];
                        let neg = instr_set["neg"];

                        match op {
                            // TODO: Find a less `hardcoded` way
                            UnaryOperation::Negate => match operand {
                                IRValue::Literal(Literal::Boolean(boolean)) => {
                                    if *boolean {
                                        write!(out, "\t{mov} {register}, 0\n").unwrap();
                                    } else {
                                        write!(out, "\t{mov} {register}, 1\n").unwrap();
                                    }
                                }
                                _ => unimplemented!(),
                            },
                            UnaryOperation::Negative => {
                                // be smarter with registers
                                write!(out, "\t{mov} {register}, {ir_var_str}\n").unwrap();
                                write!(out, "\t{neg} {register}, {register}\n").unwrap();
                            }
                            _ => unimplemented!(),
                        }
                    }
                    IRInstr::Store(addr, ir_val) => {
                        let val_asm = self.ir_value_to_asm(&used_registers, &mut out, &ir_val);

                        let full_addr = self.format_addr(&used_registers, &addr);

                        let (reg_ty, instr_set) =
                            self.get_register_ty_and_instructions(&addr.stored_data_type);

                        let mov = instr_set["mov"];

                        // Can always be general since its an address
                        let temp_reg = self.temp_register(reg_ty);
                        write!(out, "\t{mov} {temp_reg}, {val_asm}\n").unwrap();
                        write!(out, "\tstr {temp_reg}, {full_addr}\n").unwrap();
                    }
                    IRInstr::Load(res, addr) => {
                        let offset = &addr.offset;

                        match &addr.addr {
                            IRAddressType::Data(addr) => {
                                let accessed_data = self
                                    .ssa_ir
                                    .data
                                    .iter()
                                    .filter(|d| d.alias == *addr)
                                    .next()
                                    .unwrap();

                                match &accessed_data.value {
                                    IRDataLiteral::String(_) => {
                                        let register = self.get_free_or_existing_register(
                                            &mut used_registers,
                                            *res,
                                        );
                                        write!(out, "\tadrp {register}, {addr}@PAGE\n").unwrap();
                                        write!(
                                            out,
                                            "\tadd {register}, {register}, {addr}@PAGEOFF\n"
                                        )
                                        .unwrap();
                                    }
                                    IRDataLiteral::Float(_) => {
                                        let temp_reg = self.temp_register(RegisterType::General);
                                        let register = self.get_free_or_existing_register(
                                            &mut used_registers,
                                            *res,
                                        );
                                        write!(out, "\tadrp {temp_reg}, {addr}@PAGE\n").unwrap();
                                        write!(
                                            out,
                                            "\tldr {register}, [{temp_reg}, {addr}@PAGEOFF]\n"
                                        )
                                        .unwrap();
                                    }
                                }
                            }
                            IRAddressType::Register(address) => {
                                let reg_type = match addr.stored_data_type {
                                    Type::Float => RegisterType::Float32,
                                    _ => RegisterType::General,
                                };

                                let register =
                                    self.get_free_or_existing_register(&mut used_registers, *res);

                                let offset = self.format_addr_offset(&used_registers, &offset);

                                let addr = if offset == "0" {
                                    format!("[{address}]")
                                } else {
                                    format!("[{address},{offset}]")
                                };

                                write!(out, "\tldr {register}, {addr}\n").unwrap();
                            }
                            IRAddressType::RawAddr(addr) => unimplemented!(),
                        }
                    }

                    instr => {
                        println!("whatt: {instr:?}");
                        write!(out, "\n").unwrap();
                    }
                }
            }
        }

        let data = self.ssa_ir.data.clone();
        // data.retain(|d| !matches!(d.value, IRDataLiteral::String(_)));

        if !data.is_empty() {
            write!(out, ".data\n").unwrap();
            for data in &data {
                let (data_ty, data_val) = match &data.value {
                    IRDataLiteral::Float(float) => (".float", format!("{float}")),
                    IRDataLiteral::String(str) => (".string", format!("\"{str}\"")),
                    _ => todo!(),
                };
                write!(out, ".balign 4\n{}: {data_ty} {data_val}\n", data.alias).unwrap();
            }
        }

        Ok(out)
    }
}
