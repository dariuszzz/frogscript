use crate::{
    ast::{BinaryOp, BinaryOperation, Expression, Type, UnaryOp, UnaryOperation},
    backend::ssa_ir::{self, IRData, IRDataLiteral, IRValue, IRVariable, InlineTargetPart, SSAIR},
    lexer::Literal,
    symbol_table::{self, SymbolTable},
};
use ssa_ir::IRInstr;
use std::{collections::HashMap, fmt::Write, thread::current};

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
pub struct ARM64Backend {
    ssa_ir: SSAIR,
    used_registers: HashMap<usize, Register>, // ir_var -> register
    register_counter: usize,
}

impl ARM64Backend {
    pub fn new(ssa_ir: SSAIR) -> Self {
        Self {
            ssa_ir,
            used_registers: HashMap::new(),
            register_counter: 1,
        }
    }

    pub fn ir_value_to_asm(&self, ir_value: &IRValue) -> String {
        match ir_value {
            IRValue::Address(addr) => todo!("idk"),
            IRValue::Variable(var_id) => {
                let var_name = &self.ssa_ir.vars[*var_id].name;
                let register = self.used_registers.get(var_id);
                if let Some(register) = register {
                    format!("{register}")
                } else {
                    var_name.clone()
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
    pub fn get_free_or_existing_register(&mut self, ty: RegisterType, ir_var: usize) -> Register {
        if let Some(reg) = self.used_registers.get(&ir_var) {
            if reg.ty == ty {
                return reg.clone();
            }
        }

        let register = Register {
            ty,
            num: self.register_counter,
        };
        self.register_counter += 1;
        self.used_registers.insert(ir_var, register.clone());
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

    pub fn compile_ir(&mut self, symbol_table: &SymbolTable) -> Result<String, String> {
        let mut out = ".text\n.globl _main\n".to_string();

        // let mut text = self.ssa_ir.data.clone();
        // text.retain(|d| matches!(d.value, IRDataLiteral::String(_)));

        // if !text.is_empty() {
        //     write!(out, ".text\n").unwrap();
        //     for text in &text {
        //         if let IRDataLiteral::String(str) = &text.value {
        //             let val = format!("\"{str}\"");
        //             write!(out, "\t{}: .string {val}\n", text.alias).unwrap();
        //         };
        //     }
        // }

        write!(out, "_main:\n").unwrap();
        let blocks = self.ssa_ir.blocks.clone();

        let main_block = &blocks.last().unwrap().name;
        write!(out, "\tb {}\n", self.ssa_ir.entry_block).unwrap();

        for block in blocks.iter() {
            write!(out, "{}:\n", block.name).unwrap();

            for instr in &block.instructions {
                match instr {
                    IRInstr::InlineTarget(parts, used_registers) => {
                        let mut registers_to_restore = Vec::new();
                        let currently_used_registers = self.used_registers.clone();
                        for reg in used_registers {
                            for (var_id, current_reg) in &currently_used_registers {
                                // register is not empty
                                if format!("{current_reg}") == *reg {
                                    // move to new register
                                    self.used_registers.remove(var_id);

                                    let register =
                                        self.get_free_or_existing_register(current_reg.ty, *var_id);
                                    write!(out, "\tmov {register}, {current_reg}\n").unwrap();
                                    registers_to_restore.push((*var_id, current_reg.clone()))
                                }
                            }
                        }

                        let mut str = String::new();
                        for part in parts {
                            match part {
                                InlineTargetPart::String(text) => str += text,
                                InlineTargetPart::SSAIRVarRef(var_id) => {
                                    let reg = self
                                        .used_registers
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
                            let temp_reg = self.used_registers.get(&var_id).unwrap().clone();
                            self.used_registers.remove(&var_id);
                            self.used_registers.insert(var_id, reg.clone());
                            write!(out, "\tmov {reg}, {temp_reg}\n").unwrap();
                        }
                    }

                    IRInstr::Assign(var, val) => {
                        let variable = &self.ssa_ir.vars[*var];
                        let (instr, reg_ty) = {
                            match variable.ty {
                                Type::Float => ("fmov", RegisterType::Float32),
                                _ => ("mov", RegisterType::General),
                            }
                        };

                        let ir_var_str = self.ir_value_to_asm(&val);
                        let register = self.get_free_or_existing_register(reg_ty, *var);
                        write!(out, "\t{instr} {register}, {ir_var_str}\n").unwrap();
                    }
                    IRInstr::Return(val) => {
                        let ir_var_str = self.ir_value_to_asm(&val);
                        write!(out, "\tmov x0, {ir_var_str}\n\tret\n").unwrap();
                    }
                    IRInstr::Call(ret, called, args) => {
                        // Todo: pass in the arguments
                        let called_asm = self.ir_value_to_asm(&called);
                        write!(out, "\tbl {called_asm}\n").unwrap();
                        self.used_registers.insert(
                            *ret,
                            Register {
                                ty: RegisterType::General,
                                num: 0,
                            },
                        );
                    }
                    IRInstr::BinOp(res, lhs, rhs, op) => {
                        let ty = self.ssa_ir.vars[*res].ty.clone();
                        let reg_type = match ty {
                            Type::Float => RegisterType::Float32,
                            _ => RegisterType::General,
                        };

                        let move_op = match reg_type {
                            RegisterType::Float32 => "fmov",
                            _ => "mov",
                        };

                        let mut lhs_str = self.ir_value_to_asm(&lhs);
                        let mut rhs_str = self.ir_value_to_asm(&rhs);

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

                                write!(out, "\t{move_op} {temp_reg}, {lhs_str}\n").unwrap();
                                lhs_str = format!("{temp_reg}");
                            }
                        }

                        match op {
                            BinaryOperation::Add => {
                                let op = match reg_type {
                                    RegisterType::Float32 => "fadd",
                                    _ => "add",
                                };
                                let register = self.get_free_or_existing_register(reg_type, *res);

                                write!(out, "\t{op} {register}, {lhs_str}, {rhs_str}\n").unwrap();
                            }
                            BinaryOperation::Subtract => {
                                let op = match reg_type {
                                    RegisterType::Float32 => "fsub",
                                    _ => "sub",
                                };
                                let register = self.get_free_or_existing_register(reg_type, *res);

                                write!(out, "\t{op} {register}, {lhs_str}, {rhs_str}\n").unwrap();
                            }
                            BinaryOperation::Multiply => {
                                let op = match reg_type {
                                    RegisterType::Float32 => "fmul",
                                    _ => "mul",
                                };
                                let register = self.get_free_or_existing_register(reg_type, *res);

                                write!(out, "\t{move_op} {register}, {rhs_str}\n").unwrap();
                                write!(out, "\t{op} {register}, {lhs_str}, {register}\n").unwrap();
                            }
                            BinaryOperation::Divide => {
                                let op = match reg_type {
                                    RegisterType::Float32 => "fdiv",
                                    _ => todo!("Figure out how to do non float division"),
                                };
                                let register = self.get_free_or_existing_register(reg_type, *res);

                                write!(out, "\t{op} {register}, {lhs_str}, {rhs_str}\n").unwrap();
                            }
                            // idk
                            BinaryOperation::Equal
                            | BinaryOperation::NotEqual
                            | BinaryOperation::Greater
                            | BinaryOperation::GreaterEqual
                            | BinaryOperation::Less
                            | BinaryOperation::LessEqual => {
                                let op = match ty {
                                    Type::Int => {
                                        write!(out, "\tcmp {lhs_str}, {rhs_str}\n").unwrap();
                                    }
                                    _ => todo!("Other comparisons not implented"),
                                };
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
                            _ => unimplemented!("Idk"),
                        };
                    }
                    IRInstr::Goto(label, args) => {
                        write!(out, "\tb {label}\n").unwrap();
                    }
                    IRInstr::UnOp(res, operand, op) => {
                        let register =
                            self.get_free_or_existing_register(RegisterType::General, *res);
                        let ir_var_str = self.ir_value_to_asm(&operand);

                        match op {
                            UnaryOperation::Negate => {
                                if let IRValue::Literal(Literal::Boolean(boolean)) = operand {
                                    if *boolean {
                                        write!(out, "\tmov {register}, 0\n").unwrap();
                                    } else {
                                        write!(out, "\tmov {register}, 1\n").unwrap();
                                    }
                                }
                            }
                            UnaryOperation::Negative => {
                                // be smarter with registers
                                write!(out, "\tmov {register}, {ir_var_str}\n").unwrap();
                                write!(out, "\tneg {register}, {register}\n").unwrap();
                            }
                            _ => unimplemented!(),
                        }
                    }
                    IRInstr::Load(res, addr) => {
                        let addr = &addr.addr;

                        let accessed_data = self
                            .ssa_ir
                            .data
                            .iter()
                            .filter(|d| d.alias == *addr)
                            .next()
                            .unwrap();

                        match &accessed_data.value {
                            IRDataLiteral::String(_) => {
                                let register =
                                    self.get_free_or_existing_register(RegisterType::General, *res);
                                write!(out, "\tadrp {register}, {addr}@PAGE\n").unwrap();
                                write!(out, "\tadd {register}, {register}, {addr}@PAGEOFF\n")
                                    .unwrap();
                            }
                            IRDataLiteral::Float(_) => {
                                let temp_reg = self.temp_register(RegisterType::General);
                                let register =
                                    self.get_free_or_existing_register(RegisterType::Float32, *res);
                                write!(out, "\tadrp {temp_reg}, {addr}@PAGE\n").unwrap();
                                write!(out, "\tldr {register}, [{temp_reg}, {addr}@PAGEOFF]\n")
                                    .unwrap();
                            }
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
