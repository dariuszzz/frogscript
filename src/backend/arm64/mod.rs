use crate::{
    ast::{BinaryOperation, UnaryOp, UnaryOperation},
    backend::ssa_ir::{self, IRData, IRDataLiteral, IRValue, IRVariable, InlineTargetPart, SSAIR},
    lexer::Literal,
    symbol_table::{self, SymbolTable},
};
use ssa_ir::IRInstr;
use std::{collections::HashMap, fmt::Write, thread::current};

#[derive(Debug)]
pub struct ARM64Backend {
    ssa_ir: SSAIR,
    used_registers: HashMap<usize, String>, // ir_var -> register
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
                self.used_registers.get(var_id).unwrap_or(var_name).clone()
            }
            IRValue::Literal(lit) => match lit {
                Literal::Int(num) => format!("{num}"),
                Literal::Uint(num) => format!("{num}"),
                Literal::Boolean(true) => format!("1"),
                Literal::Boolean(false) => format!("0"),
                Literal::Float(num) => unimplemented!("needs to be in the data section lol"),
                Literal::String(num) => unimplemented!("needs to be in the data section lol"),
            },
        }
    }

    // probably change to lru before implementing graph coloring
    pub fn alloc_register_var(&mut self, ir_var: usize) -> String {
        let register = format!("x{}", self.register_counter);
        self.register_counter += 1;
        self.used_registers.insert(ir_var, register.clone());
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
        for block in blocks.iter().rev() {
            write!(out, "{}:\n", block.name).unwrap();

            for instr in &block.instructions {
                match instr {
                    IRInstr::InlineTarget(parts, used_registers) => {
                        let mut registers_to_restore = Vec::new();
                        let currently_used_registers = self.used_registers.clone();
                        for reg in used_registers {
                            for (var_id, current_reg) in &currently_used_registers {
                                // register is not empty
                                if current_reg == reg {
                                    // move to new register
                                    self.used_registers.remove(var_id);
                                    let register = self.alloc_register_var(*var_id);
                                    write!(out, "\tmov {register}, {current_reg}\n").unwrap();
                                    registers_to_restore.push((*var_id, current_reg.clone()))
                                }
                            }
                        }

                        let mut str = String::new();
                        for part in parts {
                            match part {
                                InlineTargetPart::String(text) => str += text,
                                InlineTargetPart::SSA_IR_Var_Ref(var_id) => {
                                    let reg = self
                                        .used_registers
                                        .get(var_id)
                                        // Todo: give better error msg
                                        .expect("Variable not allocated in any register");

                                    str += reg;
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
                        let ir_var_str = self.ir_value_to_asm(&val);
                        let register = self.alloc_register_var(*var);
                        write!(out, "\tmov {register}, {ir_var_str}\n").unwrap();
                    }
                    IRInstr::Return(val) => {
                        let ir_var_str = self.ir_value_to_asm(&val);
                        write!(out, "\tmov x0, {ir_var_str}\n\tret\n").unwrap();
                    }
                    IRInstr::Call(ret, called, args) => {
                        // Todo: pass in the arguments
                        let called_asm = self.ir_value_to_asm(&called);
                        write!(out, "\tbl {called_asm}\n").unwrap();
                        self.used_registers.insert(*ret, "x0".to_string());
                    }
                    IRInstr::BinOp(res, lhs, rhs, op) => {
                        let register = self.alloc_register_var(*res);
                        let rhs_str = self.ir_value_to_asm(&rhs);
                        let lhs_str = self.ir_value_to_asm(&lhs);

                        match op {
                            BinaryOperation::Add => {
                                write!(out, "\tadd {register}, {lhs_str}, {rhs_str}\n").unwrap();
                            }
                            BinaryOperation::Subtract => {
                                write!(out, "\tsub {register}, {lhs_str}, {rhs_str}\n").unwrap();
                            }
                            BinaryOperation::Multiply => {
                                write!(out, "\tmov {register}, {rhs_str}\n").unwrap();
                                write!(out, "\tmul {register}, {lhs_str}, {register}\n").unwrap();
                            }
                            _ => unimplemented!(),
                        }
                    }
                    IRInstr::UnOp(res, operand, op) => {
                        let register = self.alloc_register_var(*res);
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
                        let register = self.alloc_register_var(*res);
                        let addr = &addr.addr;

                        write!(out, "\tadrp {register}, {addr}@PAGE\n").unwrap();
                        write!(out, "\tadd {register}, {register}, {addr}@PAGEOFF\n").unwrap();
                    }
                    instr => {
                        println!("{instr:?}");
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
                write!(out, "\t{}: {data_ty} {data_val}\n", data.alias).unwrap();
            }
        }

        Ok(out)
    }
}
