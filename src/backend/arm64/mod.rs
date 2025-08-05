use crate::{
    ast::{BinaryOperation, UnaryOp, UnaryOperation},
    backend::ssa_ir::{self, IRValue, IRVariable, InlineTargetPart, SSAIR},
    lexer::Literal,
    symbol_table::{self, SymbolTable},
};
use ssa_ir::IRInstr;
use std::{collections::HashMap, fmt::Write};

#[derive(Debug)]
pub struct ARM64Backend {
    ir_vars: Vec<IRVariable>,
    used_registers: HashMap<usize, String>, // ir_var -> register
    register_counter: usize,
}

impl ARM64Backend {
    pub fn new(ir_vars: Vec<IRVariable>) -> Self {
        Self {
            ir_vars,
            used_registers: HashMap::new(),
            register_counter: 1,
        }
    }

    pub fn ir_value_to_asm(&self, ssa_ir: &SSAIR, ir_value: &IRValue) -> String {
        match ir_value {
            IRValue::Address(addr) => todo!("idk"),
            IRValue::Variable(var_id) => {
                let var_name = &self.ir_vars[*var_id].name;
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

    pub fn alloc_register_var(&mut self, ir_var: usize) -> String {
        let register = format!("x{}", self.register_counter);
        self.register_counter += 1;
        self.used_registers.insert(ir_var, register.clone());
        return register;
    }

    pub fn compile_ir(
        &mut self,
        ssa_ir: SSAIR,
        symbol_table: &SymbolTable,
    ) -> Result<String, String> {
        let mut out = r#"
.globl _main

_main:
"#
        .to_string();

        for block in ssa_ir.blocks.iter().rev() {
            write!(out, "{}:\n", block.name).unwrap();

            for instr in &block.instructions {
                write!(out, "\t").unwrap();
                match instr {
                    IRInstr::InlineTarget(parts) => {
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
                        write!(out, "{str}\n").unwrap();
                    }
                    IRInstr::Assign(var, val) => {
                        let ir_var_str = self.ir_value_to_asm(&ssa_ir, &val);
                        let register = self.alloc_register_var(*var);
                        write!(out, "mov {register}, {ir_var_str}\n").unwrap();
                    }
                    IRInstr::Return(val) => {
                        let ir_var_str = self.ir_value_to_asm(&ssa_ir, &val);
                        write!(out, "mov x0, {ir_var_str}\n\tret\n").unwrap();
                    }
                    IRInstr::Call(ret, called, args) => {
                        // Todo: pass in the arguments
                        let called_asm = self.ir_value_to_asm(&ssa_ir, &called);
                        write!(out, "bl {called_asm}\n").unwrap();
                        self.used_registers.insert(*ret, "x0".to_string());
                    }
                    IRInstr::BinOp(res, lhs, rhs, op) => {
                        let register = self.alloc_register_var(*res);
                        let rhs_str = self.ir_value_to_asm(&ssa_ir, &rhs);
                        let lhs_str = self.ir_value_to_asm(&ssa_ir, &lhs);

                        match op {
                            BinaryOperation::Add => {
                                write!(out, "add {register}, {lhs_str}, {rhs_str}\n").unwrap();
                            }
                            BinaryOperation::Subtract => {
                                write!(out, "sub {register}, {lhs_str}, {rhs_str}\n").unwrap();
                            }
                            BinaryOperation::Multiply => {
                                write!(out, "mov {register}, {rhs_str}\n").unwrap();
                                write!(out, "\tmul {register}, {lhs_str}, {register}\n").unwrap();
                            }
                            _ => unimplemented!(),
                        }
                    }
                    IRInstr::UnOp(res, operand, op) => {
                        let register1 = self.alloc_register_var(*res);
                        let ir_var_str = self.ir_value_to_asm(&ssa_ir, &operand);

                        match op {
                            UnaryOperation::Negate => {
                                if let IRValue::Literal(Literal::Boolean(boolean)) = operand {
                                    if *boolean {
                                        write!(out, "mov {register1}, 0\n").unwrap();
                                    } else {
                                        write!(out, "mov {register1}, 1\n").unwrap();
                                    }
                                }
                            }
                            UnaryOperation::Negative => {
                                // be smarter with registers
                                write!(out, "mov {register1}, {ir_var_str}\n").unwrap();
                                write!(out, "\tneg {register1}, {register1}\n").unwrap();
                            }
                            _ => unimplemented!(),
                        }
                    }
                    instr => {
                        println!("{instr:?}");
                        write!(out, "\n").unwrap();
                    }
                }
            }
        }

        Ok(out)
    }
}
