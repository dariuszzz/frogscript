use std::{collections::HashMap, fmt::Display};

use crate::{BinaryOp, BinaryOperation, Literal, Type, UnaryOperation, Variable};

use super::ir_gen::IRGen;

#[derive(Debug, Clone)]
pub struct SSAIR {
    pub blocks: Vec<Block>,
}

impl Default for SSAIR {
    fn default() -> Self {
        Self {
            blocks: Vec::default(),
        }
    }
}

pub type VariableID = usize;

#[derive(Debug, Clone)]
pub struct Block {
    pub name: String,
    pub parameters: Vec<VariableID>,
    pub instructions: Vec<IRInstr>,
}

impl Default for Block {
    fn default() -> Self {
        Self {
            name: String::new(),
            parameters: Vec::new(),
            instructions: Vec::new(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct IRAddress {
    pub addr: String,
    pub offset: isize,
}

#[derive(Debug, Clone, PartialEq)]
pub struct IRVariable {
    pub name: String,
    pub ty: Type,
}

#[derive(Debug, Clone, PartialEq)]
pub enum IRValue {
    Literal(Literal),
    Variable(VariableID),
    Address(IRAddress),
}

impl IRValue {
    pub fn ty(&self) -> Type {
        match self {
            // idk
            IRValue::Address(v) => Type::Uint,
            IRValue::Variable(v) => Type::Infer,
            IRValue::Literal(lit) => match lit {
                Literal::String(_) => Type::String,
                Literal::Int(_) => Type::Int,
                Literal::Uint(_) => Type::Uint,
                Literal::Float(_) => Type::Float,
                Literal::Boolean(_) => Type::Boolean,
            },
        }
    }
}

#[derive(Debug, Clone)]
pub enum IRInstr {
    Assign(VariableID, IRValue),
    BinOp(VariableID, IRValue, IRValue, BinaryOperation),
    UnOp(VariableID, IRValue, UnaryOperation),
    Call(VariableID, IRValue, Vec<IRValue>),
    If(IRValue, String, Vec<IRValue>, String, Vec<IRValue>),
    Goto(String, Vec<IRValue>),

    Store(IRAddress, IRValue),
    Load(VariableID, IRAddress),

    Return(IRValue),
    Label(String),

    InlineTarget(String),

    Unimplemented(VariableID, String),
}

impl IRGen {
    pub fn pretty_print_address(&self, addr: &IRAddress) -> String {
        if addr.offset == 0 {
            format!("[{}]", addr.addr)
        } else if addr.offset > 0 {
            format!("[{}+{}]", addr.addr, addr.offset)
        } else {
            format!("[{}-{}]", addr.addr, addr.offset)
        }
    }

    pub fn pretty_print_irval(&self, irval: &IRValue) -> String {
        match irval {
            IRValue::Address(address) => self.pretty_print_address(address),
            IRValue::Literal(literal) => format!("{literal:?}"),
            IRValue::Variable(variable) => {
                let var = &self.vars[*variable];

                format!("{}", var.name)
            }
        }
    }

    pub fn pretty_print_instr(&self, instr: &IRInstr) -> String {
        match instr {
            IRInstr::Store(addr, val) => {
                let addr = self.pretty_print_address(addr);
                let val = self.pretty_print_irval(val);
                format!("store {addr} {val}")
            }
            IRInstr::Load(var, addr) => {
                let addr = self.pretty_print_address(addr);
                let var = &self.vars[*var];
                format!("{} = load {addr}", var.name)
            }
            IRInstr::Assign(var, irvalue) => {
                let irvalue = self.pretty_print_irval(irvalue);
                let var = &self.vars[*var];
                format!("{} = {irvalue}", var.name)
            }
            IRInstr::BinOp(var, irvalue, irvalue1, op) => {
                let irvalue = self.pretty_print_irval(irvalue);
                let irvalue1 = self.pretty_print_irval(irvalue1);
                let var = &self.vars[*var];
                format!("{} = {irvalue} {op} {irvalue1}", var.name)
            }
            IRInstr::UnOp(var, irvalue, op) => {
                let irvalue = self.pretty_print_irval(irvalue);
                let var = &self.vars[*var];
                format!("{} = {op}{irvalue}", var.name)
            }
            IRInstr::Call(var, func, vec) => {
                let params = vec
                    .iter()
                    .map(|param| self.pretty_print_irval(param))
                    .collect::<Vec<_>>();
                let params = params.join(", ");

                let func = self.pretty_print_irval(func);
                let var = &self.vars[*var];
                format!("{} = call {func}({params})", var.name)
            }
            IRInstr::Return(val) => {
                let val = self.pretty_print_irval(val);
                format!("ret {val}")
            }
            IRInstr::Label(label) => format!("LABEL {label}"),
            IRInstr::Goto(label, args) => {
                let args = args
                    .iter()
                    .map(|param| self.pretty_print_irval(param))
                    .collect::<Vec<_>>();
                let args = args.join(", ");

                format!("goto {label}({args})")
            }
            IRInstr::If(val, true_label, true_args, false_label, false_args) => {
                let true_args = true_args
                    .iter()
                    .map(|param| self.pretty_print_irval(param))
                    .collect::<Vec<_>>();
                let true_args = true_args.join(", ");

                let false_args = false_args
                    .iter()
                    .map(|param| self.pretty_print_irval(param))
                    .collect::<Vec<_>>();
                let false_args = false_args.join(", ");

                let val = self.pretty_print_irval(val);
                format!(
                    "if {val} goto {true_label}({true_args}) else goto {false_label}({false_args})"
                )
            }
            IRInstr::InlineTarget(instr) => {
                format!("Inline ({instr})")
            }

            IRInstr::Unimplemented(var, str) => {
                let var = &self.vars[*var];
                format!("{} = [[{str}]]", var.name)
            }
        }
    }

    pub fn pretty_print_ssa(&self, ssa: &SSAIR) {
        for block in &ssa.blocks {
            let params = block
                .parameters
                .iter()
                .map(|param| {
                    let param = &self.vars[*param];
                    format!("{}: {}", param.name, param.ty)
                })
                .collect::<Vec<_>>();
            let params = params.join(", ");

            println!("\n{}({}):", block.name, params);
            for instr in &block.instructions {
                let instr = self.pretty_print_instr(instr);
                println!("\t{instr}");
            }
        }
    }
}
