use std::{collections::HashMap, fmt::Display};

use crate::{BinaryOp, BinaryOperation, Literal, Type, UnaryOperation, Variable};

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

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct BlockParameter {
    pub name: String,
    pub ty: Type,
}

#[derive(Debug, Clone)]
pub struct Block {
    pub name: String,
    pub parameters: Vec<BlockParameter>,
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
pub struct IRVariable {
    pub name: String,
    pub ty: Type,
}

#[derive(Debug, Clone, PartialEq)]
pub enum IRValue {
    Literal(Literal),
    Variable(IRVariable),
}

impl IRValue {
    pub fn ty(&self) -> Type {
        match self {
            IRValue::Variable(v) => v.ty.clone(),
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
    Assign(String, IRValue),
    BinOp(String, IRValue, IRValue, BinaryOperation),
    UnOp(String, IRValue, UnaryOperation),
    Call(String, IRValue, Vec<IRValue>),
    If(IRValue, String, Vec<IRValue>, String, Vec<IRValue>),
    Goto(String, Vec<IRValue>),
    Return(IRValue),
    Label(String),

    Unimplemented(String, String),
}

impl Display for SSAIR {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for block in &self.blocks {
            f.write_fmt(format_args!("{block}\n"));
        }

        Ok(())
    }
}

impl Display for Block {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let params = self
            .parameters
            .iter()
            .map(|param| format!("{}: {}", param.name, param.ty))
            .collect::<Vec<_>>();
        let params = params.join(", ");

        f.write_fmt(format_args!("{}({}):\n", self.name, params));
        for instr in &self.instructions {
            f.write_fmt(format_args!("\t{instr}\n"));
        }

        Ok(())
    }
}

impl Display for IRInstr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IRInstr::Assign(var, irvalue) => f.write_fmt(format_args!("{var} = {irvalue}")),
            IRInstr::BinOp(var, irvalue, irvalue1, op) => {
                f.write_fmt(format_args!("{var} = {irvalue} {op} {irvalue1}"))
            }
            IRInstr::UnOp(var, irvalue, op) => f.write_fmt(format_args!("{var} = {op}{irvalue}")),
            IRInstr::Call(var, func, vec) => {
                let params = vec
                    .iter()
                    .map(|param| format!("{param}"))
                    .collect::<Vec<_>>();
                let params = params.join(", ");

                f.write_fmt(format_args!("{var} = call {func}({params})"))
            }
            IRInstr::Return(val) => f.write_fmt(format_args!("ret {val}")),
            IRInstr::Label(label) => f.write_fmt(format_args!("LABEL {label}")),
            IRInstr::Goto(label, args) => {
                let args = args
                    .iter()
                    .map(|param| format!("{param}"))
                    .collect::<Vec<_>>();
                let args = args.join(", ");

                f.write_fmt(format_args!("goto {label}({args})"))
            }
            IRInstr::If(val, true_label, true_args, false_label, false_args) => {
                let true_args = true_args
                    .iter()
                    .map(|param| format!("{param}"))
                    .collect::<Vec<_>>();
                let true_args = true_args.join(", ");

                let false_args = false_args
                    .iter()
                    .map(|param| format!("{param}"))
                    .collect::<Vec<_>>();
                let false_args = false_args.join(", ");

                f.write_fmt(format_args!(
                    "if {val} goto {true_label}({true_args}) else goto {false_label}({false_args})"
                ))
            }

            IRInstr::Unimplemented(var, str) => f.write_fmt(format_args!("{var} = [[{str}]]")),
        }
    }
}

impl Display for IRValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IRValue::Literal(literal) => f.write_fmt(format_args!("{literal:?}")),
            IRValue::Variable(variable) => {
                // f.write_fmt(format_args!("{}: {}", variable.name, variable.ty))
                f.write_fmt(format_args!("{}", variable.name))
            }
        }
    }
}
