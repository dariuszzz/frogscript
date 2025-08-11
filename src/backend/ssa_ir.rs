use std::{collections::HashMap, fmt::Display};

use crate::{
    arena::Arena,
    ast::{Expression, SymbolIdx},
    backend::ir_gen::{CFGraph, CFGraphNode},
    BinaryOp, BinaryOperation, Literal, Type, UnaryOperation, Variable,
};

#[derive(Debug, Clone)]
pub struct SSAIR {
    pub vars: Vec<IRVariable>,
    pub blocks: Vec<Block>,
    pub data: Vec<IRData>,
    pub entry_block: String,
    pub stack_vars: HashMap<usize, IRAddress>,
    pub cf_graph: CFGraph,
}

impl Default for SSAIR {
    fn default() -> Self {
        Self {
            blocks: Vec::default(),
            vars: Vec::default(),
            data: Vec::default(),
            stack_vars: HashMap::default(),
            entry_block: "main".to_string(),
            cf_graph: CFGraph::default(),
        }
    }
}

pub type VariableID = usize;

#[derive(Debug, Clone)]
pub struct Block {
    pub func_name: Option<(SymbolIdx, String)>,
    pub name: String,
    pub parameters: Vec<VariableID>,
    pub instructions: Vec<IRInstr>,
}

impl Default for Block {
    fn default() -> Self {
        Self {
            func_name: None,
            name: String::new(),
            parameters: Vec::new(),
            instructions: Vec::new(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct IRData {
    pub alias: String,
    pub value: IRDataLiteral,
}

#[derive(Debug, Clone, PartialEq)]
pub enum IRDataLiteral {
    String(String),
    Float(f32),
}

#[derive(Debug, Clone, PartialEq)]
pub struct IRAddress {
    pub addr: IRAddressType,
    pub stored_data_type: Type,
    pub offset: IRAddressOffset,
}

impl std::fmt::Display for IRAddress {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let offset = match &self.offset {
            IRAddressOffset::Literal(offset) => format!("{offset}"),
            IRAddressOffset::IRVariable(offset_var) => format!("${offset_var}$"),
        };

        match &self.addr {
            IRAddressType::Data(addr)
            | IRAddressType::RawAddr(addr)
            | IRAddressType::Register(addr) => {
                if offset == "0" {
                    f.write_fmt(format_args!("[{addr}]"))
                } else if offset.starts_with("-") {
                    f.write_fmt(format_args!("[{addr}{offset}]"))
                } else {
                    f.write_fmt(format_args!("[{addr}+{offset}]"))
                }
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum IRAddressOffset {
    Literal(isize),
    IRVariable(usize),
}

#[derive(Debug, Clone, PartialEq)]
pub enum IRAddressType {
    RawAddr(String),
    Register(String),
    Data(String),
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

#[derive(Debug, Clone)]
pub enum InlineTargetPart {
    String(String),
    SSAIRVarRef(usize),
}

#[derive(Debug, Clone)]
pub enum IRInstr {
    Assign(VariableID, IRValue),
    BinOp(VariableID, IRValue, IRValue, BinaryOperation),
    UnOp(VariableID, IRValue, UnaryOperation),
    Call(VariableID, IRValue, Vec<IRValue>),
    If(
        Box<Expression>,
        IRValue,
        String,
        Vec<IRValue>,
        String,
        Vec<IRValue>,
    ),
    Goto(String, Vec<IRValue>),

    Store(IRAddress, IRValue),
    Load(VariableID, IRAddress),

    Return(Option<IRValue>),
    Label(String),

    InlineTarget(Vec<InlineTargetPart>, Vec<String>), //Target parts, used registers

    Unimplemented(VariableID, String),
}

impl SSAIR {
    pub fn pretty_print_irval(&self, irval: &IRValue) -> String {
        match irval {
            IRValue::Address(address) => format!("{address}"),
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
                let val = self.pretty_print_irval(val);
                format!("store {addr} {val}")
            }
            IRInstr::Load(var, addr) => {
                let variable = &self.vars[*var];
                format!("{} ({var}) = load {addr}", variable.name)
            }
            IRInstr::Assign(lhs, rhs) => {
                let rhs = self.pretty_print_irval(rhs);
                let variable = &self.vars[*lhs];
                format!("{} ({lhs}) = {rhs} ", variable.name)
            }
            IRInstr::BinOp(var, irvalue, irvalue1, op) => {
                let irvalue = self.pretty_print_irval(irvalue);
                let irvalue1 = self.pretty_print_irval(irvalue1);
                let variable = &self.vars[*var];
                format!("{} ({var}) = {irvalue} {op} {irvalue1}", variable.name)
            }
            IRInstr::UnOp(var, irvalue, op) => {
                let irvalue = self.pretty_print_irval(irvalue);
                let variable = &self.vars[*var];
                format!("{} ({var}) = {op}{irvalue}", variable.name)
            }
            IRInstr::Call(var, func, vec) => {
                let params = vec
                    .iter()
                    .map(|param| self.pretty_print_irval(param))
                    .collect::<Vec<_>>();
                let params = params.join(", ");

                let func = self.pretty_print_irval(func);
                let variable = &self.vars[*var];
                format!("{} ({var}) = call {func}({params})", variable.name)
            }
            IRInstr::Return(val) => {
                if let Some(val) = val {
                    let val = self.pretty_print_irval(val);
                    format!("ret {val}")
                } else {
                    format!("ret")
                }
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
            IRInstr::If(cond, val, true_label, true_args, false_label, false_args) => {
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
            IRInstr::InlineTarget(expr, registers) => {
                format!("Inline (...), {registers:?}")
            }

            IRInstr::Unimplemented(var, str) => {
                let var = &self.vars[*var];
                format!("{} = [[{str}]]", var.name)
            }
        }
    }

    pub fn pretty_print_ssa(&self) {
        if !self.data.is_empty() {
            println!("data:");
            for data in &self.data {
                println!("\t{}: {:?}", data.alias, data.value);
            }
        }

        for block in &self.blocks {
            println!("{}", self.pretty_print_block_name(block));
            println!("{}", self.pretty_print_block(block));
        }
    }

    pub fn pretty_print_block_name(&self, block: &Block) -> String {
        let mut out = String::new();
        let params = block
            .parameters
            .iter()
            .map(|param_idx| {
                let param = &self.vars[*param_idx];
                format!("{} ({}): {}", param.name, param_idx, param.ty)
            })
            .collect::<Vec<_>>();
        let params = params.join(", ");
        out += &format!("{}({}):", block.name, params);
        out
    }

    pub fn pretty_print_block(&self, block: &Block) -> String {
        let mut out = String::new();

        for instr in &block.instructions {
            let instr = self.pretty_print_instr(instr);
            out += &format!("\t{instr}\n")
        }

        out
    }
}
