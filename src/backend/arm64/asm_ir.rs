use std::{
    collections::{HashMap, HashSet},
    fmt::Write,
    sync::LazyLock,
};

use crate::{
    ast::{BinaryOp, BinaryOperation, Expression, Type, UnaryOp, UnaryOperation},
    backend::{
        liveness::{InstrIndex, VarLifespans},
        ssa_ir::{
            AddrIncrement, IRAddress, IRAddressOffset, IRAddressType, IRInstr, IRValue,
            InlineTargetPart, SSAIR,
        },
    },
    lexer::Literal,
};

#[derive(Eq, PartialEq, Debug, Copy, Clone, Hash)]
pub enum RegisterType {
    General,
    Float32,
}

#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq)]
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

        if let RegisterType::General = self.ty {
            if self.num == 31 {
                return f.write_fmt(format_args!("sp"));
            }

            if self.num == 30 {
                return f.write_fmt(format_args!("lr"));
            }

            if self.num == 29 {
                return f.write_fmt(format_args!("fp"));
            }
        }
        f.write_fmt(format_args!("{prefix}{}", self.num))
    }
}

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

static SP_REG: Register = Register {
    ty: RegisterType::General,
    num: 31,
};

static LR_REG: Register = Register {
    ty: RegisterType::General,
    num: 30,
};

static FP_REG: Register = Register {
    ty: RegisterType::General,
    num: 29,
};

pub fn get_instruction_set(ty: &Type) -> InstrSet {
    let mut set = BASE_INSTR_SET.clone();
    return match &ty {
        Type::Float => {
            set.insert("mov", "fmov");
            set.insert("add", "fadd");
            set.insert("sub", "fsub");
            set.insert("mul", "fmul");
            set.insert("div", "fdiv");
            set.insert("neg", "fneg");
            set.insert("cmp", "fcmp");
            set
        }
        _ => set,
    };
}

pub fn get_instruction_set_reg(ty: &RegisterType) -> InstrSet {
    let mut set = BASE_INSTR_SET.clone();
    return match &ty {
        RegisterType::Float32 => {
            set.insert("mov", "fmov");
            set.insert("add", "fadd");
            set.insert("sub", "fsub");
            set.insert("mul", "fmul");
            set.insert("div", "fdiv");
            set.insert("neg", "fneg");
            set.insert("cmp", "fcmp");
            set
        }
        _ => set,
    };
}

pub fn get_reg_ty(ty: &Type) -> RegisterType {
    return match &ty {
        Type::Float => RegisterType::Float32,
        _ => RegisterType::General,
    };
}

#[derive(Default, Debug, Clone)]
pub struct ASMIR {
    pub blocks: Vec<ASMBlock>,
    pub vars: Vec<ASMVar>,
    pub var_lifespans: VarLifespans,
}

#[derive(Debug, Clone)]
pub struct ASMBlock {
    pub name: String,
    pub live_vars: HashSet<usize>, // Kinda weird that ssa_ir has a VariableID type alias and i dont use it here but idk
    pub instructions: Vec<(usize, ASMInstr)>,
}

impl Default for ASMBlock {
    fn default() -> Self {
        Self {
            name: String::new(),
            live_vars: HashSet::new(),
            instructions: Vec::new(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum ASMInstr {
    InlineAsm(
        Vec<InlineTargetPart>,
        Vec<String>,
        HashMap<usize, AllocPlace>,
    ),
    Instr {
        instr: String,
        args: Vec<ASMValue>,
    },
}

#[derive(Debug, Clone)]
pub enum ASMValue {
    Label(String),
    Register(Register),
    Variable(usize),
    Address(IRAddress),
    Literal(isize),
    // Hate this
    ArbitraryString(String),
}

impl ASMValue {
    fn from_irval(irval: &IRValue) -> Self {
        match irval {
            IRValue::Literal(Literal::Int(num)) => Self::Literal(*num),
            IRValue::Literal(Literal::Uint(num)) => Self::Literal(*num as isize),
            // This is reversed because we are comparing against 0
            IRValue::Literal(Literal::Boolean(true)) => Self::Literal(0),
            IRValue::Literal(Literal::Boolean(false)) => Self::Literal(1),
            IRValue::Variable(var) => Self::Variable(*var),
            IRValue::Address(iraddress) => Self::Address(iraddress.clone()),
            _ => unreachable!(),
        }
    }
}

pub fn get_ir_value_type(vars: &Vec<ASMVar>, ir_val: &IRValue) -> Type {
    let ty = match ir_val {
        IRValue::Address(_) => unreachable!(), // i dont think this shows up
        IRValue::Literal(lit) => lit.ty().clone(),
        IRValue::Variable(var_id) => vars[*var_id].ty.clone(),
    };

    ty
}

#[derive(Debug, Clone)]
pub struct ASMVar {
    pub ir_name: String,
    pub ty: Type,
    pub allocated_to: Vec<(InstrIndex, AllocPlace)>,
}

impl ASMVar {
    pub fn get_alloc_place(&self, instr_index: InstrIndex) -> AllocPlace {
        let mut last_place = AllocPlace::Unallocated;
        for (start_idx, alloc_place) in &self.allocated_to {
            if instr_index < *start_idx {
                break;
            }

            last_place = alloc_place.clone();
        }

        last_place
    }
}

#[derive(Debug, Clone)]
pub enum AllocPlace {
    Register(Register),
    Stack(isize), // Offset from fp
    Unallocated,
}

pub fn ssa_to_asm(ssa: &SSAIR) -> ASMIR {
    let mut asmir = ASMIR::default();

    for (i, var) in ssa.vars.iter().enumerate() {
        // Important to keep the ids the same
        asmir.vars.push(ASMVar {
            ir_name: var.name.clone(),
            ty: var.ty.clone(),
            allocated_to: vec![],
        });
    }

    for (block_idx, ir_block) in ssa.blocks.iter().enumerate() {
        let mut block = ASMBlock {
            name: ir_block.name.clone(),
            live_vars: ir_block.parameters.iter().cloned().collect::<HashSet<_>>(),
            ..Default::default()
        };

        let instr_idx = 0;

        // block starts func
        if let Some(_) = ir_block.starts_func {
            // Setup stack frame
            // stp fp, lr, [sp,#-16]
            block.instructions.push((
                instr_idx,
                ASMInstr::Instr {
                    instr: "stp".to_string(),
                    args: vec![
                        ASMValue::Register(FP_REG),
                        ASMValue::Register(LR_REG),
                        ASMValue::Address(IRAddress {
                            addr: IRAddressType::Register("sp".to_string()),
                            stored_data_type: Type::Void,
                            offset: IRAddressOffset::Literal(-16),
                            increment: Some(AddrIncrement::PreIncrement),
                        }),
                    ],
                },
            ));
            // mov fp, sp
            block.instructions.push((
                instr_idx,
                ASMInstr::Instr {
                    instr: "mov".to_string(),
                    args: vec![ASMValue::Register(FP_REG), ASMValue::Register(SP_REG)],
                },
            ));
            // sub sp, sp, #16
            block.instructions.push((
                instr_idx,
                ASMInstr::Instr {
                    instr: "sub".to_string(),
                    args: vec![
                        ASMValue::Register(SP_REG),
                        ASMValue::Register(SP_REG),
                        ASMValue::Literal(16),
                    ],
                },
            ));

            let mut arg_count = 0;
            if ir_block.parameters.len() >= 8 {
                unimplemented!("CANT PASS MORE THAN 8 PARAMS FOR NOW");
            }
            for arg_id in &ir_block.parameters {
                let arg_var = &mut asmir.vars[*arg_id];

                let reg_ty = get_reg_ty(&arg_var.ty);

                let arg_register = Register {
                    ty: reg_ty,
                    num: arg_count,
                };

                arg_var.allocated_to.push((
                    InstrIndex {
                        block_idx,
                        instr_idx,
                    },
                    AllocPlace::Register(arg_register),
                ));

                arg_count += 1;
            }
        }

        for (instr_idx, instr) in ir_block.instructions.iter().enumerate() {
            let instr_index = InstrIndex {
                block_idx,
                instr_idx,
            };

            match instr {
                IRInstr::InlineTarget(parts, clobbered_registers) => {
                    block.instructions.push((
                        instr_idx,
                        ASMInstr::InlineAsm(
                            parts.clone(),
                            clobbered_registers.clone(),
                            HashMap::new(),
                        ),
                    ));
                }
                IRInstr::Assign(var, val) => {
                    let var_ty = asmir.vars[*var].ty.clone();
                    let instr_set = get_instruction_set(&var_ty);

                    block.live_vars.insert(*var);
                    if let IRValue::Variable(var) = val {
                        block.live_vars.insert(*var);
                    }

                    let mov = instr_set["mov"];

                    block.instructions.push((
                        instr_idx,
                        ASMInstr::Instr {
                            instr: mov.to_string(),
                            args: vec![ASMValue::Variable(*var), ASMValue::from_irval(val)],
                        },
                    ));
                }
                IRInstr::Return(val) => {
                    if let Some(val) = val {
                        let var_ty = get_ir_value_type(&asmir.vars, val);
                        let instr_set = get_instruction_set(&var_ty);
                        let reg_ty = get_reg_ty(&var_ty);

                        let mov = instr_set["mov"];

                        let output_reg = Register { num: 0, ty: reg_ty };

                        block.instructions.push((
                            instr_idx,
                            ASMInstr::Instr {
                                instr: mov.to_string(),
                                args: vec![
                                    ASMValue::Register(output_reg),
                                    ASMValue::from_irval(val),
                                ],
                            },
                        ))
                    }

                    // destroy stack frame and return

                    // mov sp, fp
                    block.instructions.push((
                        instr_idx,
                        ASMInstr::Instr {
                            instr: "mov".to_string(),
                            args: vec![ASMValue::Register(SP_REG), ASMValue::Register(FP_REG)],
                        },
                    ));

                    // ldp fp, lr, [sp], #16
                    block.instructions.push((
                        instr_idx,
                        ASMInstr::Instr {
                            instr: "ldp".to_string(),
                            args: vec![
                                ASMValue::Register(FP_REG),
                                ASMValue::Register(LR_REG),
                                ASMValue::Address(IRAddress {
                                    addr: IRAddressType::Register("sp".to_string()),
                                    stored_data_type: Type::Void,
                                    offset: IRAddressOffset::Literal(0),
                                    increment: Some(AddrIncrement::PostIncrement),
                                }),
                                ASMValue::Literal(16),
                            ],
                        },
                    ));

                    // ret
                    block.instructions.push((
                        instr_idx,
                        ASMInstr::Instr {
                            instr: "ret".to_string(),
                            args: vec![],
                        },
                    ));
                }
                IRInstr::Call(ret, called, args) => {
                    // Todo: pass in the arguments
                    let mut arg_count = 0;
                    for arg in args {
                        let arg_type = get_ir_value_type(&asmir.vars, arg);

                        let instr_set = get_instruction_set(&arg_type);
                        let reg_ty = get_reg_ty(&arg_type);

                        let register = Register {
                            ty: reg_ty,
                            num: arg_count,
                        };

                        if let IRValue::Variable(var) = arg {
                            block.live_vars.insert(*var);
                        }

                        let mov = instr_set["mov"];

                        block.instructions.push((
                            instr_idx,
                            ASMInstr::Instr {
                                instr: mov.to_string(),
                                args: vec![ASMValue::Register(register), ASMValue::from_irval(arg)],
                            },
                        ));

                        arg_count += 1;
                    }

                    // let called_asm = self.ir_value_to_asm(&mut out, &called);
                    match called {
                        IRValue::Variable(var_id) => {
                            block.live_vars.insert(*var_id);

                            let label_name = asmir.vars[*var_id].ir_name.clone();
                            block.instructions.push((
                                instr_idx,
                                ASMInstr::Instr {
                                    instr: "bl".to_string(),
                                    args: vec![ASMValue::Label(label_name)],
                                },
                            ));
                        }
                        _ => unimplemented!(),
                    }

                    // return val
                    block.live_vars.insert(*ret);
                    let ret_val_ty = asmir.vars[*ret].ty.clone();
                    let reg_ty = get_reg_ty(&ret_val_ty);
                    asmir.vars[*ret].allocated_to.push((
                        instr_index,
                        AllocPlace::Register(Register { ty: reg_ty, num: 0 }),
                    ));
                }
                IRInstr::BinOp(res, lhs, rhs, op) => {
                    let ty = asmir.vars[*res].ty.clone();
                    let instr_set = get_instruction_set(&ty);
                    let reg_ty = get_reg_ty(&ty);

                    let mov = instr_set["mov"];
                    let add = instr_set["add"];
                    let sub = instr_set["sub"];
                    let mul = instr_set["mul"];
                    let cmp = instr_set["cmp"];

                    block.live_vars.insert(*res);
                    if let IRValue::Variable(var) = lhs {
                        block.live_vars.insert(*var);
                    }
                    if let IRValue::Variable(var) = rhs {
                        block.live_vars.insert(*var);
                    }

                    match op {
                        BinaryOperation::Add => {
                            block.instructions.push((
                                instr_idx,
                                ASMInstr::Instr {
                                    instr: add.to_string(),
                                    args: vec![
                                        ASMValue::Variable(*res),
                                        ASMValue::from_irval(lhs),
                                        ASMValue::from_irval(rhs),
                                    ],
                                },
                            ));
                        }
                        BinaryOperation::Subtract => {
                            block.instructions.push((
                                instr_idx,
                                ASMInstr::Instr {
                                    instr: sub.to_string(),
                                    args: vec![
                                        ASMValue::Variable(*res),
                                        ASMValue::from_irval(lhs),
                                        ASMValue::from_irval(rhs),
                                    ],
                                },
                            ));
                        }
                        BinaryOperation::Multiply => {
                            block.instructions.push((
                                instr_idx,
                                ASMInstr::Instr {
                                    instr: mul.to_string(),
                                    args: vec![
                                        ASMValue::Variable(*res),
                                        ASMValue::from_irval(lhs),
                                        ASMValue::from_irval(rhs),
                                    ],
                                },
                            ));
                        }
                        BinaryOperation::Divide => {
                            // Div is not a thing for non floats so this has to be here
                            let div = instr_set["div"];

                            block.instructions.push((
                                instr_idx,
                                ASMInstr::Instr {
                                    instr: div.to_string(),
                                    args: vec![
                                        ASMValue::Variable(*res),
                                        ASMValue::from_irval(lhs),
                                        ASMValue::from_irval(rhs),
                                    ],
                                },
                            ));
                        }
                        // idk
                        BinaryOperation::Equal
                        | BinaryOperation::NotEqual
                        | BinaryOperation::Greater
                        | BinaryOperation::GreaterEqual
                        | BinaryOperation::Less
                        | BinaryOperation::LessEqual => {
                            // This will only work correctly for ints and floats and maybe checking equality for addresses
                            block.instructions.push((
                                instr_idx,
                                ASMInstr::Instr {
                                    instr: cmp.to_string(),
                                    args: vec![
                                        ASMValue::from_irval(lhs),
                                        ASMValue::from_irval(rhs),
                                    ],
                                },
                            ));
                        }
                        other => {
                            unreachable!("What {other:?}");
                        }
                    }
                }
                IRInstr::If(cond, irval, true_label, true_args, false_label, false_args) => {
                    if let IRValue::Variable(var) = irval {
                        block.live_vars.insert(*var);
                    }
                    // Not sure if this is needed
                    for true_arg in true_args {
                        if let IRValue::Variable(var) = true_arg {
                            block.live_vars.insert(*var);
                        }
                    }
                    for false_arg in false_args {
                        if let IRValue::Variable(var) = false_arg {
                            block.live_vars.insert(*var);
                        }
                    }

                    match **cond {
                        Expression::BinaryOp(BinaryOp { op, .. }) => {
                            let true_instr = match op {
                                BinaryOperation::NotEqual => "b.ne",
                                BinaryOperation::Equal => "b.eq",
                                BinaryOperation::Less => "b.lt",
                                BinaryOperation::LessEqual => "b.le",
                                BinaryOperation::Greater => "b.gt",
                                BinaryOperation::GreaterEqual => "b.ge",
                                // Handle && and ||
                                _ => {
                                    block.instructions.push((
                                        instr_idx,
                                        ASMInstr::Instr {
                                            instr: "cmp".to_string(),
                                            args: vec![
                                                ASMValue::from_irval(irval),
                                                ASMValue::Literal(0),
                                            ],
                                        },
                                    ));
                                    "b.ne"
                                }
                            };
                            block.instructions.push((
                                instr_idx,
                                ASMInstr::Instr {
                                    instr: true_instr.to_string(),
                                    args: vec![ASMValue::Label(true_label.clone())],
                                },
                            ));

                            block.instructions.push((
                                instr_idx,
                                ASMInstr::Instr {
                                    instr: "b".to_string(),
                                    args: vec![ASMValue::Label(false_label.clone())],
                                },
                            ));
                        }
                        // FIXME: These probably shouldnt be hardcoded?
                        Expression::UnaryOp(UnaryOp { op, ref operand }) => match op {
                            UnaryOperation::Negate => match **operand {
                                Expression::Literal(Literal::Boolean(boolean)) => {
                                    let label = if !boolean { true_label } else { false_label };

                                    block.instructions.push((
                                        instr_idx,
                                        ASMInstr::Instr {
                                            instr: "b".to_string(),
                                            args: vec![ASMValue::Label(label.clone())],
                                        },
                                    ));
                                }
                                _ => unimplemented!("co"),
                            },
                            _ => unimplemented!("co2"),
                        },
                        Expression::Literal(Literal::Boolean(boolean)) => {
                            let label = if boolean { true_label } else { false_label };
                            block.instructions.push((
                                instr_idx,
                                ASMInstr::Instr {
                                    instr: "b".to_string(),
                                    args: vec![ASMValue::Label(label.clone())],
                                },
                            ));
                        }
                        ref cond => unimplemented!("{cond:?}"),
                    };
                }
                IRInstr::Goto(label, args) => {
                    for arg in args {
                        if let IRValue::Variable(var) = arg {
                            block.live_vars.insert(*var);
                        }
                    }
                    block.instructions.push((
                        instr_idx,
                        ASMInstr::Instr {
                            instr: "b".to_string(),
                            args: vec![ASMValue::Label(label.clone())],
                        },
                    ));
                }
                IRInstr::UnOp(res, operand, op) => {
                    let ty = asmir.vars[*res].ty.clone();
                    let instr_set = get_instruction_set(&ty);
                    let reg_ty = get_reg_ty(&ty);

                    let mov = instr_set["mov"];
                    let neg = instr_set["neg"];

                    block.live_vars.insert(*res);
                    if let IRValue::Variable(var) = operand {
                        block.live_vars.insert(*var);
                    }

                    match op {
                        // TODO: Find a less `hardcoded` way
                        UnaryOperation::Negate => match operand {
                            IRValue::Literal(Literal::Boolean(boolean)) => {
                                block.instructions.push((
                                    instr_idx,
                                    ASMInstr::Instr {
                                        instr: mov.to_string(),
                                        args: vec![
                                            ASMValue::Variable(*res),
                                            ASMValue::Literal(if *boolean { 0 } else { 1 }),
                                        ],
                                    },
                                ));
                            }
                            _ => unimplemented!(),
                        },
                        UnaryOperation::Negative => {
                            // be smarter with registers
                            block.instructions.push((
                                instr_idx,
                                ASMInstr::Instr {
                                    instr: mov.to_string(),
                                    args: vec![
                                        ASMValue::Variable(*res),
                                        ASMValue::from_irval(operand),
                                    ],
                                },
                            ));

                            block.instructions.push((
                                instr_idx,
                                ASMInstr::Instr {
                                    instr: neg.to_string(),
                                    args: vec![ASMValue::Variable(*res), ASMValue::Variable(*res)],
                                },
                            ));
                        }
                        _ => unimplemented!(),
                    }
                }
                IRInstr::Store(addr, ir_val) => {
                    if let IRValue::Variable(var) = ir_val {
                        block.live_vars.insert(*var);
                    }

                    block.instructions.push((
                        instr_idx,
                        ASMInstr::Instr {
                            instr: "str".to_string(),
                            args: vec![
                                ASMValue::from_irval(ir_val),
                                ASMValue::Address(addr.clone()),
                            ],
                        },
                    ));
                }
                IRInstr::Load(res, addr) => {
                    let offset = &addr.offset;

                    block.live_vars.insert(*res);
                    match &addr.offset {
                        IRAddressOffset::IRVariable(var) => {
                            block.live_vars.insert(*var);
                        }
                        _ => {}
                    }

                    match &addr.addr {
                        IRAddressType::VarReg(_) => unimplemented!(),
                        IRAddressType::Data(data) => unimplemented!(),
                        IRAddressType::DataPage(data) => match &addr.stored_data_type {
                            Type::String => {
                                block.instructions.push((
                                    instr_idx,
                                    ASMInstr::Instr {
                                        instr: "adrp".to_string(),
                                        args: vec![
                                            ASMValue::Variable(*res),
                                            ASMValue::Address(addr.clone()),
                                        ],
                                    },
                                ));
                                block.instructions.push((
                                    instr_idx,
                                    ASMInstr::Instr {
                                        instr: "add".to_string(),
                                        args: vec![
                                            ASMValue::Variable(*res),
                                            ASMValue::Variable(*res),
                                            ASMValue::ArbitraryString(
                                                asmir.pretty_print_addr_offset(
                                                    &addr.offset,
                                                    instr_index,
                                                ),
                                            ),
                                        ],
                                    },
                                ));
                            }
                            Type::Float => {
                                // temp var for `adrp`
                                asmir.vars.push(ASMVar {
                                    ir_name: format!("__{}", asmir.vars.len()),
                                    ty: Type::Int,
                                    allocated_to: vec![],
                                });
                                let temp_var = asmir.vars.len() - 1;

                                asmir.var_lifespans.extend_lifespan(temp_var, instr_index);

                                block.instructions.push((
                                    instr_idx,
                                    ASMInstr::Instr {
                                        instr: "adrp".to_string(),
                                        args: vec![
                                            ASMValue::Variable(temp_var),
                                            ASMValue::Address(addr.clone()),
                                        ],
                                    },
                                ));

                                let mut addr_clone = addr.clone();
                                addr_clone.addr = IRAddressType::VarReg(temp_var);

                                block.instructions.push((
                                    instr_idx,
                                    ASMInstr::Instr {
                                        instr: "ldr".to_string(),
                                        args: vec![
                                            ASMValue::Variable(*res),
                                            ASMValue::Address(addr_clone),
                                        ],
                                    },
                                ));
                                // This is what the last .push should represent
                                // write!(out, "\tldr {register}, [{temp_reg}, {addr}@PAGEOFF]\n")
                                //     .unwrap();
                            }
                            _ => unimplemented!(),
                        },
                        IRAddressType::Register(..) => {
                            block.instructions.push((
                                instr_idx,
                                ASMInstr::Instr {
                                    instr: "ldr".to_string(),
                                    args: vec![
                                        ASMValue::Variable(*res),
                                        ASMValue::Address(addr.clone()),
                                    ],
                                },
                            ));
                        }
                        IRAddressType::RawAddr(addr) => unimplemented!(),
                    }
                }

                instr => {
                    println!("whatt: {instr:?}");
                }
            }
        }

        asmir.blocks.push(block);
        asmir.var_lifespans = ssa.var_lifespans.clone();
    }

    asmir
}

impl ASMIR {
    pub fn pretty_print(&self) -> String {
        let mut out = String::new();
        for (block_idx, block) in self.blocks.iter().enumerate() {
            write!(out, "{}", self.pretty_print_block(block, block_idx)).unwrap();
        }

        out
    }

    pub fn pretty_print_block(&self, block: &ASMBlock, block_idx: usize) -> String {
        let mut out = String::new();
        write!(out, "{}:\n", block.name).unwrap();

        for (instr_idx, instr) in &block.instructions {
            let instr_index = InstrIndex {
                block_idx,
                instr_idx: *instr_idx,
            };
            let instr = self.pretty_print_instr(instr, instr_index);
            write!(out, "\t{instr}\n").unwrap();
        }

        out
    }

    pub fn pretty_print_instr(&self, instr: &ASMInstr, instr_index: InstrIndex) -> String {
        let mut out = String::new();

        match instr {
            ASMInstr::InlineAsm(inline_target_parts, clobbered, saved_vars) => {
                for part in inline_target_parts {
                    match part {
                        InlineTargetPart::String(str) => write!(out, "{str}").unwrap(),
                        InlineTargetPart::SSAIRVarRef(var) => {
                            let var = if let Some(new_place) = saved_vars.get(var) {
                                match new_place {
                                    AllocPlace::Unallocated => format!("%{var}"),
                                    AllocPlace::Register(reg) => format!("{reg}"),
                                    AllocPlace::Stack(offset) => format!("[fp,#{offset}]"),
                                }
                            } else {
                                self.pretty_print_var(*var, instr_index)
                            };

                            write!(out, "{var}").unwrap();
                        }
                    }
                }
            }
            ASMInstr::Instr { instr, args } => {
                let args = args
                    .iter()
                    .map(|arg| self.pretty_print_asm_val(arg, instr_index))
                    .collect::<Vec<_>>()
                    .join(", ");

                write!(out, "{instr} {args}").unwrap()
            }
        };

        out
    }

    pub fn pretty_print_asm_val(&self, asm_val: &ASMValue, instr_index: InstrIndex) -> String {
        match asm_val {
            ASMValue::ArbitraryString(str) => str.clone(),
            ASMValue::Label(label) => format!("{label}"),
            ASMValue::Register(reg) => format!("{reg}"),
            ASMValue::Variable(var) => {
                let var = self.pretty_print_var(*var, instr_index);
                format!("{var}")
            }
            ASMValue::Address(addr) => self.pretty_print_addr(addr, instr_index),
            ASMValue::Literal(lit) => format!("#{lit}"),
        }
    }

    pub fn pretty_print_var(&self, var: usize, instr_index: InstrIndex) -> String {
        let alloc_place = &self.vars[var].get_alloc_place(instr_index);

        match alloc_place {
            AllocPlace::Unallocated => format!("%{var}"),
            AllocPlace::Register(reg) => format!("{reg}"),
            AllocPlace::Stack(offset) => format!("[fp,#{offset}]"),
        }
    }

    pub fn pretty_print_addr_offset(
        &self,
        offset: &IRAddressOffset,
        instr_index: InstrIndex,
    ) -> String {
        match &offset {
            IRAddressOffset::Literal(offset) => format!("#{offset}"),
            IRAddressOffset::IRVariable(offset_var) => {
                self.pretty_print_var(*offset_var, instr_index)
            }
            IRAddressOffset::DataPageOffset(data) => {
                format!("{data}@PAGEOFF")
            }
        }
    }

    pub fn pretty_print_addr(&self, address: &IRAddress, instr_index: InstrIndex) -> String {
        let offset = self.pretty_print_addr_offset(&address.offset, instr_index);
        let full_addr = match &address.addr {
            IRAddressType::VarReg(var) => {
                let reg = &self.vars[*var].get_alloc_place(instr_index);
                if let AllocPlace::Register(reg) = reg {
                    let addr = reg.to_string();

                    if offset == "#0" {
                        format!("[{addr}]")
                    } else {
                        if let Some(increment) = &address.increment {
                            match increment {
                                AddrIncrement::PreIncrement => format!("[{addr},{offset}]!"),
                                AddrIncrement::PostIncrement => format!("[{addr}], {offset}"),
                            }
                        } else {
                            format!("[{addr},{offset}]")
                        }
                    }
                } else {
                    unimplemented!()
                }
            }
            IRAddressType::Data(addr)
            | IRAddressType::RawAddr(addr)
            | IRAddressType::Register(addr) => {
                if offset == "#0" {
                    format!("[{addr}]")
                } else {
                    if let Some(increment) = &address.increment {
                        match increment {
                            AddrIncrement::PreIncrement => format!("[{addr},{offset}]!"),
                            AddrIncrement::PostIncrement => format!("[{addr}], {offset}"),
                        }
                    } else {
                        format!("[{addr},{offset}]")
                    }
                }
            }
            IRAddressType::DataPage(data) => {
                format!("{data}@PAGE")
            }
        };

        full_addr
    }
}
