use std::{collections::HashMap, sync::LazyLock};

use crate::{
    ast::{BinaryOp, BinaryOperation, Expression, Type, UnaryOp, UnaryOperation},
    backend::ssa_ir::{
        IRAddress, IRAddressOffset, IRAddressType, IRInstr, IRValue, InlineTargetPart, SSAIR,
    },
    lexer::Literal,
};

#[derive(Eq, PartialEq, Debug, Copy, Clone)]
pub enum RegisterType {
    General,
    Float32,
}

#[derive(Debug, Clone, Copy)]
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

pub fn get_reg_ty(ty: &Type) -> RegisterType {
    return match &ty {
        Type::Float => RegisterType::Float32,
        _ => RegisterType::General,
    };
}

#[derive(Default, Debug)]
pub struct ASMIR {
    pub blocks: Vec<ASMBlock>,
    pub vars: HashMap<usize, ASMVar>,
}

#[derive(Debug)]
pub struct ASMBlock {
    pub name: String,
    pub live_vars: Vec<usize>, // Kinda weird that ssa_ir has a VariableID type alias and i dont use it here but idk
    pub instructions: Vec<ASMInstr>,
}

impl Default for ASMBlock {
    fn default() -> Self {
        Self {
            name: String::new(),
            live_vars: Vec::new(),
            instructions: Vec::new(),
        }
    }
}

#[derive(Debug)]
pub enum ASMInstr {
    InlineAsm(Vec<InlineTargetPart>, Vec<String>),
    Instr { instr: String, args: Vec<ASMValue> },
}

#[derive(Debug)]
pub enum ASMValue {
    Label(String),
    Register(Register),
    Variable(usize),
    Address(IRAddress),
    Literal(isize),
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

pub fn get_ir_value_type(vars: &HashMap<usize, ASMVar>, ir_val: &IRValue) -> Type {
    let ty = match ir_val {
        IRValue::Address(_) => unreachable!(), // i dont think this shows up
        IRValue::Literal(lit) => lit.ty().clone(),
        IRValue::Variable(var_id) => vars[var_id].ty.clone(),
    };

    ty
}

#[derive(Debug)]
pub struct ASMVar {
    pub ir_name: String,
    pub ty: Type,
}

pub fn ssa_to_asm(ssa: &SSAIR) -> ASMIR {
    let mut asmir = ASMIR::default();

    for (i, var) in ssa.vars.iter().enumerate() {
        // Important to keep the ids the same
        asmir.vars.insert(
            i,
            ASMVar {
                ir_name: var.name.clone(),
                ty: var.ty.clone(),
            },
        );
    }

    for ir_block in &ssa.blocks {
        let mut block = ASMBlock {
            name: ir_block.name.clone(),
            live_vars: ir_block.parameters.clone(),
            ..Default::default()
        };

        // TODO: Need to gather live variables
        for instr in &ir_block.instructions {
            match instr {
                IRInstr::InlineTarget(parts, clobbered_registers) => {
                    block.instructions.push(ASMInstr::InlineAsm(
                        parts.clone(),
                        clobbered_registers.clone(),
                    ));
                }
                IRInstr::Assign(var, val) => {
                    let var_ty = asmir.vars[var].ty.clone();
                    let instr_set = get_instruction_set(&var_ty);

                    let mov = instr_set["mov"];

                    block.instructions.push(ASMInstr::Instr {
                        instr: mov.to_string(),
                        args: vec![ASMValue::Variable(*var), ASMValue::from_irval(val)],
                    });
                }
                IRInstr::Return(val) => {
                    if let Some(val) = val {
                        let var_ty = get_ir_value_type(&asmir.vars, val);
                        let instr_set = get_instruction_set(&var_ty);
                        let reg_ty = get_reg_ty(&var_ty);

                        let mov = instr_set["mov"];

                        let output_reg = Register { num: 0, ty: reg_ty };

                        block.instructions.push(ASMInstr::Instr {
                            instr: mov.to_string(),
                            args: vec![ASMValue::Register(output_reg), ASMValue::from_irval(val)],
                        })
                    }

                    // destroy stack frame and return

                    // mov sp, fp
                    block.instructions.push(ASMInstr::Instr {
                        instr: "mov".to_string(),
                        args: vec![ASMValue::Register(SP_REG), ASMValue::Register(FP_REG)],
                    });

                    // ldp fp, lr, [sp], #16
                    block.instructions.push(ASMInstr::Instr {
                        instr: "ldp".to_string(),
                        args: vec![
                            ASMValue::Register(FP_REG),
                            ASMValue::Register(LR_REG),
                            ASMValue::Address(IRAddress {
                                addr: IRAddressType::Register("sp".to_string()),
                                stored_data_type: Type::Void,
                                offset: IRAddressOffset::Literal(0),
                                page: None,
                            }),
                            ASMValue::Literal(16),
                        ],
                    });

                    block.instructions.push(ASMInstr::Instr {
                        instr: "ret".to_string(),
                        args: vec![],
                    });
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

                        let mov = instr_set["mov"];

                        block.instructions.push(ASMInstr::Instr {
                            instr: mov.to_string(),
                            args: vec![ASMValue::Register(register), ASMValue::from_irval(arg)],
                        });

                        arg_count += 1;
                    }

                    // let called_asm = self.ir_value_to_asm(&mut out, &called);
                    match called {
                        IRValue::Variable(var_id) => {
                            let label_name = asmir.vars[var_id].ir_name.clone();
                            block.instructions.push(ASMInstr::Instr {
                                instr: "bl".to_string(),
                                args: vec![ASMValue::Label(label_name)],
                            });
                        }
                        _ => unimplemented!(),
                    }
                }
                IRInstr::BinOp(res, lhs, rhs, op) => {
                    let ty = asmir.vars[res].ty.clone();
                    let instr_set = get_instruction_set(&ty);
                    let reg_ty = get_reg_ty(&ty);

                    let mov = instr_set["mov"];
                    let add = instr_set["add"];
                    let sub = instr_set["sub"];
                    let mul = instr_set["mul"];
                    let cmp = instr_set["cmp"];

                    match op {
                        BinaryOperation::Add => {
                            block.instructions.push(ASMInstr::Instr {
                                instr: add.to_string(),
                                args: vec![
                                    ASMValue::Variable(*res),
                                    ASMValue::from_irval(lhs),
                                    ASMValue::from_irval(rhs),
                                ],
                            });
                        }
                        BinaryOperation::Subtract => {
                            block.instructions.push(ASMInstr::Instr {
                                instr: sub.to_string(),
                                args: vec![
                                    ASMValue::Variable(*res),
                                    ASMValue::from_irval(lhs),
                                    ASMValue::from_irval(rhs),
                                ],
                            });
                        }
                        BinaryOperation::Multiply => {
                            block.instructions.push(ASMInstr::Instr {
                                instr: mul.to_string(),
                                args: vec![
                                    ASMValue::Variable(*res),
                                    ASMValue::from_irval(lhs),
                                    ASMValue::from_irval(rhs),
                                ],
                            });
                        }
                        BinaryOperation::Divide => {
                            // Div is not a thing for non floats so this has to be here
                            let div = instr_set["div"];

                            block.instructions.push(ASMInstr::Instr {
                                instr: div.to_string(),
                                args: vec![
                                    ASMValue::Variable(*res),
                                    ASMValue::from_irval(lhs),
                                    ASMValue::from_irval(rhs),
                                ],
                            });
                        }
                        // idk
                        BinaryOperation::Equal
                        | BinaryOperation::NotEqual
                        | BinaryOperation::Greater
                        | BinaryOperation::GreaterEqual
                        | BinaryOperation::Less
                        | BinaryOperation::LessEqual => {
                            // This will only work correctly for ints and floats and maybe checking equality for addresses
                            block.instructions.push(ASMInstr::Instr {
                                instr: cmp.to_string(),
                                args: vec![ASMValue::from_irval(lhs), ASMValue::from_irval(rhs)],
                            });
                        }
                        other => {
                            unreachable!("What {other:?}");
                        }
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
                                // Handle && and ||
                                _ => {
                                    block.instructions.push(ASMInstr::Instr {
                                        instr: "cmp".to_string(),
                                        args: vec![
                                            ASMValue::from_irval(irval),
                                            ASMValue::Literal(0),
                                        ],
                                    });
                                    "b.ne"
                                }
                            };
                            block.instructions.push(ASMInstr::Instr {
                                instr: true_instr.to_string(),
                                args: vec![ASMValue::Label(true_label.clone())],
                            });

                            block.instructions.push(ASMInstr::Instr {
                                instr: "b".to_string(),
                                args: vec![ASMValue::Label(false_label.clone())],
                            });
                        }
                        // FIXME: These probably shouldnt be hardcoded?
                        Expression::UnaryOp(UnaryOp { op, ref operand }) => match op {
                            UnaryOperation::Negate => match **operand {
                                Expression::Literal(Literal::Boolean(boolean)) => {
                                    let label = if !boolean { true_label } else { false_label };

                                    block.instructions.push(ASMInstr::Instr {
                                        instr: "b".to_string(),
                                        args: vec![ASMValue::Label(label.clone())],
                                    });
                                }
                                _ => unimplemented!("co"),
                            },
                            _ => unimplemented!("co2"),
                        },
                        Expression::Literal(Literal::Boolean(boolean)) => {
                            let label = if boolean { true_label } else { false_label };
                            block.instructions.push(ASMInstr::Instr {
                                instr: "b".to_string(),
                                args: vec![ASMValue::Label(label.clone())],
                            });
                        }
                        ref cond => unimplemented!("{cond:?}"),
                    };
                }
                IRInstr::Goto(label, args) => {
                    block.instructions.push(ASMInstr::Instr {
                        instr: "b".to_string(),
                        args: vec![ASMValue::Label(label.clone())],
                    });
                }
                IRInstr::UnOp(res, operand, op) => {
                    let ty = asmir.vars[res].ty.clone();
                    let instr_set = get_instruction_set(&ty);
                    let reg_ty = get_reg_ty(&ty);

                    let mov = instr_set["mov"];
                    let neg = instr_set["neg"];

                    match op {
                        // TODO: Find a less `hardcoded` way
                        UnaryOperation::Negate => match operand {
                            IRValue::Literal(Literal::Boolean(boolean)) => {
                                block.instructions.push(ASMInstr::Instr {
                                    instr: mov.to_string(),
                                    args: vec![
                                        ASMValue::Variable(*res),
                                        ASMValue::Literal(if *boolean { 0 } else { 1 }),
                                    ],
                                });
                            }
                            _ => unimplemented!(),
                        },
                        UnaryOperation::Negative => {
                            // be smarter with registers
                            block.instructions.push(ASMInstr::Instr {
                                instr: mov.to_string(),
                                args: vec![ASMValue::Variable(*res), ASMValue::from_irval(operand)],
                            });

                            block.instructions.push(ASMInstr::Instr {
                                instr: neg.to_string(),
                                args: vec![ASMValue::Variable(*res), ASMValue::Variable(*res)],
                            });
                        }
                        _ => unimplemented!(),
                    }
                }
                IRInstr::Store(addr, ir_val) => {
                    let instr_set = get_instruction_set(&addr.stored_data_type);

                    let mov = instr_set["mov"];

                    block.instructions.push(ASMInstr::Instr {
                        instr: mov.to_string(),
                        args: vec![
                            ASMValue::from_irval(ir_val),
                            ASMValue::Address(addr.clone()),
                        ],
                    });
                }
                IRInstr::Load(res, addr) => {
                    let offset = &addr.offset;
                    let mut addr_page = addr.clone();
                    addr_page.page = Some(true);

                    // I know `off` is from offset but its like off as in turned off -> false
                    let mut addr_pageoff = addr.clone();
                    addr_pageoff.page = Some(false);

                    match &addr.addr {
                        IRAddressType::Data(data) => match &addr.stored_data_type {
                            Type::String => {
                                block.instructions.push(ASMInstr::Instr {
                                    instr: "adrp".to_string(),
                                    args: vec![
                                        ASMValue::Variable(*res),
                                        ASMValue::Address(addr_page.clone()),
                                    ],
                                });
                                block.instructions.push(ASMInstr::Instr {
                                    instr: "add".to_string(),
                                    args: vec![
                                        ASMValue::Variable(*res),
                                        ASMValue::Variable(*res),
                                        ASMValue::Address(addr_pageoff.clone()),
                                    ],
                                });
                            }
                            Type::Float => {
                                block.instructions.push(ASMInstr::Instr {
                                    instr: "adrp".to_string(),
                                    args: vec![
                                        ASMValue::Variable(*res),
                                        ASMValue::Address(addr_page.clone()),
                                    ],
                                });
                                block.instructions.push(ASMInstr::Instr {
                                    instr: "ldr".to_string(),
                                    args: vec![
                                        ASMValue::Variable(*res),
                                        // This is slightly off i suppose
                                        ASMValue::Address(addr_pageoff.clone()),
                                    ],
                                });
                                // This is what the last .push should represent
                                // write!(out, "\tldr {register}, [{temp_reg}, {addr}@PAGEOFF]\n")
                                //     .unwrap();
                            }
                            _ => unimplemented!(),
                        },
                        IRAddressType::Register(..) => {
                            block.instructions.push(ASMInstr::Instr {
                                instr: "ldr".to_string(),
                                args: vec![
                                    ASMValue::Variable(*res),
                                    ASMValue::Address(addr.clone()),
                                ],
                            });
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
    }

    asmir
}
