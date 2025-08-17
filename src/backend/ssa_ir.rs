use std::{collections::HashMap, fmt::Display};

use crate::{
    arena::Arena,
    ast::{Expression, SymbolIdx},
    backend::liveness::{InstrIndex, VarLifespans},
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
    pub func_names: Vec<String>,

    pub var_lifespans: VarLifespans,

    pub var_counter: u32,
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
            func_names: Vec::default(),
            var_counter: 0,
            var_lifespans: VarLifespans::default(),
        }
    }
}

pub type VariableID = usize;

#[derive(Debug, Clone)]
pub struct Block {
    pub starts_func: Option<(SymbolIdx, String)>,
    pub name: String,
    pub parameters: Vec<VariableID>,
    pub instructions: Vec<IRInstr>,
}

impl Default for Block {
    fn default() -> Self {
        Self {
            starts_func: None,
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
    pub increment: Option<AddrIncrement>,
}

impl IRAddress {
    pub fn pretty_print(&self, vars: &Vec<IRVariable>) -> String {
        let var_names = vars.iter().map(|var| var.name.clone()).collect();
        self.pretty_print_names(&var_names)
    }

    pub fn pretty_print_names(&self, var_names: &Vec<String>) -> String {
        let offset = match &self.offset {
            IRAddressOffset::Literal(offset) => format!("#{offset}"),
            IRAddressOffset::IRVariable(offset_var) => {
                let var_name = &var_names[*offset_var];
                format!("{var_name}")
            }
            IRAddressOffset::DataPageOffset(data) => {
                format!("{data}@PAGEOFF")
            }
        };

        match &self.addr {
            IRAddressType::Data(addr)
            | IRAddressType::RawAddr(addr)
            | IRAddressType::Register(addr) => {
                if offset == "#0" {
                    format!("[{addr}]")
                } else {
                    if let Some(increment) = &self.increment {
                        match increment {
                            AddrIncrement::PreIncrement => format!("[{addr},{offset}]!"),
                            AddrIncrement::PostIncrement => format!("[{addr}], {offset}"),
                        }
                    } else {
                        format!("[{addr},{offset}]")
                    }
                }
            }
            IRAddressType::VarReg(var) => {
                let var_name = &var_names[*var];
                format!("{var_name}")
            }
            IRAddressType::DataPage(data) => {
                format!("{data}@PAGE")
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum IRAddressOffset {
    Literal(isize),
    IRVariable(usize),
    DataPageOffset(String),
}

#[derive(Debug, Clone, PartialEq)]
pub enum IRAddressType {
    RawAddr(String),
    Register(String),
    VarReg(usize),
    Data(String),
    DataPage(String),
}

#[derive(Debug, Clone, PartialEq)]
pub enum AddrIncrement {
    PreIncrement,
    PostIncrement,
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

#[derive(Default, Debug, Clone)]
pub struct CFGraphNode {
    pub dependencies: Vec<usize>,
    pub dependees: Vec<usize>,
    pub strongly_connected: Option<usize>,

    pub block_idx: usize,
}

#[derive(Default, Debug, Clone)]
pub struct CFGraph {
    pub nodes: Arena<CFGraphNode>,
    pub strongly_conn: Vec<Vec<usize>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GraphFragment {
    CyclicGroup(usize),
    SingleNode(usize),
}

#[derive(Default, Debug, Clone)]
pub struct ParamContext {
    // target, prev_node
    pub visits: Vec<(GraphFragment, i32)>,
}

pub fn split_labels_into_blocks(instructions: Vec<IRInstr>) -> (Vec<IRInstr>, Vec<Block>) {
    let mut ret_blocks = vec![];
    let mut ret_instrs = vec![];
    let mut curr_block = None;

    for instr in instructions {
        match instr {
            IRInstr::Label(label) => {
                if let Some(curr_block) = curr_block {
                    ret_blocks.push(curr_block);
                }

                curr_block = Some(Block {
                    starts_func: None,
                    name: label,
                    parameters: vec![],
                    instructions: vec![],
                })
            }
            instr => {
                if let Some(curr_block) = &mut curr_block {
                    curr_block.instructions.push(instr);
                } else {
                    ret_instrs.push(instr);
                }
            }
        }
    }

    if let Some(curr_block) = curr_block {
        ret_blocks.push(curr_block);
    }

    return (ret_instrs, ret_blocks);
}

impl SSAIR {
    pub fn make_name_unique(&mut self, smth: &str) -> String {
        let res = format!("{smth}_{}", self.var_counter);
        self.var_counter += 1;

        return res;
    }

    pub fn prune_all_instructions_after_first_branch(&mut self, func_block_idx: usize) {
        let len = self.blocks.len();
        for block_idx in func_block_idx..len {
            let block = &mut self.blocks[block_idx];
            let mut instructions = Vec::new();

            for instr in block.instructions.clone() {
                match instr {
                    instr @ IRInstr::Goto(_, _) | instr @ IRInstr::If(_, _, _, _, _, _) => {
                        instructions.push(instr);
                        break;
                    }
                    instr => instructions.push(instr),
                }
            }

            block.instructions = instructions;
        }
    }

    pub fn fix_passing_parameters_by_gotos(&mut self, func_block_idx: usize) {
        let len = self.blocks.len();

        let blocks_copy = self.blocks.clone();

        for idx in func_block_idx..len {
            let block = &mut self.blocks[idx];
            let mut local_vars = Vec::new();

            for param in &block.parameters {
                local_vars.push(param);
            }

            for instr in &mut block.instructions {
                match instr {
                    IRInstr::Load(res, _) => {
                        local_vars.push(res);
                    }
                    IRInstr::Store(_, _) => {}
                    IRInstr::Unimplemented(res, _) => {
                        local_vars.push(res);
                    }
                    IRInstr::Assign(res, irvalue) => {
                        local_vars.push(res);
                    }
                    IRInstr::BinOp(res, irvalue, irvalue1, _) => {
                        local_vars.push(res);
                    }
                    IRInstr::UnOp(res, irvalue, unary_operation) => {
                        local_vars.push(res);
                    }
                    IRInstr::Call(res, irvalue, args) => {
                        local_vars.push(res);
                    }
                    IRInstr::If(cond, irvalue, true_label, true_args, false_label, false_args) => {
                        // add all params of branches
                        let true_block =
                            blocks_copy.iter().find(|b| b.name == *true_label).unwrap();

                        for arg in &true_block.parameters {
                            let arg_name = &self.vars[*arg].name;
                            let var_in_this_block = local_vars.iter().find(|v| **v == arg);

                            if let Some(var_in_this_block) = var_in_this_block {
                                let var = IRValue::Variable(**var_in_this_block);
                                if !true_args.contains(&var) {
                                    true_args.push(var);
                                }
                            } else {
                                eprintln!("true args: Missing var {arg_name}");
                                continue;
                            }
                        }

                        let false_block =
                            blocks_copy.iter().find(|b| b.name == *false_label).unwrap();

                        for arg in &false_block.parameters {
                            let arg_name = &self.vars[*arg].name;
                            let var_in_this_block = local_vars.iter().find(|v| **v == arg);
                            // .expect(&format!("CANNOT FIND VALUE!!!!! {arg_name}\n{cond:?}"));
                            if let Some(var_in_this_block) = var_in_this_block {
                                let var = IRValue::Variable(**var_in_this_block);
                                if !false_args.contains(&var) {
                                    false_args.push(var);
                                }
                            } else {
                                eprintln!("false args: Missing var {arg_name}");
                                continue;
                            }
                        }
                    }
                    IRInstr::Goto(label, args) => {
                        // add all params of goto
                        //
                        let block = blocks_copy.iter().find(|b| b.name == *label).unwrap();

                        for arg in &block.parameters {
                            let arg_name = &self.vars[*arg].name;

                            // Ignore variables that are actually function names
                            if !self.func_names.contains(arg_name) {
                                let var_in_this_block = local_vars.iter().find(|v| **v == arg);
                                if var_in_this_block.is_none() {
                                    let label = label.clone();
                                    self.pretty_print_ssa();
                                    panic!("Cant find {arg} -- {arg_name}\n{label:?}");
                                }
                                let var = IRValue::Variable(**var_in_this_block.unwrap());
                                if !args.contains(&var) {
                                    args.push(var);
                                }
                            }
                        }
                    }
                    IRInstr::Return(irvalue) => {}
                    IRInstr::InlineTarget(_, _) => {}
                    IRInstr::Label(_) => unreachable!("There shouldnt be any labels at this point"),
                }
            }
        }
    }

    pub fn figure_out_block_params_for_func(&mut self, func_block_idx: usize) {
        self.build_partial_cf_graph(func_block_idx);

        let last_block_idx = self.blocks.len() - func_block_idx - 1;

        let mut ctx = ParamContext::default();

        self.figure_out_block_params(&mut ctx, func_block_idx, -1, &mut vec![], last_block_idx);
    }

    fn figure_out_block_params(
        &mut self,
        ctx: &mut ParamContext,
        func_block_idx: usize,
        prev_node: i32,
        unresolved_vars: &mut Vec<VariableID>,
        block_idx: usize,
    ) {
        let cf_graph = &mut self.cf_graph;
        let graph = &mut cf_graph.nodes;
        let dnode = graph.get(block_idx).unwrap();
        let cyclic = dnode.strongly_connected.clone();
        let dependencies = &dnode.dependencies.clone();

        if let Some(group_idx) = cyclic {
            // Part of a group of cyclic nodes
            if ctx
                .visits
                .contains(&(GraphFragment::CyclicGroup(group_idx), prev_node))
            {
                return;
            }
            // Mark the whole group as visited
            ctx.visits
                .push((GraphFragment::CyclicGroup(group_idx), prev_node));

            let group = cf_graph.strongly_conn[group_idx].clone();

            let mut visits = HashMap::new();
            for block_idx in &group {
                visits.insert(*block_idx, 0);
            }

            self.resolve_cycle_block_params(
                &group,
                ctx,
                func_block_idx,
                &mut unresolved_vars.clone(),
                &mut visits,
                block_idx,
            );

            let cycle_local_unresolved_vars = unresolved_vars.clone();

            for block_idx in &group {
                // Visit all dependencies outside of this cyclic group
                for dep in dependencies {
                    if group.contains(dep) {
                        continue;
                    }

                    let mut unresolved_copy = unresolved_vars.clone();
                    self.figure_out_block_params(
                        ctx,
                        func_block_idx,
                        *block_idx as i32,
                        &mut unresolved_copy,
                        *dep,
                    );

                    let curr_block = &mut self.blocks[func_block_idx + block_idx];
                    for unresolved in &cycle_local_unresolved_vars {
                        if !unresolved_copy.contains(unresolved) {
                            // prob unneeded if
                            if !curr_block.parameters.contains(&unresolved) {
                                curr_block.parameters.push(*unresolved);
                            }
                        }
                    }
                }
            }
        } else {
            // Single node, not cyclic
            if ctx
                .visits
                .contains(&(GraphFragment::SingleNode(block_idx), prev_node))
            {
                return;
            }
            // Mark node as visited
            ctx.visits
                .push((GraphFragment::SingleNode(block_idx), prev_node));

            // Figure out which params are needed from uninit vars
            let (mut foreign_vars, local_vars) =
                self.find_block_variables_and_update_lifespans(func_block_idx, block_idx);

            // Get remove newly discovered variables from unresolved_vars
            unresolved_vars.retain(|var| {
                let var_name = &self.vars[*var].name;
                for local in &local_vars {
                    let name = &self.vars[*local].name;
                    if *var_name == *name {
                        //contained
                        return false;
                    }
                }

                return true;
            });

            for param in unresolved_vars.iter() {
                if !foreign_vars.contains(&param) {
                    foreign_vars.push(param.clone());
                }
            }

            *unresolved_vars = foreign_vars.clone();

            // Add those params
            let block = &mut self.blocks[func_block_idx + block_idx];
            for param in foreign_vars {
                if !block.parameters.contains(&param) {
                    block.parameters.push(param);
                }
            }

            // Visit dependencies
            for dep in dependencies {
                self.figure_out_block_params(
                    ctx,
                    func_block_idx,
                    block_idx as i32,
                    &mut unresolved_vars.clone(),
                    *dep,
                );
            }
        }
    }

    fn find_block_variables_and_update_lifespans(
        &mut self,
        func_block_idx: usize,
        block_idx: usize,
        // Foreign, Locals
    ) -> (Vec<VariableID>, Vec<VariableID>) {
        let block_idx = func_block_idx + block_idx;
        let block = &self.blocks[block_idx];

        let mut local_vars = vec![];
        let mut new_params = vec![];

        fn contains_named_var(
            vars: &Vec<IRVariable>,
            local_vars: &Vec<VariableID>,
            var: &usize,
        ) -> bool {
            let var = &vars[*var];

            for local_var_id in local_vars {
                let local_var = &vars[*local_var_id];
                if local_var.name == var.name {
                    return true;
                }
            }

            return false;
        }

        // for param in &block.parameters {
        //     local_vars.push(*param);
        // }

        for (instr_idx, instr) in block.instructions.iter().enumerate() {
            match instr {
                IRInstr::Load(res, _) => {
                    local_vars.push(*res);
                    self.var_lifespans.extend_lifespan(
                        *res,
                        InstrIndex {
                            block_idx,
                            instr_idx,
                        },
                    );
                }
                IRInstr::Store(_, val) => {
                    if let IRValue::Variable(val) = val {
                        let contained = contains_named_var(&self.vars, &local_vars, &val);
                        if !contained {
                            // let name = self.ssa_ir.vars[*val].name.clone();
                            // let ty = self.ssa_ir.vars[*val].ty.clone();
                            // let param_id = self.named_var(&name, ty);
                            new_params.push(*val);
                        }

                        self.var_lifespans.extend_lifespan(
                            *val,
                            InstrIndex {
                                block_idx,
                                instr_idx,
                            },
                        );
                    }
                }
                IRInstr::Unimplemented(res, _) => {
                    local_vars.push(res.clone());
                    self.var_lifespans.extend_lifespan(
                        *res,
                        InstrIndex {
                            block_idx,
                            instr_idx,
                        },
                    );
                }
                IRInstr::Assign(res, irvalue) => {
                    local_vars.push(res.clone());
                    self.var_lifespans.extend_lifespan(
                        *res,
                        InstrIndex {
                            block_idx,
                            instr_idx,
                        },
                    );
                    if let IRValue::Variable(val) = irvalue {
                        let contained = contains_named_var(&self.vars, &local_vars, &val);
                        if !contained {
                            // let name = self.ssa_ir.vars[*val].name.clone();
                            // let ty = self.ssa_ir.vars[*val].ty.clone();
                            // let param_id = self.named_var(&name, ty);
                            new_params.push(*val);
                        }
                        self.var_lifespans.extend_lifespan(
                            *val,
                            InstrIndex {
                                block_idx,
                                instr_idx,
                            },
                        );
                    }
                }
                IRInstr::BinOp(res, irvalue, irvalue1, _) => {
                    local_vars.push(res.clone());
                    self.var_lifespans.extend_lifespan(
                        *res,
                        InstrIndex {
                            block_idx,
                            instr_idx,
                        },
                    );
                    if let IRValue::Variable(val) = irvalue {
                        let contained = contains_named_var(&self.vars, &local_vars, &val);
                        if !contained {
                            // let name = self.ssa_ir.vars[*val].name.clone();
                            // let ty = self.ssa_ir.vars[*val].ty.clone();
                            // let param_id = self.named_var(&name, ty);
                            new_params.push(*val);
                        }

                        self.var_lifespans.extend_lifespan(
                            *val,
                            InstrIndex {
                                block_idx,
                                instr_idx,
                            },
                        );
                    }

                    if let IRValue::Variable(val) = irvalue1 {
                        let contained = contains_named_var(&self.vars, &local_vars, &val);
                        if !contained {
                            // let name = self.ssa_ir.vars[*val].name.clone();
                            // let ty = self.ssa_ir.vars[*val].ty.clone();
                            // let param_id = self.named_var(&name, ty);
                            new_params.push(*val);
                        }
                        self.var_lifespans.extend_lifespan(
                            *val,
                            InstrIndex {
                                block_idx,
                                instr_idx,
                            },
                        );
                    }
                }
                IRInstr::UnOp(res, irvalue, unary_operation) => {
                    local_vars.push(res.clone());
                    self.var_lifespans.extend_lifespan(
                        *res,
                        InstrIndex {
                            block_idx,
                            instr_idx,
                        },
                    );
                    if let IRValue::Variable(val) = irvalue {
                        let contained = contains_named_var(&self.vars, &local_vars, &val);
                        if !contained {
                            // let name = self.ssa_ir.vars[*val].name.clone();
                            // let ty = self.ssa_ir.vars[*val].ty.clone();
                            // let param_id = self.named_var(&name, ty);
                            new_params.push(*val);
                        }
                        self.var_lifespans.extend_lifespan(
                            *val,
                            InstrIndex {
                                block_idx,
                                instr_idx,
                            },
                        );
                    }
                }
                IRInstr::Call(res, irvalue, args) => {
                    local_vars.push(res.clone());

                    self.var_lifespans.extend_lifespan(
                        *res,
                        InstrIndex {
                            block_idx,
                            instr_idx,
                        },
                    );
                    if let IRValue::Variable(called) = irvalue {
                        let var_name = &self.vars[*called].name;

                        // Dont act like a defined function is a new variable
                        if !self.func_names.contains(&var_name) {
                            let contained = contains_named_var(&self.vars, &local_vars, &called);
                            if !contained {
                                new_params.push(*called);
                            }

                            self.var_lifespans.extend_lifespan(
                                *called,
                                InstrIndex {
                                    block_idx,
                                    instr_idx,
                                },
                            );
                        }
                    }

                    for arg in args {
                        if let IRValue::Variable(val) = arg {
                            let contained = contains_named_var(&self.vars, &local_vars, &val);
                            if !contained {
                                // let name = self.ssa_ir.vars[*val].name.clone();
                                // let ty = self.ssa_ir.vars[*val].ty.clone();
                                // let param_id = self.named_var(&name, ty);
                                new_params.push(*val);
                            }
                            self.var_lifespans.extend_lifespan(
                                *val,
                                InstrIndex {
                                    block_idx,
                                    instr_idx,
                                },
                            );
                        }
                    }
                }
                IRInstr::If(cond, irvalue, true_label, true_args, false_label, false_args) => {
                    if let IRValue::Variable(val) = irvalue {
                        let contained = contains_named_var(&self.vars, &local_vars, &val);
                        if !contained {
                            // let name = self.ssa_ir.vars[*val].name.clone();
                            // let ty = self.ssa_ir.vars[*val].ty.clone();
                            // let param_id = self.named_var(&name, ty);
                            new_params.push(*val);
                        }
                        self.var_lifespans.extend_lifespan(
                            *val,
                            InstrIndex {
                                block_idx,
                                instr_idx,
                            },
                        );
                    }

                    // make sure goto params are also searched for potential new parameters (maybe fails for cyclic graphs)
                    let block_params = self
                        .blocks
                        .iter()
                        .filter(|b| b.name == *true_label || b.name == *false_label)
                        .flat_map(|b| &b.parameters)
                        .collect::<Vec<_>>();

                    for param in block_params {
                        let contained = contains_named_var(&self.vars, &local_vars, &param);
                        if !contained {
                            new_params.push(*param);
                        }
                        self.var_lifespans.extend_lifespan(
                            *param,
                            InstrIndex {
                                block_idx,
                                instr_idx,
                            },
                        );
                    }
                }
                IRInstr::Goto(label, args) => {
                    // make sure goto params are also searched for potential new parameters (maybe fails for cyclic graphs)
                    let block_params = self
                        .blocks
                        .iter()
                        .find(|b| b.name == *label)
                        .into_iter()
                        .flat_map(|b| &b.parameters)
                        .collect::<Vec<_>>();

                    for param in block_params {
                        let contained = contains_named_var(&self.vars, &local_vars, &param);
                        if !contained {
                            new_params.push(*param);
                        }
                        self.var_lifespans.extend_lifespan(
                            *param,
                            InstrIndex {
                                block_idx,
                                instr_idx,
                            },
                        );
                    }
                }
                IRInstr::Return(irvalue) => {
                    if let Some(IRValue::Variable(val)) = irvalue {
                        let contained = contains_named_var(&self.vars, &local_vars, &val);
                        if !contained {
                            // let name = self.ssa_ir.vars[*val].name.clone();
                            // let ty = self.ssa_ir.vars[*val].ty.clone();
                            // let param_id = self.named_var(&name, ty);
                            new_params.push(*val);
                        }
                        self.var_lifespans.extend_lifespan(
                            *val,
                            InstrIndex {
                                block_idx,
                                instr_idx,
                            },
                        );
                    }
                }
                IRInstr::InlineTarget(parts, _) => {
                    for part in parts {
                        match part {
                            InlineTargetPart::SSAIRVarRef(var) => {
                                let contained = contains_named_var(&self.vars, &local_vars, var);
                                if !contained {
                                    new_params.push(*var);
                                }

                                self.var_lifespans.extend_lifespan(
                                    *var,
                                    InstrIndex {
                                        block_idx,
                                        instr_idx,
                                    },
                                );
                            }
                            _ => {}
                        }
                    }
                }
                IRInstr::Label(_) => unreachable!("There shouldnt be any labels at this point"),
            }
        }

        return (new_params, local_vars);
    }

    fn resolve_cycle_block_params(
        &mut self,
        group: &Vec<usize>,
        ctx: &mut ParamContext,
        func_block_idx: usize,
        unresolved_vars: &mut Vec<VariableID>,
        visits: &mut HashMap<usize, usize>,
        block_idx: usize,
    ) {
        // man idk if this wont break
        // idk if this should be times 2.
        // maybe the minimum needed amount is just group.len(). I really dont know
        if visits[&block_idx] > group.len() * 2 {
            return;
        }

        // visit all nodes at least twice before ending
        if visits.values().all(|c| *c >= 2) {
            return;
        }

        // increment visits
        let curr_v = visits[&block_idx];
        let v = visits.get_mut(&block_idx).unwrap();
        *v = curr_v + 1;

        let (mut foreign_vars, local_vars) =
            self.find_block_variables_and_update_lifespans(func_block_idx, block_idx);

        let cf_graph = &mut self.cf_graph;
        let graph = &mut cf_graph.nodes;

        unresolved_vars.retain(|var| {
            let var_name = &self.vars[*var].name;
            for local in &local_vars {
                let name = &self.vars[*local].name;
                if var_name == name {
                    //contained
                    return false;
                }
            }

            return true;
        });

        for param in unresolved_vars.iter() {
            if !foreign_vars.contains(&param) {
                foreign_vars.push(param.clone());
            }
        }

        *unresolved_vars = foreign_vars.clone();

        // Add those params
        let block = &mut self.blocks[func_block_idx + block_idx];
        for param in foreign_vars {
            if !block.parameters.contains(&param) {
                block.parameters.push(param);
            }
        }

        let dnode = graph.get(block_idx).unwrap();
        let dependencies = dnode.dependencies.clone();

        // println!("{dependencies:?}");
        for dep in dependencies.iter() {
            if !group.contains(&dep) {
                continue;
            }
            // println!("{dep}");
            self.resolve_cycle_block_params(
                group,
                ctx,
                func_block_idx,
                unresolved_vars,
                // &mut local_unresolved_vars.clone(),
                visits,
                *dep,
            );
        }
    }

    pub fn build_partial_cf_graph(&mut self, func_block_idx: usize) {
        let mut cf_graph = CFGraph::default();
        let graph = &mut cf_graph.nodes;

        let blocks_by_name = self
            .blocks
            .iter()
            .enumerate()
            .skip(func_block_idx)
            .map(|(idx, b)| (b.name.clone(), idx - func_block_idx))
            .collect::<HashMap<String, usize>>();

        let len = self.blocks.len();
        // Create nodes
        for i in func_block_idx..len {
            let mut node = CFGraphNode::default();
            node.block_idx = i - func_block_idx;
            graph.insert(node);
        }

        // Fill in dependees and dependencies
        for i in func_block_idx..len {
            let block = &self.blocks[i];
            let curr_idx = i - func_block_idx;

            for instr in &block.instructions {
                match instr {
                    IRInstr::If(_, _, true_block, _, false_block, _) => {
                        let true_block_id = blocks_by_name.get(true_block).unwrap();

                        let true_block = graph.get_mut(*true_block_id).unwrap();
                        true_block.dependencies.push(curr_idx);

                        let this_block = graph.get_mut(curr_idx).unwrap();
                        this_block.dependees.push(*true_block_id);

                        let false_block_id = blocks_by_name.get(false_block).unwrap();
                        let false_block = graph.get_mut(*false_block_id).unwrap();
                        false_block.dependencies.push(curr_idx);
                        let this_block = graph.get_mut(curr_idx).unwrap();
                        this_block.dependees.push(*false_block_id);
                    }
                    IRInstr::Goto(block, _) => {
                        let goto_block_id = blocks_by_name.get(block).unwrap();

                        let goto_block = graph.get_mut(*goto_block_id).unwrap();
                        goto_block.dependencies.push(curr_idx);

                        let this_block = graph.get_mut(curr_idx).unwrap();
                        this_block.dependees.append(&mut vec![*goto_block_id]);
                    }
                    // other instructions dont reference different blocks
                    _ => {}
                }
            }
        }

        self.find_strongly_connected(&mut cf_graph);

        self.cf_graph = cf_graph;
    }

    fn find_strongly_connected(&mut self, cf_graph: &mut CFGraph) {
        let graph = &mut cf_graph.nodes;
        let mut num = vec![-1; graph.vec.len()];
        let mut lowest = vec![-1; graph.vec.len()];
        let mut visited = vec![false; graph.vec.len()];
        let mut processed = vec![false; graph.vec.len()];
        let mut s = Vec::new();
        let mut i = 0;

        let mut comps = vec![];

        let v_count = graph.vec.len();
        for v in 0..v_count {
            if !visited[v] {
                Self::strong_connect(
                    &mut num,
                    &mut lowest,
                    &mut visited,
                    &mut processed,
                    &mut s,
                    &mut i,
                    &mut comps,
                    cf_graph,
                    v,
                );
            }
        }

        cf_graph.strongly_conn = comps;
    }

    //https://www.baeldung.com/cs/scc-tarjans-algorithm
    fn strong_connect(
        num: &mut Vec<i32>,
        lowest: &mut Vec<i32>,
        visited: &mut Vec<bool>,
        processed: &mut Vec<bool>,
        s: &mut Vec<usize>,
        i: &mut i32,
        comps: &mut Vec<Vec<usize>>,
        cf_graph: &mut CFGraph,
        v: usize,
    ) {
        num[v] = *i;
        lowest[v] = num[v];
        *i = *i + 1;
        visited[v] = true;
        s.push(v);

        let node = cf_graph.nodes.get(v).unwrap();
        let successors = node.dependees.clone();
        for u in successors {
            if !visited[u] {
                Self::strong_connect(num, lowest, visited, processed, s, i, comps, cf_graph, u);
                lowest[v] = lowest[v].min(lowest[u]);
            } else if !processed[u] {
                lowest[v] = lowest[v].min(num[u]);
            }
        }

        processed[v] = true;

        if lowest[v] == num[v] {
            let mut scc = Vec::new();
            let mut scc_v = s.pop().unwrap();

            while scc_v != v {
                scc.push(scc_v);
                scc_v = s.pop().unwrap();
            }

            scc.push(scc_v);

            if scc.len() > 1 {
                comps.push(scc.clone());

                for v in &scc {
                    let node = cf_graph.nodes.get_mut(*v).unwrap();
                    node.strongly_connected = Some(comps.len() - 1);
                }
            }
        }
    }

    // -------------------------------------

    pub fn pretty_print_irval(&self, irval: &IRValue) -> String {
        match irval {
            IRValue::Address(address) => address.pretty_print(&self.vars),
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
                let addr = addr.pretty_print(&self.vars);
                format!("store {addr} {val}")
            }
            IRInstr::Load(var, addr) => {
                let variable = &self.vars[*var];
                let addr = addr.pretty_print(&self.vars);
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

        for (block_idx, block) in self.blocks.iter().enumerate() {
            println!("{}", self.pretty_print_block_name(block));
            println!("{}", self.pretty_print_block(block, block_idx));
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

    pub fn pretty_print_block(&self, block: &Block, block_idx: usize) -> String {
        let mut out = String::new();

        for (instr_idx, instr) in block.instructions.iter().enumerate() {
            let instr_idx = InstrIndex {
                block_idx,
                instr_idx,
            };
            let live_vars = self.var_lifespans.get_live_vars(instr_idx);
            let live_vars = live_vars
                .iter()
                .map(|v| self.vars[*v].name.clone())
                .collect::<Vec<_>>()
                .join(", ");

            let instr = self.pretty_print_instr(instr);
            // out += &format!("{}\t\t{instr}\n", "#".repeat(live_vars.len()))
            out += &format!("\t{instr:<40}\t{live_vars}\n")
        }

        out
    }
}
