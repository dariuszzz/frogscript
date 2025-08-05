use super::ssa_ir;
use std::{collections::HashMap, ptr::read};

use crate::{
    ast::{FunctionType, SymbolIdx},
    backend::ssa_ir::{IRData, IRDataLiteral, InlineTargetPart},
    lexer::FStringPart,
    pond::{Dependency, Target},
    ssa_ir::{Block, IRAddress, IRInstr, IRValue, IRVariable, VariableID, SSAIR},
    symbol_table::*,
    Arena, BinaryOperation, CodeBlock, Expression, Literal, Program, Type, Variable, VariableDecl,
};

#[derive(Default)]
pub struct LoopInfo {
    pub start_label: String,
    pub end_label: String,
}

#[derive(Default)]
pub struct IRGen {
    pub var_counter: u32,
    pub ssa_ir: SSAIR,
}

#[derive(Default, Debug, Clone)]
pub struct DTreeNode {
    pub dependencies: Vec<usize>,
    pub dependees: Vec<usize>,
    pub strongly_connected: Option<usize>,
}

type DependencyGraph = Arena<DTreeNode>;

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

impl IRGen {
    // fn get_type(&self, scope: &mut usize, symbol_table: &SymbolTable, expr: &Expression) {
    //     match expr {
    //         Expression::Variable(var) => symbol_table.scope,
    //     }
    //     symbol_table.scope_get_symbol(scope, name, symbol_type)
    // }

    fn temp_var(&mut self, ty: Type) -> usize {
        let temp_name = self.make_name_unique("_");
        self.ssa_ir.vars.push(IRVariable {
            name: temp_name,
            ty,
        });

        return self.ssa_ir.vars.len() - 1;
    }

    fn symbol_idx_to_name(symbol_idx: &SymbolIdx) -> String {
        format!("s{}i{}", symbol_idx.0, symbol_idx.1)
    }

    fn symbol_idx_to_var(&mut self, symbol_idx: &SymbolIdx, ty: Type) -> usize {
        let name = Self::symbol_idx_to_name(symbol_idx);
        self.ssa_ir.vars.push(IRVariable { name, ty });

        return self.ssa_ir.vars.len() - 1;
    }

    fn named_var(&mut self, name: &str, ty: Type) -> usize {
        self.ssa_ir.vars.push(IRVariable {
            name: name.to_string(),
            ty,
        });

        return self.ssa_ir.vars.len() - 1;
    }

    pub fn generate_ir(
        &mut self,
        program: Program,
        target: &Target,
        symbol_table: &SymbolTable,
    ) -> Result<SSAIR, String> {
        let mut scope = 0;

        for module in &program.modules {
            // self.generate_ir_codeblock(&mut scope, &module.toplevel_scope, symbol_table)?;

            for func in &module.function_defs {
                scope += 1;

                let name = Self::symbol_idx_to_name(&func.symbol_idx);

                self.ssa_ir.vars.push(IRVariable {
                    name: name.clone(),
                    ty: Type::Function(FunctionType {
                        env_args: vec![],
                        args: vec![], // TODO: ADD ARG PARAMS
                        ret: Box::new(func.return_type.clone()),
                    }),
                });

                let mut parameters = Vec::new();

                let mut renamed_vars = HashMap::new();

                for arg in &func.argument_list {
                    let arg_id = self.symbol_idx_to_var(&arg.symbol_idx, arg.arg_type.clone());
                    let var_name = self.ssa_ir.vars[arg_id].name.clone();
                    parameters.push(arg_id);
                    renamed_vars.insert(arg.arg_name.clone(), var_name);
                }

                self.ssa_ir.blocks.push(Block {
                    name,
                    parameters,
                    instructions: vec![],
                });
                let block_idx = self.ssa_ir.blocks.len() - 1;

                let instructions = self.generate_ir_codeblock(
                    &mut scope,
                    symbol_table,
                    &mut renamed_vars,
                    &LoopInfo::default(),
                    &func.function_body,
                )?;

                // these are the instructions before any label
                let remaining_instrs = self.split_labels_into_blocks(instructions);
                let block = self.ssa_ir.blocks.get_mut(block_idx).unwrap();
                block.instructions = remaining_instrs;

                // Deletes unreachable instructions in all blocks belonging to this func
                self.prune_all_instructions_after_first_branch(block_idx);

                self.figure_out_block_params_for_func(block_idx);
            }

            scope += 1;
        }

        Ok(self.ssa_ir.clone())
    }

    fn build_fn_dependency_graph(&mut self, func_block_idx: usize) -> DependencyGraph {
        let mut graph: DependencyGraph = Arena::new();

        let blocks_by_name = self
            .ssa_ir
            .blocks
            .iter()
            .enumerate()
            .skip(func_block_idx)
            .map(|(idx, b)| (b.name.clone(), idx - func_block_idx))
            .collect::<HashMap<String, usize>>();

        let len = self.ssa_ir.blocks.len();
        // Create nodes
        for i in func_block_idx..len {
            let node = DTreeNode::default();
            graph.insert(node);
        }

        // Fill in dependees and dependencies
        for i in func_block_idx..len {
            let block = &self.ssa_ir.blocks[i];
            let curr_idx = i - func_block_idx;

            for instr in &block.instructions {
                match instr {
                    IRInstr::If(_, true_block, _, false_block, _) => {
                        let true_block_id = blocks_by_name.get(true_block).unwrap();
                        let false_block_id = blocks_by_name.get(false_block).unwrap();

                        let true_block = graph.get_mut(*true_block_id).unwrap();
                        true_block.dependencies.push(curr_idx);

                        let false_block = graph.get_mut(*false_block_id).unwrap();
                        false_block.dependencies.push(curr_idx);

                        let this_block = graph.get_mut(curr_idx).unwrap();
                        this_block
                            .dependees
                            .append(&mut vec![*true_block_id, *false_block_id]);
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

        return graph;
    }

    fn find_block_variables(
        &mut self,
        func_block_idx: usize,
        block_idx: usize,
        // Foreign, Locals
    ) -> (Vec<VariableID>, Vec<VariableID>) {
        let block = &self.ssa_ir.blocks[func_block_idx + block_idx];

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

        for param in &block.parameters {
            local_vars.push(*param);
        }

        for instr in &block.instructions {
            match instr {
                IRInstr::Load(res, _) => {
                    local_vars.push(*res);
                }
                IRInstr::Store(_, val) => {
                    if let IRValue::Variable(val) = val {
                        let contained = contains_named_var(&self.ssa_ir.vars, &local_vars, &val);
                        if !contained {
                            // let name = self.ssa_ir.vars[*val].name.clone();
                            // let ty = self.ssa_ir.vars[*val].ty.clone();
                            // let param_id = self.named_var(&name, ty);
                            new_params.push(*val);
                        }
                    }
                }
                IRInstr::Unimplemented(res, _) => {
                    local_vars.push(res.clone());
                }
                IRInstr::Assign(res, irvalue) => {
                    local_vars.push(res.clone());
                    if let IRValue::Variable(val) = irvalue {
                        let contained = contains_named_var(&self.ssa_ir.vars, &local_vars, &val);
                        if !contained {
                            // let name = self.ssa_ir.vars[*val].name.clone();
                            // let ty = self.ssa_ir.vars[*val].ty.clone();
                            // let param_id = self.named_var(&name, ty);
                            new_params.push(*val);
                        }
                    }
                }
                IRInstr::BinOp(res, irvalue, irvalue1, _) => {
                    local_vars.push(res.clone());
                    if let IRValue::Variable(val) = irvalue {
                        let contained = contains_named_var(&self.ssa_ir.vars, &local_vars, &val);
                        if !contained {
                            // let name = self.ssa_ir.vars[*val].name.clone();
                            // let ty = self.ssa_ir.vars[*val].ty.clone();
                            // let param_id = self.named_var(&name, ty);
                            new_params.push(*val);
                        }
                    }

                    if let IRValue::Variable(val) = irvalue1 {
                        let contained = contains_named_var(&self.ssa_ir.vars, &local_vars, &val);
                        if !contained {
                            // let name = self.ssa_ir.vars[*val].name.clone();
                            // let ty = self.ssa_ir.vars[*val].ty.clone();
                            // let param_id = self.named_var(&name, ty);
                            new_params.push(*val);
                        }
                    }
                }
                IRInstr::UnOp(res, irvalue, unary_operation) => {
                    local_vars.push(res.clone());
                    if let IRValue::Variable(val) = irvalue {
                        let contained = contains_named_var(&self.ssa_ir.vars, &local_vars, &val);
                        if !contained {
                            // let name = self.ssa_ir.vars[*val].name.clone();
                            // let ty = self.ssa_ir.vars[*val].ty.clone();
                            // let param_id = self.named_var(&name, ty);
                            new_params.push(*val);
                        }
                    }
                }
                IRInstr::Call(res, irvalue, args) => {
                    local_vars.push(res.clone());
                    for arg in args {
                        if let IRValue::Variable(val) = arg {
                            let contained =
                                contains_named_var(&self.ssa_ir.vars, &local_vars, &val);
                            if !contained {
                                // let name = self.ssa_ir.vars[*val].name.clone();
                                // let ty = self.ssa_ir.vars[*val].ty.clone();
                                // let param_id = self.named_var(&name, ty);
                                new_params.push(*val);
                            }
                        }
                    }
                }
                IRInstr::If(irvalue, true_label, true_args, false_label, false_args) => {
                    if let IRValue::Variable(val) = irvalue {
                        let contained = contains_named_var(&self.ssa_ir.vars, &local_vars, &val);
                        if !contained {
                            // let name = self.ssa_ir.vars[*val].name.clone();
                            // let ty = self.ssa_ir.vars[*val].ty.clone();
                            // let param_id = self.named_var(&name, ty);
                            new_params.push(*val);
                        }
                    }
                }
                IRInstr::Goto(label, args) => {}
                IRInstr::Return(irvalue) => {
                    if let IRValue::Variable(val) = irvalue {
                        let contained = contains_named_var(&self.ssa_ir.vars, &local_vars, &val);
                        if !contained {
                            // let name = self.ssa_ir.vars[*val].name.clone();
                            // let ty = self.ssa_ir.vars[*val].ty.clone();
                            // let param_id = self.named_var(&name, ty);
                            new_params.push(*val);
                        }
                    }
                }
                IRInstr::InlineTarget(_, _) => {}
                IRInstr::Label(_) => unreachable!("There shouldnt be any labels at this point"),
            }
        }
        // println!(
        //     "New ({}): {}",
        //     block.name,
        //     new_params
        //         .iter()
        //         .map(|param| self.ssa_ir.vars[*param].name.clone())
        //         .collect::<Vec<_>>()
        //         .join(", ")
        // );

        // println!(
        //     "Locals ({}): {}",
        //     block.name,
        //     local_vars
        //         .iter()
        //         .map(|param| self.ssa_ir.vars[*param].name.clone())
        //         .collect::<Vec<_>>()
        //         .join(", ")
        // );

        return (new_params, local_vars);
    }

    fn resolve_cycle_block_params(
        &mut self,
        group: &Vec<usize>,
        graph: &mut DependencyGraph,
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

        // visit all nodes at least twice before endin
        if visits.values().all(|c| *c >= 2) {
            return;
        }

        // increment visits
        let curr_v = visits[&block_idx];
        let v = visits.get_mut(&block_idx).unwrap();
        *v = curr_v + 1;

        let (mut foreign_vars, local_vars) = self.find_block_variables(func_block_idx, block_idx);

        unresolved_vars.retain(|var| {
            let var_name = &self.ssa_ir.vars[*var].name;
            for local in &local_vars {
                let name = &self.ssa_ir.vars[*local].name;
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
        let block = &mut self.ssa_ir.blocks[func_block_idx + block_idx];
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
                graph,
                ctx,
                func_block_idx,
                unresolved_vars,
                // &mut local_unresolved_vars.clone(),
                visits,
                *dep,
            );
        }
    }

    fn figure_out_block_params(
        &mut self,
        graph: &mut DependencyGraph,
        ctx: &mut ParamContext,
        func_block_idx: usize,
        prev_node: i32,
        unresolved_vars: &mut Vec<VariableID>,
        comps: &Vec<Vec<usize>>,
        block_idx: usize,
    ) {
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

            let group = comps[group_idx].clone();

            let mut visits = HashMap::new();
            for block_idx in &group {
                visits.insert(*block_idx, 0);
            }

            let mut cycle_local_unresolved_vars = unresolved_vars.clone();
            self.resolve_cycle_block_params(
                &group,
                graph,
                ctx,
                func_block_idx,
                &mut unresolved_vars.clone(),
                &mut visits,
                block_idx,
            );

            for block_idx in &group {
                // Visit all dependencies outside of this cyclic group
                for dep in dependencies {
                    if group.contains(dep) {
                        continue;
                    }

                    self.figure_out_block_params(
                        graph,
                        ctx,
                        func_block_idx,
                        *block_idx as i32,
                        &mut unresolved_vars.clone(),
                        comps,
                        *dep,
                    );
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
                self.find_block_variables(func_block_idx, block_idx);

            // Get remove newly discovered variables from unresolved_vars
            unresolved_vars.retain(|var| {
                let var_name = &self.ssa_ir.vars[*var].name;
                for local in &local_vars {
                    let name = &self.ssa_ir.vars[*local].name;
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
            let block = &mut self.ssa_ir.blocks[func_block_idx + block_idx];
            for param in foreign_vars {
                if !block.parameters.contains(&param) {
                    block.parameters.push(param);
                }
            }

            // Visit dependencies
            for dep in dependencies {
                self.figure_out_block_params(
                    graph,
                    ctx,
                    func_block_idx,
                    block_idx as i32,
                    &mut unresolved_vars.clone(),
                    comps,
                    *dep,
                );
            }
        }
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
        graph: &mut DependencyGraph,
        v: usize,
    ) {
        num[v] = *i;
        lowest[v] = num[v];
        *i = *i + 1;
        visited[v] = true;
        s.push(v);

        let node = graph.get(v).unwrap();
        let successors = node.dependees.clone();
        for u in successors {
            if !visited[u] {
                Self::strong_connect(num, lowest, visited, processed, s, i, comps, graph, u);
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
                    let node = graph.get_mut(*v).unwrap();
                    node.strongly_connected = Some(comps.len() - 1);
                }
            }
        }
    }

    fn find_strongly_connected(&mut self, graph: &mut DependencyGraph) -> Vec<Vec<usize>> {
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
                    graph,
                    v,
                );
            }
        }

        comps
    }

    fn figure_out_block_params_for_func(&mut self, func_block_idx: usize) {
        let mut dependency_graph = self.build_fn_dependency_graph(func_block_idx);
        let strongly_connected_comps = self.find_strongly_connected(&mut dependency_graph);

        let last_block_idx = self.ssa_ir.blocks.len() - func_block_idx - 1;

        let mut ctx = ParamContext::default();

        self.figure_out_block_params(
            &mut dependency_graph,
            &mut ctx,
            func_block_idx,
            -1,
            &mut vec![],
            &strongly_connected_comps,
            last_block_idx,
        );

        self.fix_passing_parameters_by_gotos(func_block_idx);
    }

    fn fix_passing_parameters_by_gotos(&mut self, func_block_idx: usize) {
        let len = self.ssa_ir.blocks.len();

        let block_copies = self.ssa_ir.blocks.clone();

        for idx in func_block_idx..len {
            let block = &mut self.ssa_ir.blocks[idx];
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
                    IRInstr::If(irvalue, true_label, true_args, false_label, false_args) => {
                        // add all params of branches
                        let true_block =
                            block_copies.iter().find(|b| b.name == *true_label).unwrap();

                        for arg in &true_block.parameters {
                            let var_in_this_block = local_vars.iter().find(|v| **v == arg).unwrap();
                            true_args.push(IRValue::Variable(**var_in_this_block));
                        }

                        let false_block = block_copies
                            .iter()
                            .find(|b| b.name == *false_label)
                            .unwrap();

                        for arg in &false_block.parameters {
                            let var_in_this_block = local_vars.iter().find(|v| **v == arg).unwrap();
                            false_args.push(IRValue::Variable(**var_in_this_block));
                        }
                    }
                    IRInstr::Goto(label, args) => {
                        // add all params of goto
                        //
                        let block = block_copies.iter().find(|b| b.name == *label).unwrap();

                        for arg in &block.parameters {
                            let var_in_this_block = local_vars.iter().find(|v| **v == arg).unwrap();
                            args.push(IRValue::Variable(**var_in_this_block));
                        }
                    }
                    IRInstr::Return(irvalue) => {}
                    IRInstr::InlineTarget(_, _) => {}
                    IRInstr::Label(_) => unreachable!("There shouldnt be any labels at this point"),
                }
            }
        }
    }

    fn prune_all_instructions_after_first_branch(&mut self, func_block_idx: usize) {
        let len = self.ssa_ir.blocks.len();
        for block_idx in func_block_idx..len {
            let block = &mut self.ssa_ir.blocks[block_idx];
            let mut instructions = Vec::new();

            for instr in block.instructions.clone() {
                match instr {
                    instr @ IRInstr::Goto(_, _) | instr @ IRInstr::If(_, _, _, _, _) => {
                        instructions.push(instr);
                        break;
                    }
                    instr => instructions.push(instr),
                }
            }

            block.instructions = instructions;
        }
    }

    fn split_labels_into_blocks(&mut self, instructions: Vec<IRInstr>) -> Vec<IRInstr> {
        let mut ret_instrs = vec![];
        let mut curr_block = None;

        for instr in instructions {
            match instr {
                IRInstr::Label(label) => {
                    if let Some(curr_block) = curr_block {
                        self.ssa_ir.blocks.push(curr_block);
                    }

                    curr_block = Some(Block {
                        name: label,
                        parameters: vec![],
                        instructions: vec![],
                    })
                }
                instr => {
                    if let Some(curr_block) = &mut curr_block {
                        curr_block.instructions.push(instr.clone());
                    } else {
                        ret_instrs.push(instr);
                    }
                }
            }
        }

        if let Some(curr_block) = curr_block {
            self.ssa_ir.blocks.push(curr_block);
        }

        return ret_instrs;
    }

    pub fn generate_ir_codeblock(
        &mut self,
        scope: &mut usize,
        symbol_table: &SymbolTable,
        renamed_vars: &mut HashMap<String, String>,
        loop_info: &LoopInfo,
        codeblock: &CodeBlock,
    ) -> Result<Vec<IRInstr>, String> {
        let mut instructions = Vec::new();

        for expr in &codeblock.expressions {
            let (res_var, mut instrs) =
                self.generate_ir_expr(scope, symbol_table, renamed_vars, loop_info, &expr)?;
            instructions.append(&mut instrs);
        }

        Ok(instructions)
    }

    pub fn generate_ir_expr(
        &mut self,
        scope: &mut usize,
        symbol_table: &SymbolTable,
        renamed_vars: &mut HashMap<String, String>,
        loop_info: &LoopInfo,
        expr: &Expression,
    ) -> Result<(IRValue, Vec<IRInstr>), String> {
        let mut instructions = Vec::new();

        match expr {
            Expression::VariableDecl(variable_decl) => {
                let var_id = self
                    .symbol_idx_to_var(&variable_decl.symbol_idx, variable_decl.var_type.clone());
                let var_name = self.ssa_ir.vars[var_id].name.clone();

                let (value, mut instrs) = self.generate_ir_expr(
                    scope,
                    symbol_table,
                    renamed_vars,
                    loop_info,
                    &variable_decl.var_value,
                )?;

                renamed_vars.insert(variable_decl.var_name.clone(), var_name.clone());

                instructions.append(&mut instrs);

                instructions.push(IRInstr::Assign(var_id, value));

                return Ok((IRValue::Variable(var_id), instructions));
            }
            Expression::Literal(literal) => {
                let value = match literal {
                    Literal::String(parts) => {
                        if parts.len() != 1 {
                            unimplemented!("FStrings not supported yet")
                        }

                        if let FStringPart::String(str) = &parts[0] {
                            let var_id = self.temp_var(Type::String);
                            let alias = format!("str{}", self.ssa_ir.data.len());

                            self.ssa_ir.data.push(IRData {
                                alias: alias.clone(),
                                value: IRDataLiteral::String(str.clone()),
                            });

                            instructions.push(IRInstr::Load(
                                var_id,
                                IRAddress {
                                    addr: alias,
                                    offset: 0,
                                },
                            ));

                            IRValue::Variable(var_id)
                        } else {
                            unimplemented!("FStrings not supported yet")
                        }
                    }
                    Literal::Float(float) => {
                        let var_id = self.temp_var(Type::String);
                        let alias = format!("fl{}", self.ssa_ir.data.len());

                        self.ssa_ir.data.push(IRData {
                            alias: alias.clone(),
                            value: IRDataLiteral::Float(*float),
                        });

                        instructions.push(IRInstr::Load(
                            var_id,
                            IRAddress {
                                addr: alias,
                                offset: 0,
                            },
                        ));

                        IRValue::Variable(var_id)
                    }
                    lit @ Literal::Int(_) | lit @ Literal::Uint(_) | lit @ Literal::Boolean(_) => {
                        IRValue::Literal(lit.clone())
                    }
                    _ => unimplemented!(),
                };

                return Ok((value, instructions));
            }
            Expression::BinaryOp(binary_op) => {
                let (lhs, mut lhs_instrs) = self.generate_ir_expr(
                    scope,
                    symbol_table,
                    renamed_vars,
                    loop_info,
                    &binary_op.lhs,
                )?;
                let (rhs, mut rhs_instrs) = self.generate_ir_expr(
                    scope,
                    symbol_table,
                    renamed_vars,
                    loop_info,
                    &binary_op.rhs,
                )?;

                instructions.append(&mut lhs_instrs);
                instructions.append(&mut rhs_instrs);

                let var_id = self.temp_var(lhs.ty());
                instructions.push(IRInstr::BinOp(var_id, lhs.clone(), rhs, binary_op.op));

                return Ok((IRValue::Variable(var_id), instructions));
            }
            Expression::UnaryOp(unary_op) => {
                let (operand, mut operand_instrs) = self.generate_ir_expr(
                    scope,
                    symbol_table,
                    renamed_vars,
                    loop_info,
                    &unary_op.operand,
                )?;

                instructions.append(&mut operand_instrs);

                let var_id = self.temp_var(operand.ty());
                instructions.push(IRInstr::UnOp(var_id, operand.clone(), unary_op.op));

                return Ok((IRValue::Variable(var_id), instructions));
            }
            Expression::FunctionCall(function_call) => {
                let (mut func_expr, mut func_instrs) = self.generate_ir_expr(
                    scope,
                    symbol_table,
                    renamed_vars,
                    loop_info,
                    &function_call.func_expr,
                )?;

                // if let IRValue::IRVariable(func) = &mut func_expr {
                // let func_symbol = symbol_table
                //     .get_scope(func.symbol_idx.0)
                //     .unwrap()
                //     .symbols
                //     .get(func.symbol_idx.1)
                //     .unwrap();

                // func.name = func_symbol.qualified_name.clone();
                // }

                instructions.append(&mut func_instrs);

                let mut args = vec![];
                for arg in &function_call.arguments {
                    let (arg_expr, mut arg_instrs) =
                        self.generate_ir_expr(scope, symbol_table, renamed_vars, loop_info, &arg)?;

                    instructions.append(&mut arg_instrs);

                    args.push(arg_expr);
                }

                // TODO: this should have the return type as type
                let var_id = self.temp_var(func_expr.ty());
                instructions.push(IRInstr::Call(var_id, func_expr.clone(), args));

                return Ok((IRValue::Variable(var_id), instructions));
            }
            Expression::Variable(variable) => {
                let name_to_find = if let Some(replaced_name) = renamed_vars.get(&variable.name) {
                    replaced_name
                } else {
                    &Self::symbol_idx_to_name(&variable.symbol_idx)
                };

                for (idx, var) in self.ssa_ir.vars.iter().enumerate() {
                    if var.name == *name_to_find {
                        return Ok((IRValue::Variable(idx), instructions));
                    }
                }

                unreachable!("{name_to_find}, {}", variable.name)
            }
            Expression::Return(expression) => {
                let (ret_expr, mut ret_instrs) = self.generate_ir_expr(
                    scope,
                    symbol_table,
                    renamed_vars,
                    loop_info,
                    &expression,
                )?;

                instructions.append(&mut ret_instrs);
                instructions.push(IRInstr::Return(ret_expr));

                return Ok((IRValue::Literal(Literal::Int(0)), instructions));
            }
            Expression::Assignment(assignment) => {
                let (lhs, mut lhs_instrs) = self.generate_ir_expr(
                    scope,
                    symbol_table,
                    renamed_vars,
                    loop_info,
                    &assignment.lhs,
                )?;
                let (rhs, mut rhs_instrs) = self.generate_ir_expr(
                    scope,
                    symbol_table,
                    renamed_vars,
                    loop_info,
                    &assignment.rhs,
                )?;

                instructions.append(&mut lhs_instrs);
                instructions.append(&mut rhs_instrs);

                if let IRValue::Variable(var) = lhs.clone() {
                    let old_var_name = self.ssa_ir.vars[var].name.clone();
                    let original_name = old_var_name.split("#").next().unwrap();
                    let var_id = self.named_var(&original_name, lhs.ty());
                    let new_var_name = self.ssa_ir.vars[var_id].name.clone();

                    instructions.push(IRInstr::Assign(var_id, rhs));
                    renamed_vars.insert(original_name.to_string(), new_var_name);
                } else {
                    panic!("Assignment to literal?, {lhs:?}");
                }

                return Ok((IRValue::Literal(Literal::Int(0)), instructions));
            }
            Expression::AnonStruct(anon_struct) => {
                let var_id = self.temp_var(Type::Any);
                return Ok((
                    IRValue::Variable(var_id),
                    vec![IRInstr::Unimplemented(var_id, format!("Anon struct"))],
                ));
            }
            Expression::ArrayLiteral(array_literal) => {
                let mut inner_ty = Type::Any;

                let initial_offset = 0;
                let mut offset = initial_offset;

                for el in &array_literal.elements {
                    let (el, mut el_instrs) =
                        self.generate_ir_expr(scope, symbol_table, renamed_vars, loop_info, &el)?;

                    inner_ty = el.ty();

                    instructions.append(&mut el_instrs);
                    instructions.push(IRInstr::Store(
                        IRAddress {
                            addr: "$stack$".to_string(),
                            offset,
                        },
                        el,
                    ));

                    match inner_ty {
                        Type::Int => offset += 4,
                        _ => {}
                    }
                }

                let var_id = self.temp_var(Type::Array(Box::new(inner_ty)));
                instructions.push(IRInstr::Assign(
                    var_id,
                    IRValue::Address(IRAddress {
                        addr: "$stack$".to_string(),
                        offset: 0,
                    }),
                ));

                return Ok((IRValue::Variable(var_id), instructions));
            }
            Expression::ArrayAccess(array_access) => {
                let (index, mut index_instrs) = self.generate_ir_expr(
                    scope,
                    symbol_table,
                    renamed_vars,
                    loop_info,
                    &array_access.index,
                )?;

                let (expr, mut expr_instrs) = self.generate_ir_expr(
                    scope,
                    symbol_table,
                    renamed_vars,
                    loop_info,
                    &array_access.expr,
                )?;

                instructions.append(&mut index_instrs);
                instructions.append(&mut expr_instrs);

                let idx_var = self.temp_var(index.ty());
                let expr_var = self.temp_var(expr.ty());
                let res_var = self.temp_var(Type::Uint);

                let expr_name = &self.ssa_ir.vars[expr_var].name;
                let idx_name = &self.ssa_ir.vars[idx_var].name;

                instructions.push(IRInstr::Assign(idx_var, index));
                instructions.push(IRInstr::Assign(expr_var, expr));

                instructions.push(IRInstr::Load(
                    res_var,
                    IRAddress {
                        addr: format!("{expr_name} + {idx_name}"),
                        offset: 0,
                    },
                ));

                return Ok((IRValue::Variable(res_var), instructions));
            }
            Expression::FieldAccess(field_access) => {
                let res = self.temp_var(Type::Any);
                return Ok((
                    IRValue::Variable(res),
                    vec![IRInstr::Unimplemented(res, format!("Field access"))],
                ));
            }
            Expression::NamedStruct(named_struct) => {
                let res = self.temp_var(Type::Any);
                return Ok((
                    IRValue::Variable(res),
                    vec![IRInstr::Unimplemented(res, format!("Named struct"))],
                ));
            }
            Expression::Lambda(lambda) => {
                let res = self.temp_var(Type::Any);
                return Ok((
                    IRValue::Variable(res),
                    vec![IRInstr::Unimplemented(res, format!("Lambda"))],
                ));
            }
            Expression::Range(range) => {
                let res = self.temp_var(Type::Any);
                return Ok((
                    IRValue::Variable(res),
                    vec![IRInstr::Unimplemented(res, format!("Range"))],
                ));
            }
            Expression::BuiltinTarget(expr) => {
                let res = self.temp_var(Type::Any);

                let mut instrs_parts = Vec::new();
                if let Expression::Literal(Literal::String(parts)) = expr.as_ref() {
                    for part in parts {
                        let part = match part {
                            // TODO: this doesnt work if expr is an if or a for since js doesnt support that
                            FStringPart::Code(expr) => {
                                let (expr, mut instrs) = self.generate_ir_expr(
                                    scope,
                                    symbol_table,
                                    renamed_vars,
                                    loop_info,
                                    &expr,
                                )?;

                                if let IRValue::Variable(var) = expr {
                                    InlineTargetPart::SSA_IR_Var_Ref(var)
                                } else {
                                    unreachable!()
                                }
                            }
                            FStringPart::String(string) => {
                                InlineTargetPart::String(string.clone().replace("\\", ""))
                            }
                        };
                        instrs_parts.push(part);
                    }
                }

                let mut used_registers = Vec::new();
                let last_part = instrs_parts.last_mut().unwrap();
                if let InlineTargetPart::String(end) = last_part {
                    let split: Vec<_> = end.split("|").collect();

                    let first_half = split[0].to_string();
                    let used_regs_text = split[1];

                    used_registers = used_regs_text
                        .split(" ")
                        .map(|s| s.trim().to_string())
                        .collect();

                    *end = first_half;
                }

                return Ok((
                    IRValue::Variable(res),
                    vec![IRInstr::InlineTarget(instrs_parts, used_registers)],
                ));
            }
            Expression::BuiltinType(expression) => {
                unreachable!("I think");
                let res = self.temp_var(Type::Any);
                return Ok((
                    IRValue::Variable(res),
                    vec![IRInstr::Unimplemented(res, format!("@type"))],
                ));
            }
            Expression::If(if_stmt) => {
                let (cond_expr, mut cond_instrs) = self.generate_ir_expr(
                    scope,
                    symbol_table,
                    renamed_vars,
                    loop_info,
                    &if_stmt.cond,
                )?;

                instructions.append(&mut cond_instrs);

                let after_if_label_name = self.make_name_unique("merge");
                let true_branch_label_name = self.make_name_unique("true");
                let false_branch_label_name = self.make_name_unique("false");

                // here if instr
                instructions.push(IRInstr::If(
                    cond_expr,
                    true_branch_label_name.clone(),
                    vec![],
                    if if_stmt.else_branch.is_some() {
                        false_branch_label_name.clone()
                    } else {
                        after_if_label_name.clone()
                    },
                    vec![],
                ));

                instructions.push(IRInstr::Label(true_branch_label_name));

                let mut true_branch_instrs = self.generate_ir_codeblock(
                    scope,
                    symbol_table,
                    &mut renamed_vars.clone(),
                    loop_info,
                    &if_stmt.true_branch,
                )?;

                instructions.append(&mut true_branch_instrs);
                instructions.push(IRInstr::Goto(after_if_label_name.clone(), vec![]));

                if let Some(else_branch) = &if_stmt.else_branch {
                    instructions.push(IRInstr::Label(false_branch_label_name));

                    let mut false_branch_instrs = self.generate_ir_codeblock(
                        scope,
                        symbol_table,
                        &mut renamed_vars.clone(),
                        loop_info,
                        else_branch,
                    )?;

                    instructions.append(&mut false_branch_instrs);
                    instructions.push(IRInstr::Goto(after_if_label_name.clone(), vec![]));
                }
                instructions.push(IRInstr::Label(after_if_label_name));

                return Ok((IRValue::Literal(Literal::Int(0)), instructions));
            }
            Expression::For(for_expr) => {
                let loop_cond_label = self.make_name_unique("loop_cond");
                let loop_body_label = self.make_name_unique("loop_body");
                let loop_end_label = self.make_name_unique("loop_end");
                instructions.push(IRInstr::Goto(loop_cond_label.clone(), vec![]));
                instructions.push(IRInstr::Label(loop_cond_label.clone()));

                let (iterator_expr, mut iterator_instrs) = self.generate_ir_expr(
                    scope,
                    symbol_table,
                    renamed_vars,
                    loop_info,
                    &for_expr.iterator,
                )?;

                let binding_var_id =
                    self.symbol_idx_to_var(&for_expr.symbol_idx, iterator_expr.ty());
                let binding_var_name = self.ssa_ir.vars[binding_var_id].name.clone();
                renamed_vars.insert(for_expr.binding.clone(), binding_var_name);

                instructions.append(&mut iterator_instrs);
                instructions.push(IRInstr::Assign(binding_var_id, iterator_expr.clone()));
                // instructions for condition checking here...
                //
                //  ---
                instructions.push(IRInstr::If(
                    iterator_expr,
                    loop_body_label.clone(),
                    vec![],
                    loop_end_label.clone(),
                    vec![],
                ));
                instructions.push(IRInstr::Label(loop_body_label.clone()));

                let mut loop_body = self.generate_ir_codeblock(
                    scope,
                    symbol_table,
                    &mut renamed_vars.clone(),
                    &LoopInfo {
                        start_label: loop_cond_label.clone(),
                        end_label: loop_end_label.clone(),
                    },
                    &for_expr.body,
                )?;
                instructions.append(&mut loop_body);

                instructions.push(IRInstr::Goto(loop_cond_label.clone(), vec![]));
                instructions.push(IRInstr::Label(loop_end_label.clone()));

                return Ok((IRValue::Literal(Literal::Int(0)), instructions));
            }
            Expression::Import(import) => {
                return Ok((IRValue::Literal(Literal::Int(0)), instructions));
            }
            Expression::Placeholder => {
                return Ok((IRValue::Literal(Literal::Int(0)), instructions));
            }
            Expression::Break => {
                instructions.push(IRInstr::Goto(loop_info.end_label.clone(), vec![]));
                return Ok((IRValue::Literal(Literal::Int(0)), instructions));
            }
            Expression::Continue => {
                instructions.push(IRInstr::Goto(loop_info.start_label.clone(), vec![]));
                return Ok((IRValue::Literal(Literal::Int(0)), instructions));
            }
        }
    }

    fn make_name_unique(&mut self, smth: &str) -> String {
        let res = format!("{smth}#{}", self.var_counter);
        self.var_counter += 1;

        return res;
    }
}
