use std::{collections::HashMap, ptr::read};

use crate::{
    pond::{Dependency, Target},
    ssa_ir::{Block, BlockParameter, IRInstr, IRValue, IRVariable, SSAIR},
    symbol_table::SymbolTable,
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
    pub label_counter: u32,
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

    pub fn generate_ir(
        &mut self,
        program: Program,
        target: &Target,
        symbol_table: &SymbolTable,
    ) -> Result<SSAIR, String> {
        let mut ssa_ir = SSAIR::default();
        let mut scope = 0;

        for module in &program.modules {
            // self.generate_ir_codeblock(&mut scope, &module.toplevel_scope, symbol_table)?;

            for func in &module.function_defs {
                scope += 1;

                let mut parameters = Vec::new();

                for arg in &func.argument_list {
                    parameters.push(BlockParameter {
                        name: arg.arg_name.clone(),
                        ty: arg.arg_type.clone(),
                    });
                }

                let func_symbol = symbol_table
                    .get_scope(func.symbol_idx.0)
                    .unwrap()
                    .symbols
                    .get(func.symbol_idx.1)
                    .unwrap();

                ssa_ir.blocks.push(Block {
                    name: func_symbol.qualified_name.clone(),
                    parameters,
                    instructions: vec![],
                });
                let block_idx = ssa_ir.blocks.len() - 1;

                let instructions = self.generate_ir_codeblock(
                    &mut scope,
                    &mut ssa_ir,
                    symbol_table,
                    &mut HashMap::new(),
                    &LoopInfo::default(),
                    &func.function_body,
                )?;

                // these are the instructions before any label
                let remaining_instrs = Self::split_labels_into_blocks(&mut ssa_ir, instructions);
                let block = ssa_ir.blocks.get_mut(block_idx).unwrap();
                block.instructions = remaining_instrs;

                // Deletes unreachable instructions in all blocks belonging to this func
                self.prune_all_instructions_after_first_branch(&mut ssa_ir, block_idx);

                self.figure_out_block_params_for_func(&mut ssa_ir, block_idx);
            }

            scope += 1;
        }

        println!("{ssa_ir}");

        Ok(ssa_ir)
    }

    fn build_fn_dependency_graph(
        &mut self,
        ssa: &mut SSAIR,
        func_block_idx: usize,
    ) -> DependencyGraph {
        let mut graph: DependencyGraph = Arena::new();

        let blocks_by_name = ssa
            .blocks
            .iter()
            .enumerate()
            .skip(func_block_idx)
            .map(|(idx, b)| (b.name.clone(), idx - func_block_idx))
            .collect::<HashMap<String, usize>>();

        let len = ssa.blocks.len();
        // Create nodes
        for i in func_block_idx..len {
            let node = DTreeNode::default();
            graph.insert(node);
        }

        // Fill in dependees and dependencies
        for i in func_block_idx..len {
            let block = &ssa.blocks[i];
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

    fn find_params_from_uninitialized_vars(
        &mut self,
        ssa: &mut SSAIR,
        func_block_idx: usize,
        block_idx: usize,
    ) -> (Vec<BlockParameter>, Vec<String>) {
        let block = &ssa.blocks[func_block_idx + block_idx];

        // THIS SHOULD BE A HASHMAP LIKE IN THAT OTHER FUNCTION !!!!
        // SO THAT A PARAMETER GETS RESOLVED IF THE BLOCK OVERWRITES THE VARIABLE
        // BUT THEN WHAT ABOUT SOMETHING LIKE
        //
        // foo(bar#40: int):
        //      bar#50 = bar#40
        //      goto baz(bar#50)
        //
        // HERE IT SHOULD BE A PARAMETER EVEN THOUGH THE VARIABLE IS OVERWRITTEN
        //
        // foo():
        //      bar#50 = Int(3)
        //      goto baz(bar#50)
        //
        // HERE THE bar PARAMETER ISNT NEEDED

        let mut local_vars = vec![];
        let mut new_params = vec![];

        // for param in &block.parameters {
        //     local_vars.push(param.name.clone());
        // }

        for instr in &block.instructions {
            match instr {
                IRInstr::Unimplemented(res, _) => {
                    local_vars.push(res.clone());
                }
                IRInstr::Assign(res, irvalue) => {
                    local_vars.push(res.clone());
                    if let IRValue::Variable(val) = irvalue {
                        if !local_vars.contains(&val.name) {
                            new_params.push(BlockParameter {
                                name: val.name.clone(),
                                ty: val.ty.clone(),
                            })
                        }
                    }
                }
                IRInstr::BinOp(res, irvalue, irvalue1, _) => {
                    local_vars.push(res.clone());
                    if let IRValue::Variable(val) = irvalue {
                        if !local_vars.contains(&val.name) {
                            new_params.push(BlockParameter {
                                name: val.name.clone(),
                                ty: val.ty.clone(),
                            })
                        }
                    }

                    if let IRValue::Variable(val) = irvalue1 {
                        if !local_vars.contains(&val.name) {
                            new_params.push(BlockParameter {
                                name: val.name.clone(),
                                ty: val.ty.clone(),
                            })
                        }
                    }
                }
                IRInstr::UnOp(res, irvalue, unary_operation) => {
                    local_vars.push(res.clone());
                    if let IRValue::Variable(val) = irvalue {
                        if !local_vars.contains(&val.name) {
                            new_params.push(BlockParameter {
                                name: val.name.clone(),
                                ty: val.ty.clone(),
                            })
                        }
                    }
                }
                IRInstr::Call(res, irvalue, args) => {
                    local_vars.push(res.clone());
                    for arg in args {
                        if let IRValue::Variable(val) = arg {
                            if !local_vars.contains(&val.name) {
                                new_params.push(BlockParameter {
                                    name: val.name.clone(),
                                    ty: val.ty.clone(),
                                })
                            }
                        }
                    }
                }
                IRInstr::If(irvalue, true_label, true_args, false_label, false_args) => {
                    if let IRValue::Variable(val) = irvalue {
                        if !local_vars.contains(&val.name) {
                            new_params.push(BlockParameter {
                                name: val.name.clone(),
                                ty: val.ty.clone(),
                            })
                        }
                    }
                }
                IRInstr::Goto(label, args) => {}
                IRInstr::Return(irvalue) => {
                    if let IRValue::Variable(val) = irvalue {
                        if !local_vars.contains(&val.name) {
                            new_params.push(BlockParameter {
                                name: val.name.clone(),
                                ty: val.ty.clone(),
                            })
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
        ssa: &mut SSAIR,
        graph: &mut DependencyGraph,
        ctx: &mut ParamContext,
        func_block_idx: usize,
        unresolved_vars: &mut Vec<BlockParameter>,
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

        let (mut guaranteed_params, local_vars) =
            self.find_params_from_uninitialized_vars(ssa, func_block_idx, block_idx);

        unresolved_vars.retain(|var| !local_vars.contains(&var.name));

        for param in &guaranteed_params {
            if !unresolved_vars.contains(&param) {
                unresolved_vars.push(param.clone());
            }
        }

        for param in unresolved_vars.iter() {
            if !guaranteed_params.contains(&param) {
                guaranteed_params.push(param.clone());
            }
        }

        // Add those params
        let block = &mut ssa.blocks[func_block_idx + block_idx];
        for param in guaranteed_params {
            if !block.parameters.contains(&param) {
                block.parameters.push(param);
            }
        }

        let dnode = graph.get(block_idx).unwrap();
        let dependencies = dnode.dependencies.clone();

        println!("{dependencies:?}");
        for dep in dependencies.iter() {
            if !group.contains(&dep) {
                continue;
            }
            println!("{dep}");
            self.resolve_cycle_block_params(
                group,
                ssa,
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
        ssa: &mut SSAIR,
        graph: &mut DependencyGraph,
        ctx: &mut ParamContext,
        func_block_idx: usize,
        prev_node: i32,
        unresolved_vars: &mut Vec<BlockParameter>,
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

            // let mut cycle_local_unresolved_vars = unresolved_vars.clone();
            self.resolve_cycle_block_params(
                &group,
                ssa,
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
                        ssa,
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
            let (mut guaranteed_params, local_vars) =
                self.find_params_from_uninitialized_vars(ssa, func_block_idx, block_idx);

            unresolved_vars.retain(|var| !local_vars.contains(&var.name));

            for param in &guaranteed_params {
                if !unresolved_vars.contains(&param) {
                    unresolved_vars.push(param.clone());
                }
            }

            for param in unresolved_vars.iter() {
                if !guaranteed_params.contains(&param) {
                    guaranteed_params.push(param.clone());
                }
            }

            // Add those params
            let block = &mut ssa.blocks[func_block_idx + block_idx];
            for param in guaranteed_params {
                if !block.parameters.contains(&param) {
                    block.parameters.push(param);
                }
            }

            // Visit dependencies
            for dep in dependencies {
                self.figure_out_block_params(
                    ssa,
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

    fn figure_out_block_params_for_func(&mut self, ssa: &mut SSAIR, func_block_idx: usize) {
        let mut dependency_graph = self.build_fn_dependency_graph(ssa, func_block_idx);
        let strongly_connected_comps = self.find_strongly_connected(&mut dependency_graph);

        let last_block_idx = ssa.blocks.len() - func_block_idx - 1;

        let mut ctx = ParamContext::default();

        self.figure_out_block_params(
            ssa,
            &mut dependency_graph,
            &mut ctx,
            func_block_idx,
            -1,
            &mut vec![],
            &strongly_connected_comps,
            last_block_idx,
        );

        self.fix_passing_parameters_by_gotos(ssa, func_block_idx);
    }

    fn fix_passing_parameters_by_gotos(&mut self, ssa: &mut SSAIR, func_block_idx: usize) {
        let len = ssa.blocks.len();

        let block_copies = ssa.blocks.clone();

        let get_og_name = |name: &str| {
            let name = name.split("#").next().unwrap().to_string();
            let name = name.split("@").next().unwrap().to_string();
            name
        };

        for idx in func_block_idx..len {
            let block = &mut ssa.blocks[idx];
            let mut local_vars = HashMap::new();

            for param in &block.parameters {
                let og_name = get_og_name(&param.name);
                local_vars.insert(og_name, param.name.clone());
            }

            for instr in &mut block.instructions {
                match instr {
                    IRInstr::Unimplemented(res, _) => {
                        let og_name = get_og_name(&res);
                        local_vars.insert(og_name, res.clone());
                    }
                    IRInstr::Assign(res, irvalue) => {
                        let og_name = get_og_name(&res);
                        local_vars.insert(og_name, res.clone());
                    }
                    IRInstr::BinOp(res, irvalue, irvalue1, _) => {
                        let og_name = get_og_name(&res);
                        local_vars.insert(og_name, res.clone());
                    }
                    IRInstr::UnOp(res, irvalue, unary_operation) => {
                        let og_name = get_og_name(&res);
                        local_vars.insert(og_name, res.clone());
                    }
                    IRInstr::Call(res, irvalue, args) => {
                        let og_name = get_og_name(&res);
                        local_vars.insert(og_name, res.clone());
                    }
                    IRInstr::If(irvalue, true_label, true_args, false_label, false_args) => {
                        // add all params of branches
                        let true_block =
                            block_copies.iter().find(|b| b.name == *true_label).unwrap();

                        for arg in &true_block.parameters {
                            let og_name = get_og_name(&arg.name);
                            let this_block_name = local_vars.get(&og_name).unwrap();
                            true_args.push(IRValue::Variable(IRVariable {
                                name: this_block_name.to_string(),
                                ty: Type::Any,
                            }));
                        }

                        let false_block = block_copies
                            .iter()
                            .find(|b| b.name == *false_label)
                            .unwrap();

                        for arg in &false_block.parameters {
                            let og_name = get_og_name(&arg.name);
                            let this_block_name = local_vars.get(&og_name).unwrap();
                            false_args.push(IRValue::Variable(IRVariable {
                                name: this_block_name.to_string(),
                                ty: Type::Any,
                            }));
                        }
                    }
                    IRInstr::Goto(label, args) => {
                        // add all params of goto
                        //
                        let block = block_copies.iter().find(|b| b.name == *label).unwrap();

                        for arg in &block.parameters {
                            let og_name = get_og_name(&arg.name);
                            println!("{og_name}, {local_vars:?}");
                            let this_block_name = local_vars.get(&og_name).unwrap();
                            args.push(IRValue::Variable(IRVariable {
                                name: this_block_name.to_string(),
                                ty: Type::Any,
                            }));
                        }
                    }
                    IRInstr::Return(irvalue) => {}
                    IRInstr::Label(_) => unreachable!("There shouldnt be any labels at this point"),
                }
            }
        }
    }

    fn prune_all_instructions_after_first_branch(
        &mut self,
        ssa: &mut SSAIR,
        func_block_idx: usize,
    ) {
        let len = ssa.blocks.len();
        for block_idx in func_block_idx..len {
            let block = &mut ssa.blocks[block_idx];
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

    fn split_labels_into_blocks(ssa: &mut SSAIR, instructions: Vec<IRInstr>) -> Vec<IRInstr> {
        let mut ret_instrs = vec![];
        let mut curr_block = None;

        for instr in instructions {
            match instr {
                IRInstr::Label(label) => {
                    if let Some(curr_block) = curr_block {
                        ssa.blocks.push(curr_block);
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
            ssa.blocks.push(curr_block);
        }

        return ret_instrs;
    }

    pub fn generate_ir_codeblock(
        &mut self,
        scope: &mut usize,
        ssa: &mut SSAIR,
        symbol_table: &SymbolTable,
        renamed_vars: &mut HashMap<String, String>,
        loop_info: &LoopInfo,
        codeblock: &CodeBlock,
    ) -> Result<Vec<IRInstr>, String> {
        let mut instructions = Vec::new();

        for expr in &codeblock.expressions {
            let (res_var, mut instrs) =
                self.generate_ir_expr(scope, ssa, symbol_table, renamed_vars, loop_info, &expr)?;
            instructions.append(&mut instrs);
        }

        Ok(instructions)
    }

    pub fn generate_ir_expr(
        &mut self,
        scope: &mut usize,
        ssa: &mut SSAIR,
        symbol_table: &SymbolTable,
        renamed_vars: &mut HashMap<String, String>,
        loop_info: &LoopInfo,
        expr: &Expression,
    ) -> Result<(IRValue, Vec<IRInstr>), String> {
        let mut instructions = Vec::new();

        match expr {
            Expression::VariableDecl(variable_decl) => {
                let var_name = self.get_next_unique_name(&variable_decl.var_name);

                let (value, mut instrs) = self.generate_ir_expr(
                    scope,
                    ssa,
                    symbol_table,
                    renamed_vars,
                    loop_info,
                    &variable_decl.var_value,
                )?;

                renamed_vars.insert(variable_decl.var_name.clone(), var_name.clone());

                instructions.append(&mut instrs);

                instructions.push(IRInstr::Assign(var_name.clone(), value));

                return Ok((
                    IRValue::Variable(IRVariable {
                        name: var_name,
                        // symbol_idx: variable_decl.symbol_idx,
                        ty: variable_decl.var_type.clone(),
                    }),
                    instructions,
                ));
            }
            Expression::Literal(literal) => {
                let value = match literal {
                    Literal::String(vec) => IRValue::Literal(Literal::Int(0)),
                    lit => IRValue::Literal(lit.clone()),
                };

                return Ok((value, instructions));
            }
            Expression::BinaryOp(binary_op) => {
                let res = self.get_next_unique_name("_");

                let (lhs, mut lhs_instrs) = self.generate_ir_expr(
                    scope,
                    ssa,
                    symbol_table,
                    renamed_vars,
                    loop_info,
                    &binary_op.lhs,
                )?;
                let (rhs, mut rhs_instrs) = self.generate_ir_expr(
                    scope,
                    ssa,
                    symbol_table,
                    renamed_vars,
                    loop_info,
                    &binary_op.rhs,
                )?;

                instructions.append(&mut lhs_instrs);
                instructions.append(&mut rhs_instrs);

                instructions.push(IRInstr::BinOp(res.clone(), lhs.clone(), rhs, binary_op.op));

                return Ok((
                    IRValue::Variable(IRVariable {
                        name: res,
                        // IDK if this should be lhs cuz what about binops that take different types of args?
                        ty: lhs.ty(),
                    }),
                    instructions,
                ));
            }
            Expression::UnaryOp(unary_op) => {
                let res = self.get_next_unique_name("_");

                let (operand, mut operand_instrs) = self.generate_ir_expr(
                    scope,
                    ssa,
                    symbol_table,
                    renamed_vars,
                    loop_info,
                    &unary_op.operand,
                )?;

                instructions.append(&mut operand_instrs);

                instructions.push(IRInstr::UnOp(res.clone(), operand.clone(), unary_op.op));

                return Ok((
                    IRValue::Variable(IRVariable {
                        name: res,
                        ty: operand.ty(),
                    }),
                    instructions,
                ));
            }
            Expression::FunctionCall(function_call) => {
                let res = self.get_next_unique_name("_");

                let (mut func_expr, mut func_instrs) = self.generate_ir_expr(
                    scope,
                    ssa,
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
                    let (arg_expr, mut arg_instrs) = self.generate_ir_expr(
                        scope,
                        ssa,
                        symbol_table,
                        renamed_vars,
                        loop_info,
                        &arg,
                    )?;

                    instructions.append(&mut arg_instrs);

                    args.push(arg_expr);
                }

                instructions.push(IRInstr::Call(res.clone(), func_expr.clone(), args));

                return Ok((
                    IRValue::Variable(IRVariable {
                        name: res,
                        ty: func_expr.ty(),
                    }),
                    instructions,
                ));
            }
            Expression::Variable(variable) => {
                let var_symbol = symbol_table
                    .get_scope(variable.symbol_idx.0)
                    .unwrap()
                    .symbols
                    .get(variable.symbol_idx.1)
                    .unwrap();

                if let Some(replaced_name) = renamed_vars.get(&variable.name) {
                    return Ok((
                        IRValue::Variable(IRVariable {
                            name: replaced_name.clone(),
                            ty: var_symbol.value_type.clone(),
                        }),
                        instructions,
                    ));
                }

                return Ok((
                    IRValue::Variable(IRVariable {
                        name: variable.name.clone(),
                        ty: var_symbol.value_type.clone(),
                    }),
                    instructions,
                ));
            }
            Expression::Return(expression) => {
                let (ret_expr, mut ret_instrs) = self.generate_ir_expr(
                    scope,
                    ssa,
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
                    ssa,
                    symbol_table,
                    renamed_vars,
                    loop_info,
                    &assignment.lhs,
                )?;
                let (rhs, mut rhs_instrs) = self.generate_ir_expr(
                    scope,
                    ssa,
                    symbol_table,
                    renamed_vars,
                    loop_info,
                    &assignment.rhs,
                )?;

                instructions.append(&mut lhs_instrs);
                instructions.append(&mut rhs_instrs);

                if let IRValue::Variable(var) = lhs.clone() {
                    let original_name = var.name.split("#").next().unwrap();
                    let res = self.get_next_unique_name(&original_name);
                    instructions.push(IRInstr::Assign(res.clone(), rhs));
                    renamed_vars.insert(original_name.to_string(), res.clone());
                } else {
                    panic!("Assignment to literal?, {lhs:?}");
                }

                return Ok((IRValue::Literal(Literal::Int(0)), instructions));
            }
            Expression::AnonStruct(anon_struct) => {
                let res = self.get_next_unique_name("_");
                return Ok((
                    IRValue::Variable(IRVariable {
                        name: res.clone(),
                        ty: Type::Any,
                    }),
                    vec![IRInstr::Unimplemented(res, format!("Anon struct"))],
                ));
            }
            Expression::ArrayLiteral(array_literal) => {
                let res = self.get_next_unique_name("_");
                return Ok((
                    IRValue::Variable(IRVariable {
                        name: res.clone(),
                        ty: Type::Any,
                    }),
                    vec![IRInstr::Unimplemented(res, format!("Array literal"))],
                ));
            }
            Expression::ArrayAccess(array_access) => {
                let res = self.get_next_unique_name("_");
                return Ok((
                    IRValue::Variable(IRVariable {
                        name: res.clone(),
                        ty: Type::Any,
                    }),
                    vec![IRInstr::Unimplemented(res, format!("Array access"))],
                ));
            }
            Expression::FieldAccess(field_access) => {
                let res = self.get_next_unique_name("_");
                return Ok((
                    IRValue::Variable(IRVariable {
                        name: res.clone(),
                        ty: Type::Any,
                    }),
                    vec![IRInstr::Unimplemented(res, format!("Field access"))],
                ));
            }
            Expression::NamedStruct(named_struct) => {
                let res = self.get_next_unique_name("_");
                return Ok((
                    IRValue::Variable(IRVariable {
                        name: res.clone(),
                        ty: Type::Any,
                    }),
                    vec![IRInstr::Unimplemented(res, format!("Named struct"))],
                ));
            }
            Expression::Lambda(lambda) => {
                let res = self.get_next_unique_name("_");
                return Ok((
                    IRValue::Variable(IRVariable {
                        name: res.clone(),
                        ty: Type::Any,
                    }),
                    vec![IRInstr::Unimplemented(res, format!("Lambda"))],
                ));
            }
            Expression::Range(range) => {
                let res = self.get_next_unique_name("_");
                return Ok((
                    IRValue::Variable(IRVariable {
                        name: res.clone(),
                        ty: Type::Any,
                    }),
                    vec![IRInstr::Unimplemented(res, format!("Range"))],
                ));
            }
            Expression::JS(expression) => {
                let res = self.get_next_unique_name("_");
                return Ok((
                    IRValue::Variable(IRVariable {
                        name: res.clone(),
                        ty: Type::Any,
                    }),
                    vec![IRInstr::Unimplemented(res, format!("JS"))],
                ));
            }
            Expression::BuiltinType(expression) => {
                let res = self.get_next_unique_name("_");
                return Ok((
                    IRValue::Variable(IRVariable {
                        name: res.clone(),
                        ty: Type::Any,
                    }),
                    vec![IRInstr::Unimplemented(res, format!("@type"))],
                ));
            }
            Expression::If(if_stmt) => {
                let (cond_expr, mut cond_instrs) = self.generate_ir_expr(
                    scope,
                    ssa,
                    symbol_table,
                    renamed_vars,
                    loop_info,
                    &if_stmt.cond,
                )?;

                instructions.append(&mut cond_instrs);

                let after_if_label_name = self.get_next_unique_name("merge");
                let true_branch_label_name = self.get_next_unique_name("true");
                let false_branch_label_name = self.get_next_unique_name("false");

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
                    ssa,
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
                        ssa,
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
                let loop_cond_label = self.get_next_unique_name("loop_cond");
                let loop_body_label = self.get_next_unique_name("loop_body");
                let loop_end_label = self.get_next_unique_name("loop_end");
                instructions.push(IRInstr::Goto(loop_cond_label.clone(), vec![]));
                instructions.push(IRInstr::Label(loop_cond_label.clone()));

                let (interator_expr, mut iterator_instrs) = self.generate_ir_expr(
                    scope,
                    ssa,
                    symbol_table,
                    renamed_vars,
                    loop_info,
                    &for_expr.iterator,
                )?;

                let unique_binding_name = self.get_next_unique_name(&for_expr.binding);
                renamed_vars.insert(for_expr.binding.clone(), unique_binding_name.clone());

                instructions.append(&mut iterator_instrs);
                instructions.push(IRInstr::Assign(unique_binding_name, interator_expr.clone()));
                // instructions for condition checking here...
                //
                //  ---
                instructions.push(IRInstr::If(
                    interator_expr,
                    loop_body_label.clone(),
                    vec![],
                    loop_end_label.clone(),
                    vec![],
                ));
                instructions.push(IRInstr::Label(loop_body_label.clone()));

                let mut loop_body = self.generate_ir_codeblock(
                    scope,
                    ssa,
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

    fn get_next_unique_name(&mut self, smth: &str) -> String {
        let res = format!("{smth}#{}", self.var_counter);
        self.var_counter += 1;

        return res;
    }
}
