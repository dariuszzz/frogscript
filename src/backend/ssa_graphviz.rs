use std::{
    collections::{HashMap, HashSet},
    thread::AccessError,
};

use crate::{
    ast::{AnonStruct, BinaryOperation, CodeBlock, Expression, Module, SymbolIdx, Variable},
    backend::ssa_ir::{Block, IRInstr, SSAIR},
    lexer::{FStringPart, Literal},
    symbol_table::SymbolTable,
};

pub enum ConnStyle {
    Regular,
}

impl ConnStyle {
    pub fn get(&self) -> &str {
        match self {
            Self::Regular => "",
        }
    }
}

pub enum NodeStyle {
    Loop,
    Stmt,
}

impl NodeStyle {
    pub fn get(&self) -> &str {
        match self {
            Self::Stmt => "shape=box",
            Self::Loop => "shape=box style=filled color=\"#ffa07a88\"",
        }
    }
}

#[derive(Default)]
pub struct SSAGraphvizExporter {
    name_counter: usize,
    connections: String,
    ssa: SSAIR,

    block_to_node: HashMap<String, String>,
}

impl SSAGraphvizExporter {
    pub fn new(ssa: SSAIR) -> Self {
        Self {
            ssa,
            connections: String::new(),
            name_counter: 0,
            block_to_node: HashMap::new(),
        }
    }

    fn get_unique_name(&mut self) -> String {
        let name = format!("{}", self.name_counter);
        self.name_counter += 1;
        name
    }

    pub fn export_naive(&mut self) -> String {
        let mut out = String::new();
        out += "digraph ssa {\n";

        let mut in_func = false;
        let blocks = self.ssa.blocks.clone();
        for (block_idx, block) in blocks.iter().enumerate() {
            if let Some(func_name) = &block.func_name {
                if in_func {
                    self.end_cluster(&mut out);
                }
                in_func = true;
                self.start_cluster(&mut out, func_name);
            }
            let this_node = self.get_unique_name();
            self.block_to_node
                .insert(block.name.clone(), this_node.clone());
            let name = self.ssa.pretty_print_block_name(&block);
            let instrs = self.ssa.pretty_print_block(&block);

            let block_content = format!("{name}\n{instrs}")
                .replace("&", "&amp;")
                .replace("\"", "&quot;")
                .replace("<", "&lt;")
                .replace(">", "&gt;")
                .replace("\t", "&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;")
                .replace("\n", "<BR ALIGN=\"left\"/>");

            let style = if self
                .ssa
                .cf_graph
                .strongly_conn
                .iter()
                .flatten()
                .find(|idx| **idx == block_idx)
                .is_some()
            {
                NodeStyle::Loop
            } else {
                NodeStyle::Stmt
            };
            self.named_node(&mut out, &this_node, &block_content, style);
        }

        if in_func {
            self.end_cluster(&mut out);
        }

        let graph_nodes = self.ssa.cf_graph.nodes.vec.clone();
        let mut visited = HashSet::new();
        for (idx, node) in graph_nodes.iter().enumerate() {
            if let Some(node) = node {
                if !visited.contains(&idx) {
                    visited.insert(idx);

                    let block = self.ssa.blocks[node.block_idx].name.clone();
                    let block_node = self.block_to_node.get(&block).unwrap().clone();

                    for next in &node.dependees {
                        let dependee = self.ssa.blocks[*next].name.clone();
                        let dependee_node = self.block_to_node.get(&dependee).unwrap().clone();
                        self.connect(
                            &vec![block_node.clone()],
                            &dependee_node,
                            ConnStyle::Regular,
                        );
                    }
                }
            }
        }

        out += &self.connections;
        out += "}";
        out
    }

    fn basicblock_to_graphviz(
        &mut self,
        out: &mut String,
        block: &Block,
        label: &str,
    ) -> (Vec<String>, Vec<String>) {
        let mut first = vec![];
        let mut last = vec![];
        self.start_cluster(out, label);
        for stmt in &block.instructions {
            let (in_nodes, out_nodes) = self.instr_to_graphviz(out, stmt);

            if !in_nodes.is_empty() {
                self.connect(&last, &in_nodes[0], ConnStyle::Regular);

                if first.is_empty() {
                    first = in_nodes;
                }

                last = out_nodes;
            }
        }
        self.end_cluster(out);

        (first, last)
    }

    fn connect(&mut self, from: &Vec<String>, to: &str, style: ConnStyle) {
        for from in from {
            self.connections += &format!("{from} -> {to} [{}]\n", style.get());
            // self.conn_map
            //     .entry(from.to_string())
            //     .and_modify(|conns| conns.push(to.to_string()))
            //     .or_insert(vec![to.to_string()]);
        }
    }

    fn connect_label(&mut self, from: &Vec<String>, to: &str, label: &str, style: ConnStyle) {
        for from in from {
            self.connections += &format!("{from} -> {to} [label=\"{}\" {}]\n", label, style.get());
            // self.conn_map
            //     .entry(from.to_string())
            //     .and_modify(|conns| conns.push(to.to_string()))
            //     .or_insert(vec![to.to_string()]);
        }
    }

    fn named_node(&self, out: &mut String, node: &str, name: &str, style: NodeStyle) {
        *out += &format!("{node}[label=<{name}> {}]\n", style.get());
    }

    fn output_one(&self, nodes: String) -> (Vec<String>, Vec<String>) {
        (vec![nodes.clone()], vec![nodes])
    }

    fn start_cluster(&mut self, out: &mut String, label: &str) -> String {
        let uniq = self.get_unique_name();
        let name = if label.is_empty() {
            format!("{uniq}")
        } else {
            format!("cluster_{uniq}")
        };

        *out += &format!("\tsubgraph {name} {{\n");
        *out += &format!("\t\tlabel = \"{label}\"\n");
        *out += &format!("\t\tcolor = gray\n");
        *out += &format!("\t\tstyle = rounded\n");

        name
    }

    fn end_cluster(&self, out: &mut String) {
        *out += "}\n";
    }

    fn instr_to_graphviz(
        &mut self,
        out: &mut String,
        instr: &IRInstr,
    ) -> (Vec<String>, Vec<String>) {
        self.output_one(String::new())
    }
}
