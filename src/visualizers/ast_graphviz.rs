use std::{collections::HashMap, thread::AccessError};

use crate::{
    ast::{AnonStruct, BinaryOperation, CodeBlock, Expression, Module, SymbolIdx, Variable},
    lexer::{FStringPart, Literal},
    symbol_table::SymbolTable,
};

pub enum ConnStyle {
    Regular,
    Input,
    Output,
    Object,
}

impl ConnStyle {
    pub fn get(&self) -> &str {
        match self {
            Self::Regular => "",
            Self::Input => "style=dashed color=\"#add8e6\"",
            Self::Output => "style=dashed color=\"#f08080\"",
            Self::Object => "style=dashed color=\"#8fbc8f\" ",
        }
    }
}

pub enum NodeStyle {
    Stmt,
    Variable,
    Value,
    Action,
    Cond,
    Operation,
    FuncCall,
    StartOrEnd,
}

impl NodeStyle {
    pub fn get(&self) -> &str {
        match self {
            Self::Stmt => "shape=box",
            Self::Value => "style=dashed color=\"#8fbc8f\"",
            Self::Variable => "style=dashed color=\"#f08080\"",
            Self::Action => "shape=box style=dashed color=\"#20b2aa\"",
            Self::Cond => "shape=diamond color=\"#ffa07a\"",
            Self::Operation => "shape=circle color=\"#6a5acd\"",
            Self::FuncCall => "style=\"rounded,filled\" shape=box color=\"#6a5acd30\"",
            Self::StartOrEnd => "style=\"filled\" shape=box color=\"#6a5acd30\"",
        }
    }
}

#[derive(Default)]
pub struct ASTGraphvizExporter {
    use_symbol_data: bool,
    name_counter: usize,
    symbol_to_node: HashMap<SymbolIdx, String>,
    connections: String,
    conn_map: HashMap<String, Vec<String>>,
    //loop shenanigans for break and continue
    last_loop: String,
    breaks_to_fix: Vec<(String, String)>, //break node, related loop node
}

impl ASTGraphvizExporter {
    pub fn use_symbol_data(&mut self, opt: bool) {
        self.use_symbol_data = opt;
    }

    fn get_unique_name(&mut self) -> String {
        let name = format!("{}", self.name_counter);
        self.name_counter += 1;
        name
    }

    pub fn export_modules(&mut self, modules: &Vec<Module>) -> String {
        let mut out = String::new();
        out += "digraph ast {\n";

        for module in modules {
            let mod_name = &module.module_name;
            self.start_cluster(&mut out, mod_name);

            for func in &module.function_defs {
                let func_name = &func.func_name;
                self.start_cluster(&mut out, func_name);
                let start = self.get_unique_name();
                self.named_node(&mut out, &start, "START", NodeStyle::Stmt);

                // This is ugly (lines across the entire graph, and some functions dont connect anway, unreadable)
                // self.symbol_to_node.insert(func.symbol_idx, start.clone());

                self.start_cluster(&mut out, "params");
                for arg in &func.argument_list {
                    let uniq = self.get_unique_name();
                    self.named_node(
                        &mut out,
                        &uniq,
                        &format!("{} {}", arg.arg_name, arg.arg_type),
                        NodeStyle::Variable,
                    );
                    self.symbol_to_node.insert(arg.symbol_idx, uniq.clone());
                }
                self.end_cluster(&mut out);

                let mut last = vec![start];
                for stmt in &func.function_body.expressions {
                    let (in_nodes, out_nodes) = self.expr_to_graphviz(&mut out, stmt);

                    if !in_nodes.is_empty() {
                        self.connect(&last, &in_nodes[0], ConnStyle::Regular);
                        last = out_nodes;
                    }
                }
                self.end_cluster(&mut out);
            }
            self.end_cluster(&mut out);
        }

        // fix breaks
        for (br, lo) in self.breaks_to_fix.clone() {
            let next_node = self
                .conn_map
                .get(&lo)
                .expect("What")
                .last()
                .unwrap()
                .clone();

            self.connect(&vec![br.to_string()], &next_node, ConnStyle::Regular);
        }

        out += &self.connections;
        out += "}";
        out
    }

    fn codeblock_to_graphviz(
        &mut self,
        out: &mut String,
        block: &CodeBlock,
        label: &str,
    ) -> (Vec<String>, Vec<String>) {
        let mut first = vec![];
        let mut last = vec![];
        self.start_cluster(out, label);
        for stmt in &block.expressions {
            let (in_nodes, out_nodes) = self.expr_to_graphviz(out, stmt);

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
            self.conn_map
                .entry(from.to_string())
                .and_modify(|conns| conns.push(to.to_string()))
                .or_insert(vec![to.to_string()]);
        }
    }

    fn connect_label(&mut self, from: &Vec<String>, to: &str, label: &str, style: ConnStyle) {
        for from in from {
            self.connections += &format!("{from} -> {to} [label=\"{}\" {}]\n", label, style.get());
            self.conn_map
                .entry(from.to_string())
                .and_modify(|conns| conns.push(to.to_string()))
                .or_insert(vec![to.to_string()]);
        }
    }

    fn named_node(&self, out: &mut String, node: &str, name: &str, style: NodeStyle) {
        *out += &format!("{node}[label=\"{name}\" {}]\n", style.get());
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

    fn anon_struct_to_graphviz(
        &mut self,
        out: &mut String,
        anon_struct: &AnonStruct,
    ) -> (Vec<String>, Vec<String>) {
        let this_node = self.get_unique_name();
        self.named_node(out, &this_node, "anon struct", NodeStyle::Action);
        for (field_name, field) in &anon_struct.fields {
            let (_, field_val) = self.expr_to_graphviz(out, field);

            self.connect_label(
                &field_val,
                &this_node,
                &format!("{field_name}"),
                ConnStyle::Input,
            );
        }

        self.output_one(this_node)
    }

    fn expr_to_graphviz(
        &mut self,
        out: &mut String,
        expr: &Expression,
    ) -> (Vec<String>, Vec<String>) {
        match expr {
            Expression::VariableDecl(var_decl) => {
                let (_, value_node) = self.expr_to_graphviz(out, &var_decl.var_value);

                let mutable = if var_decl.is_mutable { "mut" } else { "let" };
                let name = &var_decl.var_name;
                let ty = var_decl.var_type.to_string();

                let this_node = self.get_unique_name();
                self.named_node(
                    out,
                    &this_node,
                    &format!("{mutable} {ty} {name}"),
                    NodeStyle::Stmt,
                );

                self.symbol_to_node
                    .insert(var_decl.symbol_idx, this_node.clone());

                self.connect(&value_node, &this_node, ConnStyle::Input);
                self.output_one(this_node)
            }
            Expression::Literal(lit) => {
                let this_node = self.get_unique_name();
                let (label, style) = match lit {
                    Literal::String(parts) => {
                        let mut count = 1;
                        for part in parts {
                            match part {
                                FStringPart::Code(expr) => {
                                    let (_, value_nodes) = self.expr_to_graphviz(out, &expr);
                                    self.connect_label(
                                        &value_nodes,
                                        &this_node,
                                        &format!("part{count}"),
                                        ConnStyle::Input,
                                    );
                                }
                                FStringPart::String(str) => {
                                    let str_part_node = self.get_unique_name();
                                    self.named_node(
                                        out,
                                        &str_part_node,
                                        &format!("\\\"{str}\\\""),
                                        NodeStyle::Value,
                                    );
                                    self.connect_label(
                                        &vec![str_part_node],
                                        &this_node,
                                        &format!("part{count}"),
                                        ConnStyle::Input,
                                    );
                                }
                            }
                            count += 1;
                        }

                        (format!("FString"), NodeStyle::Action)
                    }
                    other => (format!("{other:?}"), NodeStyle::Value),
                };

                self.named_node(out, &this_node, &label, style);

                self.output_one(this_node)
            }
            Expression::Variable(var) => {
                if self.use_symbol_data {
                    let maybe_node = self.symbol_to_node.get(&var.symbol_idx).cloned();

                    // let this_node = self.get_unique_name();
                    // self.named_node(
                    //     out,
                    //     &this_node,
                    //     &format!("{} -- {:?}", var.name, var.symbol_idx),
                    //     NodeStyle::Variable,
                    // );
                    if let Some(node) = maybe_node {
                        // self.connect(&vec![this_node.clone()], &node, ConnStyle::Input);
                        return (vec![node.clone()], vec![node.clone()]);
                    }
                    // return self.output_one(this_node);
                }

                let this_node = self.get_unique_name();
                self.named_node(out, &this_node, &var.name, NodeStyle::Variable);
                self.output_one(this_node)
            }
            Expression::Assignment(ass) => {
                let (_, lhs_val) = self.expr_to_graphviz(out, &ass.lhs);
                let (_, rhs_val) = self.expr_to_graphviz(out, &ass.rhs);

                let this_node = self.get_unique_name();
                self.named_node(out, &this_node, "=", NodeStyle::Stmt);
                // This should never have more than one val on lhs
                self.connect(&vec![this_node.clone()], &lhs_val[0], ConnStyle::Output);
                self.connect(&rhs_val, &this_node, ConnStyle::Input);

                self.output_one(this_node)
            }
            Expression::BinaryOp(bin_op) => {
                let (_, lhs_val) = self.expr_to_graphviz(out, &bin_op.lhs);
                let (_, rhs_val) = self.expr_to_graphviz(out, &bin_op.rhs);

                let this_node = self.get_unique_name();
                let op_label = bin_op.op.to_string();
                self.named_node(out, &this_node, &op_label, NodeStyle::Operation);
                self.connect_label(&lhs_val, &this_node, "lhs", ConnStyle::Input);
                self.connect_label(&rhs_val, &this_node, "rhs", ConnStyle::Input);

                self.output_one(this_node)
            }
            Expression::UnaryOp(un_op) => {
                let (_, operand_val) = self.expr_to_graphviz(out, &un_op.operand);
                let this_node = self.get_unique_name();
                let op_label = un_op.op.to_string();
                self.named_node(out, &this_node, &op_label, NodeStyle::Operation);
                self.connect(&operand_val, &this_node, ConnStyle::Input);

                self.output_one(this_node)
            }
            Expression::Break => {
                let this_node = self.get_unique_name();
                self.named_node(out, &this_node, "break", NodeStyle::Stmt);

                self.breaks_to_fix
                    .push((this_node.clone(), self.last_loop.clone()));

                (vec![this_node], vec![])
            }
            Expression::Continue => {
                let this_node = self.get_unique_name();
                self.named_node(out, &this_node, "continue", NodeStyle::Stmt);

                self.connect(
                    &vec![this_node.clone()],
                    &self.last_loop.clone(),
                    ConnStyle::Regular,
                );

                (vec![this_node], vec![])
            }
            Expression::FunctionCall(function_call) => {
                let this_node = self.get_unique_name();

                self.named_node(out, &this_node, "func call", NodeStyle::FuncCall);
                let (_, func_val) = self.expr_to_graphviz(out, &function_call.func_expr);

                self.connect(&vec![this_node.clone()], &func_val[0], ConnStyle::Object);

                let mut count = 1;
                for arg in &function_call.arguments {
                    let (_, arg_val) = self.expr_to_graphviz(out, &arg);

                    // hopefully this always works
                    self.connect_label(
                        &arg_val,
                        &this_node,
                        &format!("arg{count}"),
                        ConnStyle::Input,
                    );

                    count += 1;
                }

                self.output_one(this_node)
            }
            Expression::Return(ret) => {
                let this_node = self.get_unique_name();
                self.named_node(out, &this_node, "return", NodeStyle::Stmt);
                if let Some(ret) = ret {
                    let (_, operand_val) = self.expr_to_graphviz(out, &ret);
                    self.connect(&operand_val, &this_node, ConnStyle::Input);
                }

                (vec![this_node], vec![])
            }
            Expression::AnonStruct(anon_struct) => self.anon_struct_to_graphviz(out, anon_struct),
            Expression::ArrayLiteral(arr) => {
                let this_node = self.get_unique_name();
                self.named_node(out, &this_node, "array literal", NodeStyle::Action);
                let mut count = 0;
                for el in &arr.elements {
                    let (_, el_val) = self.expr_to_graphviz(out, el);

                    self.connect_label(
                        &el_val,
                        &this_node,
                        &format!("el{count}"),
                        ConnStyle::Input,
                    );
                    count += 1
                }

                self.output_one(this_node)
            }
            Expression::ArrayAccess(arr_acc) => {
                let this_node = self.get_unique_name();
                self.named_node(out, &this_node, "array access", NodeStyle::Action);
                let (_, expr_val) = self.expr_to_graphviz(out, &arr_acc.expr);
                let (_, index_val) = self.expr_to_graphviz(out, &arr_acc.index);

                self.connect(&expr_val, &this_node, ConnStyle::Object);
                self.connect(&index_val, &this_node, ConnStyle::Input);

                self.output_one(this_node)
            }
            Expression::FieldAccess(field_access) => {
                let this_node = self.get_unique_name();
                self.named_node(
                    out,
                    &this_node,
                    &format!("field: {}", field_access.field),
                    NodeStyle::Action,
                );
                let (_, expr_val) = self.expr_to_graphviz(out, &field_access.expr);
                // let field_val = self.get_unique_name();
                // self.named_node(out, &field_val, &field_access.field, NodeStyle::Variable);

                self.connect(&expr_val, &this_node, ConnStyle::Object);
                // self.connect(&vec![field_val], &this_node, ConnStyle::Input);

                self.output_one(this_node)
            }
            Expression::NamedStruct(named_struct) => {
                let this_node = self.get_unique_name();
                self.named_node(
                    out,
                    &this_node,
                    &format!("cast: {}", named_struct.casted_to),
                    NodeStyle::Action,
                );

                let (anon_struct_in, anon_struct_out) =
                    self.anon_struct_to_graphviz(out, &named_struct.struct_literal);

                self.connect(&anon_struct_out, &this_node, ConnStyle::Input);

                self.output_one(this_node)
            }
            Expression::Lambda(lambda) => {
                let this_node = self.get_unique_name();
                self.named_node(out, &this_node, "lambda", NodeStyle::Variable);

                self.output_one(this_node)
            }
            Expression::Range(range) => {
                let this_node = self.get_unique_name();
                self.named_node(out, &this_node, "range", NodeStyle::Value);
                let (_, start_val) = self.expr_to_graphviz(out, &range.start);
                let (_, end_val) = self.expr_to_graphviz(out, &range.end);

                self.connect_label(&start_val, &this_node, "start", ConnStyle::Input);
                self.connect_label(&end_val, &this_node, "end", ConnStyle::Input);

                self.output_one(this_node)
            }
            Expression::BuiltinTarget(expression) => {
                let this_node = self.get_unique_name();
                self.named_node(out, &this_node, "@instr", NodeStyle::Stmt);

                self.output_one(this_node)
            }
            Expression::BuiltinType(expression) => {
                let this_node = self.get_unique_name();

                self.named_node(out, &this_node, "@type", NodeStyle::Stmt);

                self.output_one(this_node)
            }
            Expression::If(if_expr) => {
                let (_, cond_val) = self.expr_to_graphviz(out, &if_expr.cond);
                //overwrite style
                *out += &format!("{} [{}]\n", cond_val[0], NodeStyle::Cond.get());

                let (in_true_block, out_true_block) =
                    self.codeblock_to_graphviz(out, &if_expr.true_branch, "true");

                self.connect_label(&cond_val, &in_true_block[0], "true", ConnStyle::Regular);

                let mut out_vec = out_true_block.clone();

                if let Some(false_branch) = &if_expr.else_branch {
                    let (in_false_block, mut out_false_block) =
                        self.codeblock_to_graphviz(out, false_branch, "false");
                    self.connect_label(&cond_val, &in_false_block[0], "false", ConnStyle::Regular);
                    out_vec.append(&mut out_false_block);
                } else {
                    // if out_vec.is_empty() {
                    out_vec.append(&mut cond_val.clone())
                    // }
                }

                (cond_val, out_vec)
            }
            Expression::For(for_expr) => {
                let this_node = self.get_unique_name();
                self.named_node(out, &this_node, "check loop", NodeStyle::Cond);
                let (_, iterator_out) = self.expr_to_graphviz(out, &for_expr.iterator);

                self.start_cluster(out, "loop body");

                let binding = self.get_unique_name();
                self.named_node(
                    out,
                    &binding,
                    &format!("{} {}", for_expr.binding, for_expr.binding_type),
                    NodeStyle::Variable,
                );
                self.symbol_to_node
                    .insert(for_expr.symbol_idx, binding.clone());

                self.last_loop = this_node.clone();

                self.connect(&vec![this_node.clone()], &binding, ConnStyle::Output);
                self.connect(&vec![binding], &this_node, ConnStyle::Input);
                self.connect(&iterator_out, &this_node, ConnStyle::Input);

                let (in_body, out_body) = self.codeblock_to_graphviz(out, &for_expr.body, "");

                self.connect_label(
                    &vec![this_node.clone()],
                    &in_body[0],
                    "true",
                    ConnStyle::Regular,
                );
                self.connect(&out_body, &this_node, ConnStyle::Regular);
                self.end_cluster(out);

                self.output_one(this_node)
            }
            Expression::Import(import) => {
                let this_node = self.get_unique_name();

                self.named_node(out, &this_node, "import", NodeStyle::Action);

                self.output_one(this_node)
            }
            Expression::Placeholder => {
                let this_node = self.get_unique_name();
                self.named_node(out, &this_node, "...", NodeStyle::Value);

                self.output_one(this_node)
            }
        }
    }
}
