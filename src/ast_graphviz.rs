use std::collections::HashMap;

use crate::{
    ast::{BinaryOperation, CodeBlock, Expression, Module, SymbolIdx},
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
            Self::Object => "style=dashed color=\"#90ee90\"",
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
}

impl NodeStyle {
    pub fn get(&self) -> &str {
        match self {
            Self::Stmt => "shape=box",
            Self::Value => "style=dashed color=\"#90ee90\"",
            Self::Variable => "style=dashed color=\"#f08080\"",
            Self::Action => "shape=box style=dashed color=\"#20b2aa\"",
            Self::Cond => "shape=diamond color=\"#ffa07a\"",
            Self::Operation => "shape=circle color=\"#6a5acd\"",
            Self::FuncCall => "style=\"rounded,filled\" shape=box color=\"#6a5acd30\"",
        }
    }
}

#[derive(Default)]
pub struct ASTGraphvizExporter {
    use_symbol_data: bool,
    name_counter: usize,
    symbol_to_node: HashMap<SymbolIdx, String>,
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

                self.symbol_to_node.insert(func.symbol_idx, start.clone());

                self.start_cluster(&mut out, "params");
                for arg in &func.argument_list {
                    let uniq = self.get_unique_name();
                    self.named_node(&mut out, &uniq, &arg.arg_name, NodeStyle::Variable);
                    self.symbol_to_node.insert(arg.symbol_idx, uniq.clone());
                }
                self.end_cluster(&mut out);

                let mut prev = vec![start];
                for stmt in &func.function_body.expressions {
                    let node_name = self.expr_to_graphviz(&mut out, stmt, prev);

                    prev = node_name;
                }
                self.end_cluster(&mut out);
            }
            self.end_cluster(&mut out);
        }

        out += "}";
        out
    }

    fn codeblock_to_graphviz(
        &mut self,
        out: &mut String,
        block: &CodeBlock,
        name: &str,
        mut prev: Vec<String>,
    ) -> Vec<String> {
        for stmt in &block.expressions {
            let output_nodes = self.expr_to_graphviz(out, stmt, prev);

            prev = output_nodes;
        }

        prev
    }

    fn connect(&self, out: &mut String, from: &Vec<String>, to: &str, style: ConnStyle) {
        for from in from {
            *out += &format!("{from} -> {to} [{}]\n", style.get());
        }
    }

    fn connect_label(
        &self,
        out: &mut String,
        from: &Vec<String>,
        to: &str,
        label: &str,
        style: ConnStyle,
    ) {
        for from in from {
            *out += &format!("{from} -> {to} [label=\"{}\" {}]\n", label, style.get());
        }
    }

    fn named_node(&self, out: &mut String, node: &str, name: &str, style: NodeStyle) {
        *out += &format!("{node}[label=\"{name}\" {}]\n", style.get());
    }

    fn start_cluster(&mut self, out: &mut String, label: &str) -> String {
        let uniq = self.get_unique_name();
        let name = format!("cluster_{uniq}");
        *out += &format!("\tsubgraph {name} {{\n");
        *out += &format!("\t\tlabel = \"{label}\"\n");
        *out += &format!("\t\tcolor = black\n");
        *out += &format!("\t\tstyle = rounded\n");

        name
    }

    fn end_cluster(&self, out: &mut String) {
        *out += "}\n";
    }

    fn expr_to_graphviz(
        &mut self,
        out: &mut String,
        expr: &Expression,
        prev: Vec<String>,
    ) -> Vec<String> {
        match expr {
            Expression::VariableDecl(var_decl) => {
                let value_node = self.expr_to_graphviz(out, &var_decl.var_value, vec![]);

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

                self.connect(out, &value_node, &this_node, ConnStyle::Input);
                self.connect(out, &prev, &this_node, ConnStyle::Regular);
                vec![this_node]
            }
            Expression::Literal(lit) => {
                let this_node = self.get_unique_name();
                let (label, style) = match lit {
                    Literal::String(parts) => {
                        let mut count = 1;
                        for part in parts {
                            match part {
                                FStringPart::Code(expr) => {
                                    let value_nodes = self.expr_to_graphviz(out, &expr, vec![]);
                                    self.connect_label(
                                        out,
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
                                        out,
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

                vec![this_node]
            }
            Expression::Variable(var) => {
                if self.use_symbol_data {
                    if let Some(node) = self.symbol_to_node.get(&var.symbol_idx) {
                        return vec![node.clone()];
                    }
                }

                let this_node = self.get_unique_name();
                self.named_node(out, &this_node, &var.name, NodeStyle::Variable);
                vec![this_node]
            }
            Expression::Assignment(ass) => {
                let lhs_val = self.expr_to_graphviz(out, &ass.lhs, vec![]);
                let rhs_val = self.expr_to_graphviz(out, &ass.rhs, vec![]);

                let this_node = self.get_unique_name();
                self.named_node(out, &this_node, "=", NodeStyle::Stmt);
                // This should never have more than one val on lhs
                self.connect(
                    out,
                    &vec![this_node.clone()],
                    &lhs_val[0],
                    ConnStyle::Output,
                );
                self.connect(out, &rhs_val, &this_node, ConnStyle::Input);

                self.connect(out, &prev, &this_node, ConnStyle::Regular);

                vec![this_node]
            }
            Expression::BinaryOp(bin_op) => {
                let lhs_val = self.expr_to_graphviz(out, &bin_op.lhs, vec![]);
                let rhs_val = self.expr_to_graphviz(out, &bin_op.rhs, vec![]);

                let this_node = self.get_unique_name();
                let op_label = bin_op.op.to_string();
                self.named_node(out, &this_node, &op_label, NodeStyle::Operation);
                self.connect_label(out, &lhs_val, &this_node, "lhs", ConnStyle::Input);
                self.connect_label(out, &rhs_val, &this_node, "rhs", ConnStyle::Input);

                self.connect(out, &prev, &this_node, ConnStyle::Regular);

                vec![this_node]
            }
            Expression::UnaryOp(un_op) => {
                let operand_val = self.expr_to_graphviz(out, &un_op.operand, vec![]);
                let this_node = self.get_unique_name();
                let op_label = un_op.op.to_string();
                self.named_node(out, &this_node, &op_label, NodeStyle::Operation);
                self.connect(out, &operand_val, &this_node, ConnStyle::Input);

                self.connect(out, &prev, &this_node, ConnStyle::Regular);

                vec![this_node]
            }
            Expression::Break => {
                let this_node = self.get_unique_name();
                self.named_node(out, &this_node, "break", NodeStyle::Stmt);

                self.connect(out, &prev, &this_node, ConnStyle::Regular);

                vec![this_node]
            }
            Expression::Continue => {
                let this_node = self.get_unique_name();
                self.named_node(out, &this_node, "break", NodeStyle::Stmt);

                self.connect(out, &prev, &this_node, ConnStyle::Regular);

                vec![this_node]
            }
            Expression::FunctionCall(function_call) => {
                let this_node = self.get_unique_name();

                self.named_node(out, &this_node, "func call", NodeStyle::FuncCall);
                let func_val = self.expr_to_graphviz(out, &function_call.func_expr, vec![]);

                self.connect(
                    out,
                    &vec![this_node.clone()],
                    &func_val[0],
                    ConnStyle::Object,
                );

                let mut count = 1;
                for arg in &function_call.arguments {
                    let arg_val = self.expr_to_graphviz(out, &arg, vec![]);

                    // hopefully this always works
                    self.connect_label(
                        out,
                        &arg_val,
                        &func_val[0],
                        &format!("arg{count}"),
                        ConnStyle::Input,
                    );

                    count += 1;
                }

                self.connect(out, &prev, &this_node, ConnStyle::Regular);

                vec![this_node]
            }
            Expression::Return(ret) => {
                let operand_val = self.expr_to_graphviz(out, &ret, vec![]);
                let this_node = self.get_unique_name();
                self.named_node(out, &this_node, "return", NodeStyle::Stmt);
                self.connect(out, &operand_val, &this_node, ConnStyle::Input);

                self.connect(out, &prev, &this_node, ConnStyle::Regular);

                vec![]
            }
            Expression::AnonStruct(anon_struct) => todo!(),
            Expression::ArrayLiteral(arr) => {
                let this_node = self.get_unique_name();
                self.named_node(out, &this_node, "array literal", NodeStyle::Action);
                let mut count = 0;
                for el in &arr.elements {
                    let el_val = self.expr_to_graphviz(out, el, vec![]);

                    self.connect_label(
                        out,
                        &el_val,
                        &this_node,
                        &format!("el{count}"),
                        ConnStyle::Input,
                    );
                    count += 1
                }

                self.connect(out, &prev, &this_node, ConnStyle::Regular);

                vec![this_node]
            }
            Expression::ArrayAccess(arr_acc) => {
                let this_node = self.get_unique_name();
                self.named_node(out, &this_node, "array access", NodeStyle::Action);
                let expr_val = self.expr_to_graphviz(out, &arr_acc.expr, vec![]);
                let index_val = self.expr_to_graphviz(out, &arr_acc.index, vec![]);

                self.connect(out, &expr_val, &this_node, ConnStyle::Object);
                self.connect(out, &index_val, &this_node, ConnStyle::Input);
                self.connect(out, &prev, &this_node, ConnStyle::Regular);

                vec![this_node]
            }
            Expression::FieldAccess(field_access) => todo!(),
            Expression::NamedStruct(named_struct) => todo!(),
            Expression::Lambda(lambda) => todo!(),
            Expression::Range(range) => {
                let this_node = self.get_unique_name();
                self.named_node(out, &this_node, "range", NodeStyle::Value);
                let start_val = self.expr_to_graphviz(out, &range.start, vec![]);
                let end_val = self.expr_to_graphviz(out, &range.end, vec![]);

                self.connect_label(out, &start_val, &this_node, "start", ConnStyle::Input);
                self.connect_label(out, &end_val, &this_node, "end", ConnStyle::Input);
                self.connect(out, &prev, &this_node, ConnStyle::Regular);

                vec![this_node]
            }
            Expression::BuiltinTarget(expression) => {
                let this_node = self.get_unique_name();
                self.named_node(out, &this_node, "@instr", NodeStyle::Stmt);

                self.connect(out, &prev, &this_node, ConnStyle::Regular);

                vec![this_node]
            }
            Expression::BuiltinType(expression) => {
                let this_node = self.get_unique_name();

                self.named_node(out, &this_node, "@type", NodeStyle::Stmt);

                self.connect(out, &prev, &this_node, ConnStyle::Regular);

                vec![this_node]
            }
            Expression::If(if_expr) => {
                let cond_val = self.expr_to_graphviz(out, &if_expr.cond, prev);
                self.start_cluster(out, "if");

                //overwrite style
                *out += &format!("{} [{}]\n", cond_val[0], NodeStyle::Cond.get());

                let true_block =
                    self.codeblock_to_graphviz(out, &if_expr.true_branch, "true", cond_val.clone());

                let mut out_vec = true_block.clone();

                if let Some(false_branch) = &if_expr.else_branch {
                    let mut false_block =
                        self.codeblock_to_graphviz(out, false_branch, "false", cond_val.clone());
                    out_vec.append(&mut false_block);
                }
                self.end_cluster(out);

                out_vec
            }
            Expression::For(for_expr) => {
                // for_expr.
                todo!()
            }
            Expression::Import(import) => {
                let this_node = self.get_unique_name();

                self.named_node(out, &this_node, "import", NodeStyle::Action);

                self.connect(out, &prev, &this_node, ConnStyle::Regular);

                vec![this_node]
            }
            Expression::Placeholder => {
                let this_node = self.get_unique_name();
                self.named_node(out, &this_node, "...", NodeStyle::Value);

                self.connect(out, &prev, &this_node, ConnStyle::Regular);

                vec![this_node]
            }
        }
    }
}
