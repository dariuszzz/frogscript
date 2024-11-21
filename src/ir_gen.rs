use std::collections::HashMap;

use crate::{
    pond::Target,
    ssa_ir::{Block, IRInstr, IRValue, SSAIR},
    symbol_table::SymbolTable,
    CodeBlock, Expression, Literal, Program, Type, Variable,
};

#[derive(Default)]
pub struct IRGen {
    pub var_counter: u32,
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
            self.generate_ir_codeblock(&mut scope, &module.toplevel_scope, symbol_table)?;

            for func in &module.function_defs {
                scope += 1;

                let mut parameters = HashMap::new();

                for arg in &func.argument_list {
                    parameters.insert(arg.arg_name.clone(), arg.arg_type.clone());
                }

                let instructions =
                    self.generate_ir_codeblock(&mut scope, &func.function_body, symbol_table)?;

                ssa_ir.blocks.push(Block {
                    parameters,
                    instructions,
                })
            }

            scope += 1;
        }

        Ok(ssa_ir)
    }

    pub fn generate_ir_codeblock(
        &mut self,
        scope: &mut usize,
        codeblock: &CodeBlock,
        symbol_table: &SymbolTable,
    ) -> Result<Vec<IRInstr>, String> {
        let mut instructions = Vec::new();

        for expr in &codeblock.expressions {
            let (res_var, mut instrs) = self.generate_ir_expr(scope, symbol_table, &expr)?;
            instructions.append(&mut instrs);
        }

        Ok(instructions)
    }

    pub fn generate_ir_expr(
        &mut self,
        scope: &mut usize,
        symbol_table: &SymbolTable,
        expr: &Expression,
    ) -> Result<(String, Vec<IRInstr>), String> {
        let mut instructions = Vec::new();

        match expr {
            Expression::VariableDecl(variable_decl) => {
                let var_name = variable_decl.var_name.clone();
                instructions.push(IRInstr::CreateVar(var_name.clone()));

                let (res, mut instrs) =
                    self.generate_ir_expr(scope, symbol_table, &variable_decl.var_value)?;

                instructions.append(&mut instrs);

                instructions.push(IRInstr::SetVar(
                    var_name.clone(),
                    IRValue::Variable(Variable {
                        name: res,
                        decl_scope: 0,
                    }),
                ));

                return Ok((var_name, instructions));
            }
            Expression::Literal(literal) => {
                let res = self.get_next_var_name("_");
                instructions.push(IRInstr::CreateVar(res.clone()));

                match literal {
                    Literal::String(vec) => todo!(),
                    lit => {
                        instructions
                            .push(IRInstr::SetVar(res.clone(), IRValue::Literal(lit.clone())));
                    }
                }

                return Ok((res, instructions));
            }
            Expression::BinaryOp(binary_op) => {
                let res = self.get_next_var_name("_");
                instructions.push(IRInstr::CreateVar(res.clone()));

                let (lhs, mut lhs_instrs) =
                    self.generate_ir_expr(scope, symbol_table, &binary_op.lhs)?;
                let (rhs, mut rhs_instrs) =
                    self.generate_ir_expr(scope, symbol_table, &binary_op.rhs)?;

                instructions.append(&mut lhs_instrs);
                instructions.append(&mut rhs_instrs);

                instructions.push(IRInstr::Add);

                return Ok((res, instructions));
            }
            Expression::UnaryOp(unary_op) => todo!(),
            Expression::FunctionCall(function_call) => todo!(),
            Expression::Variable(variable) => todo!(),
            Expression::Return(expression) => todo!(),
            Expression::Assignment(assignment) => todo!(),
            Expression::AnonStruct(anon_struct) => todo!(),
            Expression::ArrayLiteral(array_literal) => todo!(),
            Expression::ArrayAccess(array_access) => todo!(),
            Expression::FieldAccess(field_access) => todo!(),
            Expression::NamedStruct(named_struct) => todo!(),
            Expression::Lambda(lambda) => todo!(),
            Expression::Range(range) => todo!(),
            Expression::JS(expression) => todo!(),
            Expression::BuiltinType(expression) => todo!(),
            Expression::If(_) => todo!(),
            Expression::For(_) => todo!(),
            Expression::Import(import) => todo!(),
            Expression::Placeholder => todo!(),
            Expression::Break => todo!(),
            Expression::Continue => todo!(),
        }
    }

    fn get_next_var_name(&mut self, smth: &str) -> String {
        let res = format!("{smth}_{}", self.var_counter);
        self.var_counter += 1;

        return res;
    }
}
