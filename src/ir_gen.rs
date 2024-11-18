use std::collections::HashMap;

use crate::{
    pond::Target,
    ssa_ir::{Block, IRInstr, IRValue, SSAIR},
    CodeBlock, Expression, Literal, Program, Variable,
};

#[derive(Default)]
pub struct IRGen {
    pub var_counter: u32,
}

impl IRGen {
    pub fn generate_ir(&mut self, program: Program, target: &Target) -> Result<SSAIR, String> {
        let mut ssa_ir = SSAIR::default();

        for module in &program.modules {
            for func in &module.function_defs {
                let mut parameters = HashMap::new();

                for arg in &func.argument_list {
                    parameters.insert(arg.arg_name.clone(), arg.arg_type.clone());
                }

                let instructions = self.generate_ir_codeblock(&func.function_body)?;

                ssa_ir.blocks.push(Block {
                    parameters,
                    instructions,
                })
            }
        }

        Ok(ssa_ir)
    }

    pub fn generate_ir_codeblock(&mut self, codeblock: &CodeBlock) -> Result<Vec<IRInstr>, String> {
        let mut instructions = Vec::new();

        for expr in &codeblock.expressions {
            let (res_var, mut instrs) = self.generate_ir_expr(&expr)?;
            instructions.append(&mut instrs);
        }

        Ok(instructions)
    }

    pub fn generate_ir_expr(
        &mut self,
        expr: &Expression,
    ) -> Result<(String, Vec<IRInstr>), String> {
        let mut instructions = Vec::new();

        match expr {
            Expression::VariableDecl(variable_decl) => {
                let var_name = variable_decl.var_name.clone();
                instructions.push(IRInstr::CreateVar(var_name.clone()));

                let (res_var, mut instrs) = self.generate_ir_expr(&variable_decl.var_value)?;

                instructions.append(&mut instrs);

                instructions.push(IRInstr::SetVar(
                    var_name.clone(),
                    IRValue::Variable(Variable { name: res_var }),
                ));

                return Ok((var_name, instructions));
            }
            Expression::Literal(literal) => {
                let var_name = format!("__{}", self.var_counter);
                self.var_counter += 1;
                instructions.push(IRInstr::CreateVar(var_name.clone()));

                match literal {
                    Literal::String(vec) => todo!(),
                    lit => {
                        instructions.push(IRInstr::SetVar(
                            var_name.clone(),
                            IRValue::Literal(lit.clone()),
                        ));
                    }
                }

                return Ok((var_name, instructions));
            }
            Expression::BinaryOp(binary_op) => todo!(),
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
}
