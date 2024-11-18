use std::collections::HashMap;

use crate::{
    pond::Target,
    ssa_ir::{Block, IRInstr, IRValue, SSAIR},
    CodeBlock, ExprKind, Expression, Literal, Program, Variable,
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

        match &expr.kind {
            ExprKind::VariableDecl(variable_decl) => {
                let var_name = variable_decl.var_name.clone();
                instructions.push(IRInstr::CreateVar(var_name.clone()));

                let (res, mut instrs) = self.generate_ir_expr(&variable_decl.var_value)?;

                instructions.append(&mut instrs);

                instructions.push(IRInstr::SetVar(
                    var_name.clone(),
                    IRValue::Variable(Variable { name: res }),
                ));

                return Ok((var_name, instructions));
            }
            ExprKind::Literal(literal) => {
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
            ExprKind::BinaryOp(binary_op) => {
                let res = self.get_next_var_name("_");
                instructions.push(IRInstr::CreateVar(res.clone()));

                let (lhs, mut lhs_instrs) = self.generate_ir_expr(&binary_op.lhs)?;
                let (rhs, mut rhs_instrs) = self.generate_ir_expr(&binary_op.rhs)?;

                instructions.append(&mut lhs_instrs);
                instructions.append(&mut rhs_instrs);

                instructions.push(IRInstr::Add);

                return Ok((res, instructions));
            }
            ExprKind::UnaryOp(unary_op) => todo!(),
            ExprKind::FunctionCall(function_call) => todo!(),
            ExprKind::Variable(variable) => todo!(),
            ExprKind::Return(expression) => todo!(),
            ExprKind::Assignment(assignment) => todo!(),
            ExprKind::AnonStruct(anon_struct) => todo!(),
            ExprKind::ArrayLiteral(array_literal) => todo!(),
            ExprKind::ArrayAccess(array_access) => todo!(),
            ExprKind::FieldAccess(field_access) => todo!(),
            ExprKind::NamedStruct(named_struct) => todo!(),
            ExprKind::Lambda(lambda) => todo!(),
            ExprKind::Range(range) => todo!(),
            ExprKind::JS(expression) => todo!(),
            ExprKind::BuiltinType(expression) => todo!(),
            ExprKind::If(_) => todo!(),
            ExprKind::For(_) => todo!(),
            ExprKind::Import(import) => todo!(),
            ExprKind::Placeholder => todo!(),
            ExprKind::Break => todo!(),
            ExprKind::Continue => todo!(),
        }
    }

    fn get_next_var_name(&mut self, smth: &str) -> String {
        let res = format!("{smth}_{}", self.var_counter);
        self.var_counter += 1;

        return res;
    }
}
