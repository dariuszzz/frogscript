use std::collections::HashMap;

use crate::{Literal, Type, Variable};

#[derive(Debug, Clone)]
pub struct SSAIR {
    pub blocks: Vec<Block>,
}

impl Default for SSAIR {
    fn default() -> Self {
        Self {
            blocks: Vec::default(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Block {
    pub parameters: HashMap<String, Type>,
    pub instructions: Vec<IRInstr>,
}

impl Default for Block {
    fn default() -> Self {
        Self {
            parameters: HashMap::new(),
            instructions: Vec::new(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum IRValue {
    Literal(Literal),
    Variable(Variable),
}

#[derive(Debug, Clone)]
pub enum IRInstr {
    CreateVar(String),
    SetVar(String, IRValue),
    GetVar(String),
    Add,
}
