use std::{cmp::Ordering, collections::HashMap};

#[derive(Default, Debug, Clone, Copy, PartialEq, Eq, Ord)]
pub struct InstrIndex {
    pub block_idx: usize,
    pub instr_idx: usize,
}

impl PartialOrd for InstrIndex {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let ord = if self.block_idx < other.block_idx {
            Ordering::Less
        } else if self.block_idx > other.block_idx {
            Ordering::Greater
        } else {
            if self.instr_idx < other.instr_idx {
                Ordering::Less
            } else if self.instr_idx > other.instr_idx {
                Ordering::Greater
            } else {
                Ordering::Equal
            }
        };

        return Some(ord);
    }
}

#[derive(Default, Debug, Clone)]
pub struct VarLifespans {
    pub var_lifepsans: HashMap<usize, (InstrIndex, InstrIndex)>,
}

impl VarLifespans {
    pub fn extend_lifespan(&mut self, var: usize, instr_index: InstrIndex) {
        self.var_lifepsans
            .entry(var)
            .and_modify(|(start, end)| {
                if instr_index < *start {
                    *start = instr_index;
                }
                if instr_index > *end {
                    *end = instr_index
                }
            })
            .or_insert((instr_index, instr_index));
    }

    pub fn is_var_alive(&self, var: usize, instr_index: InstrIndex) -> bool {
        match self.var_lifepsans.get(&var) {
            Some((start, end)) => return instr_index >= *start && instr_index <= *end,
            None => return false,
        }
    }

    pub fn get_live_vars(&self, instr_index: InstrIndex) -> Vec<usize> {
        let mut vars = vec![];

        for (var, (start, end)) in &self.var_lifepsans {
            if instr_index >= *start && instr_index <= *end {
                vars.push(*var);
            }
        }

        vars
    }
}
