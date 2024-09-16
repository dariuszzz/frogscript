use crate::{Arena, Import, Type};

#[derive(Debug, Clone)]
pub struct Symbol {
    pub original_name: String,
    pub symbol_type: SymbolType,
    pub value_type: Type,
    pub exported: bool,
}

#[derive(PartialEq, Eq, Debug, Clone, Copy)]
pub enum SymbolType {
    Module,
    Identifier,
    Type,
}

#[derive(Debug, Clone, Default)]
pub struct Scope {
    pub parent_scope: Option<usize>,
    pub children_scopes: Vec<usize>,
    pub symbols: Vec<Symbol>,
    pub used_modules: Vec<Import>,
}

impl Scope {
    pub fn with_parent(parent: usize) -> Self {
        Self {
            parent_scope: Some(parent),
            children_scopes: Vec::new(),
            symbols: Vec::new(),
            used_modules: Vec::new(),
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct SymbolTable {
    pub table: Arena<Scope>,
}

impl SymbolTable {
    pub fn get_scope(&self, idx: usize) -> Option<&Scope> {
        self.table.get(idx)
    }

    pub fn get_scope_mut(&mut self, idx: usize) -> Option<&mut Scope> {
        self.table.get_mut(idx)
    }

    pub fn add_child_scope(&mut self, parent: usize, child: usize) -> Result<(), String> {
        let parent = self.get_scope_mut(parent).ok_or("Scope doesnt exist")?;
        parent.children_scopes.push(child);

        Ok(())
    }

    pub fn new_scope(&mut self, parent: usize) -> Result<usize, String> {
        let child = self.table.insert(Scope::with_parent(parent));
        self.add_child_scope(parent, child)?;

        Ok(child)
    }

    pub fn scope_get_symbol(
        &self,
        scope: usize,
        name: &str,
        symbol_type: SymbolType,
    ) -> Option<&Symbol> {
        let scope = self.get_scope(scope)?;

        scope
            .symbols
            .iter()
            .filter(|s| s.original_name == name && s.symbol_type == symbol_type)
            .next()
    }

    pub fn scope_get_symbol_mut(
        &mut self,
        scope: usize,
        name: &str,
        symbol_type: SymbolType,
    ) -> Option<&mut Symbol> {
        let scope = self.get_scope_mut(scope)?;

        scope
            .symbols
            .iter_mut()
            .filter(|s| s.original_name == name && s.symbol_type == symbol_type)
            .next()
    }

    pub fn find_symbol_rec(
        &self,
        scope: usize,
        symbol_name: &str,
        symbol_type: SymbolType,
    ) -> Result<&Symbol, String> {
        let mut curr_scope_opt = Some(scope);
        while let Some(curr_scope_idx) = curr_scope_opt {
            let curr_scope_parent = self
                .get_scope(curr_scope_idx)
                .ok_or("Scope does not exist")?
                .parent_scope;

            if let Some(symbol) = self.scope_get_symbol(curr_scope_idx, symbol_name, symbol_type) {
                return Ok(symbol);
            } else {
                curr_scope_opt = curr_scope_parent;
            }
        }

        Err(format!("Symbol {symbol_name:?} doesnt exist in scope"))
    }

    pub fn find_symbol_rec_mut(
        &mut self,
        scope: usize,
        symbol_name: &str,
        symbol_type: SymbolType,
    ) -> Result<&mut Symbol, String> {
        let mut curr_scope_opt = Some(scope);
        while let Some(curr_scope_idx) = curr_scope_opt {
            let curr_scope_parent = self
                .get_scope(curr_scope_idx)
                .ok_or("Scope does not exist")?
                .parent_scope;

            let symbol = self.scope_get_symbol_mut(curr_scope_idx, symbol_name, symbol_type);
            if symbol.is_none() {
                curr_scope_opt = curr_scope_parent;
            } else {
                break;
            }
        }

        if curr_scope_opt.is_none() {
            return Err(format!("Symbol {symbol_name:?} doesnt exist in scope"));
        }

        Ok(self
            .scope_get_symbol_mut(curr_scope_opt.unwrap(), symbol_name, symbol_type)
            .unwrap())
    }

    pub fn add_symbol_to_scope(&mut self, scope: usize, symbol: Symbol) -> Result<(), String> {
        let exists = self
            .scope_get_symbol(scope, &symbol.original_name, symbol.symbol_type)
            .is_some();

        let curr_scope = self.get_scope_mut(scope).ok_or("Scope does not exist")?;

        if exists {
            return Err(format!("Duplicate symbol {:?}", symbol.original_name));
        } else {
            curr_scope.symbols.push(symbol);
            Ok(())
        }
    }
}
