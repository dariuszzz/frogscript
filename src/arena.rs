use std::mem;

#[derive(Debug, Default)]
pub struct Arena<T> {
    pub vec: Vec<Option<T>>,
    pub free_spaces: Vec<usize>,
}

impl<T: Clone> Clone for Arena<T> {
    fn clone(&self) -> Self {
        Self {
            vec: self.vec.clone(),
            free_spaces: self.free_spaces.clone(),
        }
    }

    fn clone_from(&mut self, source: &Self) {
        self.vec = source.vec.clone();
        self.free_spaces = source.free_spaces.clone();
    }
}

impl<T> Arena<T> {
    pub fn new() -> Self {
        Self {
            vec: Vec::new(),
            free_spaces: Vec::new(),
        }
    }

    #[inline]
    pub fn free_index(&mut self) -> Option<usize> {
        self.free_spaces.pop()
    }

    #[inline]
    pub fn overwrite(&mut self, index: usize, val: T) {
        _ = mem::replace(&mut self.vec[index], Some(val))
    }

    #[inline]
    pub fn force_new_idx_push(&mut self, val: T) -> usize {
        self.vec.push(Some(val));
        self.vec.len() - 1
    }

    #[inline]
    pub fn insert(&mut self, val: T) -> usize {
        match self.free_index() {
            Some(idx) => {
                self.vec[idx] = Some(val);
                idx
            }
            None => {
                self.vec.push(Some(val));
                self.vec.len() - 1
            }
        }
    }

    #[inline]
    pub fn remove(&mut self, idx: usize) -> Option<T> {
        self.free_spaces.push(idx);
        mem::replace(&mut self.vec[idx], None)
    }

    #[inline]
    #[must_use]
    pub fn get(&self, idx: usize) -> Option<&T> {
        match self.vec.get(idx) {
            Some(v) => v.as_ref(),
            None => None,
        }
    }

    #[inline]
    #[must_use]
    pub fn get_mut(&mut self, idx: usize) -> Option<&mut T> {
        match self.vec.get_mut(idx) {
            Some(v) => v.as_mut(),
            None => None,
        }
    }
}
