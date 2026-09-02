use crate::clause::ClauseRef;
use rm_akx::literal::Literal;

/// Two-watched-literal index.
/// `watches[lit.raw()]` = list of clause refs that watch `lit`.
pub struct WatchList {
    watches: Vec<Vec<ClauseRef>>,
}

impl WatchList {
    pub fn new(num_vars: u32) -> Self {
        WatchList {
            watches: vec![Vec::new(); (num_vars * 2 + 2) as usize],
        }
    }

    pub fn watch(&mut self, lit: Literal, cr: ClauseRef) {
        self.watches[lit.raw() as usize].push(cr);
    }

    /// Remove every clause reference (used before rebuilding from the clause
    /// database, e.g. after a learnt-clause reduction).
    pub fn clear(&mut self) {
        for list in self.watches.iter_mut() {
            list.clear();
        }
    }

    pub fn get(&self, lit: Literal) -> &[ClauseRef] {
        &self.watches[lit.raw() as usize]
    }

    pub fn get_mut(&mut self, lit: Literal) -> &mut Vec<ClauseRef> {
        &mut self.watches[lit.raw() as usize]
    }

    pub fn remove(&mut self, lit: Literal, cr: ClauseRef) {
        let list = &mut self.watches[lit.raw() as usize];
        if let Some(pos) = list.iter().position(|&r| r == cr) {
            list.swap_remove(pos);
        }
    }
}
