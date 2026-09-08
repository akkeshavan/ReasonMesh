use crate::clause::ClauseRef;
use rm_akx::literal::Literal;

/// A watch entry: the clause being watched and a "blocker" literal.
///
/// The blocker is the other watched literal in the clause at the time this
/// entry was written. If `blocker` is True, the clause is already satisfied
/// and need not be fetched from memory — this is the key BCP cache win.
/// Blockers may go stale (the clause might have moved its second watch), but
/// staleness only causes missed skip opportunities, never incorrect results.
pub type WatchEntry = (ClauseRef, Literal);

/// Two-watched-literal index.
/// `watches[lit.raw()]` = list of (clause_ref, blocker) entries watching `lit`.
pub struct WatchList {
    watches: Vec<Vec<WatchEntry>>,
}

impl WatchList {
    pub fn new(num_vars: u32) -> Self {
        WatchList {
            watches: vec![Vec::new(); (num_vars * 2 + 2) as usize],
        }
    }

    /// Register that `cr` watches `lit`, with `blocker` as the other watched literal.
    pub fn watch(&mut self, lit: Literal, cr: ClauseRef, blocker: Literal) {
        self.watches[lit.raw() as usize].push((cr, blocker));
    }

    /// Remove every watch entry (used before rebuilding from the clause DB).
    pub fn clear(&mut self) {
        for list in self.watches.iter_mut() {
            list.clear();
        }
    }

    pub fn get(&self, lit: Literal) -> &[WatchEntry] {
        &self.watches[lit.raw() as usize]
    }

    pub fn get_mut(&mut self, lit: Literal) -> &mut Vec<WatchEntry> {
        &mut self.watches[lit.raw() as usize]
    }

    pub fn remove(&mut self, lit: Literal, cr: ClauseRef) {
        let list = &mut self.watches[lit.raw() as usize];
        if let Some(pos) = list.iter().position(|(r, _)| *r == cr) {
            list.swap_remove(pos);
        }
    }
}
