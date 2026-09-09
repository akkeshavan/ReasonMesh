use rm_akx::literal::Literal;

// ---------------------------------------------------------------------------
// ClauseRef — index into the arena (word offset, not byte offset)
// ---------------------------------------------------------------------------

/// A handle to a clause. Stores the word offset of the clause header in the
/// arena. Sentinel values (DECISION, UNIT_CONFLICT) never point into the arena.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct ClauseRef(pub u32);

impl ClauseRef {
    /// Antecedent for a decision literal — no real clause.
    pub const DECISION: ClauseRef = ClauseRef(u32::MAX);
    /// Sentinel for a unit conflict with no antecedent clause.
    pub const UNIT_CONFLICT: ClauseRef = ClauseRef(u32::MAX - 1);

    pub fn is_decision(self) -> bool {
        self.0 == u32::MAX
    }
    pub fn is_sentinel(self) -> bool {
        self.0 >= u32::MAX - 1
    }
}

// ---------------------------------------------------------------------------
// ClauseArena
// ---------------------------------------------------------------------------
//
// All clauses (problem + learned) live in a single Vec<u32> arena.
//
// Per-clause layout (contiguous words starting at offset `cr.0`):
//   word[0]  — header: (len << 16) | (used << 15) | (lbd << 2) | (learnt << 1) | deleted
//              bit 0:     deleted flag
//              bit 1:     learnt flag
//              bits 2-14: LBD (13 bits, max 8191 — never reached in practice)
//              bit 15:    used_since_reduce — set when the clause participates in
//                         conflict analysis; cleared at each reduce round so that
//                         tier-2 clauses (LBD 3–6) must prove their value every round
//              bits 16-31: clause length
//   word[1..=len]  — literal raw values (Literal::raw() == u32)
//   word[len+1]  — clause activity encoded as f32::to_bits()
//
// This keeps all clause data in one hot region; every BCP watch hit that
// reaches the clause fetches the header and both watched literals in at most
// two adjacent cache lines instead of chasing a SmallVec heap pointer.

pub struct ClauseArena {
    data: Vec<u32>,
    learnt_count: usize,
    problem_count: usize,
    has_empty: bool,
}

impl ClauseArena {
    pub fn new() -> Self {
        ClauseArena {
            data: Vec::with_capacity(1 << 16),
            learnt_count: 0,
            problem_count: 0,
            has_empty: false,
        }
    }

    // -----------------------------------------------------------------------
    // Header field helpers (inlined for BCP hot path)
    // -----------------------------------------------------------------------

    #[inline]
    fn raw_header(&self, cr: ClauseRef) -> u32 {
        self.data[cr.0 as usize]
    }

    #[inline]
    pub fn clause_len(&self, cr: ClauseRef) -> usize {
        (self.raw_header(cr) >> 16) as usize
    }

    #[inline]
    pub fn lbd(&self, cr: ClauseRef) -> u32 {
        (self.raw_header(cr) >> 2) & 0x1FFF
    }

    /// Whether this clause has been used in conflict analysis since the last
    /// reduce round.  Cleared for surviving tier-2 clauses in `reduce_learned`.
    #[inline]
    pub fn is_used(&self, cr: ClauseRef) -> bool {
        self.raw_header(cr) & (1 << 15) != 0
    }

    /// Mark that this clause participated in conflict analysis this round.
    #[inline]
    pub fn mark_used(&mut self, cr: ClauseRef) {
        self.data[cr.0 as usize] |= 1 << 15;
    }

    #[inline]
    pub fn is_learnt(&self, cr: ClauseRef) -> bool {
        self.raw_header(cr) & 2 != 0
    }

    #[inline]
    pub fn is_deleted(&self, cr: ClauseRef) -> bool {
        self.raw_header(cr) & 1 != 0
    }

    pub fn set_lbd(&mut self, cr: ClauseRef, lbd: u32) {
        let h = &mut self.data[cr.0 as usize];
        *h = (*h & !(0x1FFF << 2)) | ((lbd & 0x1FFF) << 2);
    }

    pub fn mark_deleted(&mut self, cr: ClauseRef) {
        if !self.is_deleted(cr) {
            self.data[cr.0 as usize] |= 1;
            if self.is_learnt(cr) {
                self.learnt_count -= 1;
            }
        }
    }

    // -----------------------------------------------------------------------
    // Literal access — O(1), returns a pointer into the arena
    // -----------------------------------------------------------------------

    /// Direct literal access by index. Bounds-checked only in debug builds.
    #[inline]
    pub fn lit_at(&self, cr: ClauseRef, idx: usize) -> Literal {
        debug_assert!(idx < self.clause_len(cr));
        Literal::from_raw(self.data[cr.0 as usize + 1 + idx])
    }

    #[inline]
    pub fn set_lit_at(&mut self, cr: ClauseRef, idx: usize, lit: Literal) {
        debug_assert!(idx < self.clause_len(cr));
        self.data[cr.0 as usize + 1 + idx] = lit.raw();
    }

    #[inline]
    pub fn swap_lits(&mut self, cr: ClauseRef, i: usize, j: usize) {
        let base = cr.0 as usize + 1;
        self.data.swap(base + i, base + j);
    }

    /// Return all literals as a slice backed directly by the arena — zero copy.
    ///
    /// # Safety
    /// Safe because `Literal` is `#[repr(transparent)]` over `u32`.
    #[inline]
    pub fn lits(&self, cr: ClauseRef) -> &[Literal] {
        let n = self.clause_len(cr);
        let base = cr.0 as usize + 1;
        unsafe {
            std::slice::from_raw_parts(self.data[base..].as_ptr() as *const Literal, n)
        }
    }

    // -----------------------------------------------------------------------
    // Activity
    // -----------------------------------------------------------------------

    #[inline]
    pub fn activity(&self, cr: ClauseRef) -> f32 {
        let n = self.clause_len(cr);
        f32::from_bits(self.data[cr.0 as usize + 1 + n])
    }

    #[inline]
    pub fn bump_activity(&mut self, cr: ClauseRef, inc: f32) {
        let n = self.clause_len(cr);
        let idx = cr.0 as usize + 1 + n;
        let cur = f32::from_bits(self.data[idx]);
        self.data[idx] = (cur + inc).to_bits();
    }

    pub fn rescale_activities(&mut self, factor: f32) {
        let mut offset = 0usize;
        while offset < self.data.len() {
            let header = self.data[offset];
            let n = (header >> 16) as usize;
            let act_idx = offset + 1 + n;
            let cur = f32::from_bits(self.data[act_idx]);
            self.data[act_idx] = (cur * factor).to_bits();
            offset += n + 2;
        }
    }

    // -----------------------------------------------------------------------
    // Adding clauses
    // -----------------------------------------------------------------------

    pub fn add(&mut self, lits: &[Literal], learnt: bool, lbd: u32) -> ClauseRef {
        let offset = self.data.len() as u32;
        let n = lits.len() as u32;
        // Learned tier-2 clauses start with used=1 so they survive their first reduce round
        // (same as CaDiCaL). Problem clauses and tier-1/tier-3 learnt clauses leave it 0.
        let used_bit = if learnt && lbd > 2 && lbd <= 6 { 1u32 << 15 } else { 0 };
        let header = (n << 16) | used_bit | ((lbd & 0x1FFF) << 2) | ((learnt as u32) << 1);
        self.data.push(header);
        for &lit in lits {
            self.data.push(lit.raw());
        }
        self.data.push(0u32); // activity = 0.0
        if learnt {
            self.learnt_count += 1;
        } else {
            self.problem_count += 1;
        }
        ClauseRef(offset)
    }

    // -----------------------------------------------------------------------
    // Statistics
    // -----------------------------------------------------------------------

    pub fn learnt_count(&self) -> usize {
        self.learnt_count
    }

    /// Number of non-learned (problem) clauses currently in the arena.
    pub fn problem_count(&self) -> usize {
        self.problem_count
    }

    pub fn set_empty_clause(&mut self) {
        self.has_empty = true;
    }

    pub fn has_empty_clause(&self) -> bool {
        self.has_empty
    }

    // -----------------------------------------------------------------------
    // Learned-clause reduction
    // -----------------------------------------------------------------------

    /// Mark learned clauses for deletion when `should_delete(cr, lbd, activity, lit0, used)`.
    ///
    /// `lit0` is the first literal — used by the caller to check if the clause is a reason.
    /// `used` is true if the clause participated in conflict analysis since the last call to
    /// this function.  For surviving tier-2 clauses (LBD 3–6) the `used` bit is cleared so
    /// they must prove their value again next round (CaDiCaL-style consecutive-round tracking).
    pub fn reduce_learned(
        &mut self,
        mut should_delete: impl FnMut(ClauseRef, u32, f32, Literal, bool) -> bool,
    ) {
        const USED_BIT: u32 = 1 << 15;
        let mut offset = 0usize;
        while offset < self.data.len() {
            let header = self.data[offset];
            let n = (header >> 16) as usize;
            let learnt = (header & 2) != 0;
            let deleted = (header & 1) != 0;
            if learnt && !deleted {
                let cr = ClauseRef(offset as u32);
                let lbd = (header >> 2) & 0x1FFF;
                let used = header & USED_BIT != 0;
                let activity = f32::from_bits(self.data[offset + 1 + n]);
                let lit0 = Literal::from_raw(self.data[offset + 1]);
                if should_delete(cr, lbd, activity, lit0, used) {
                    self.data[offset] |= 1;
                    self.learnt_count -= 1;
                } else if lbd > 2 && lbd <= 6 {
                    // Tier-2 survivor: clear the used bit so the clause must
                    // be seen again in conflict analysis before the next round.
                    self.data[offset] &= !USED_BIT;
                }
            }
            offset += n + 2;
        }
    }

    // -----------------------------------------------------------------------
    // Arena compaction (called after reduce_learned to reclaim deleted space)
    // -----------------------------------------------------------------------

    /// Remove all deleted entries from the arena and return `(old_offset, new_offset)` pairs
    /// for every clause that moved. The caller must remap assignment reasons and binary-clause
    /// tables before calling `rebuild_watches`.
    pub fn compact(&mut self) -> Vec<(u32, u32)> {
        let mut new_data: Vec<u32> = Vec::with_capacity(self.data.len());
        let mut remaps: Vec<(u32, u32)> = Vec::new();
        let mut offset = 0usize;
        while offset < self.data.len() {
            let header = self.data[offset];
            let n = (header >> 16) as usize;
            let deleted = (header & 1) != 0;
            if !deleted {
                let new_offset = new_data.len() as u32;
                let old_offset = offset as u32;
                if old_offset != new_offset {
                    remaps.push((old_offset, new_offset));
                }
                new_data.extend_from_slice(&self.data[offset..offset + n + 2]);
            }
            offset += n + 2;
        }
        self.data = new_data;
        remaps
    }

    // -----------------------------------------------------------------------
    // Watch-list reconstruction (called after reduce_learned)
    // -----------------------------------------------------------------------

    pub fn rebuild_watches(&self, watches: &mut super::watched::WatchList) {
        watches.clear();
        let mut offset = 0usize;
        while offset < self.data.len() {
            let header = self.data[offset];
            let n = (header >> 16) as usize;
            let deleted = (header & 1) != 0;
            if !deleted && n >= 3 {
                let cr = ClauseRef(offset as u32);
                let lits = self.lits(cr);
                watches.watch(lits[0].negate(), cr, lits[1]);
                watches.watch(lits[1].negate(), cr, lits[0]);
            }
            offset += n + 2;
        }
    }

    /// Current word-count of the arena (used by callers to record a start
    /// position before adding clauses, then scan only the newly added ones).
    pub fn data_len(&self) -> usize {
        self.data.len()
    }

    // -----------------------------------------------------------------------
    // Arena iteration (for inprocessing passes)
    // -----------------------------------------------------------------------

    /// Call `f(cr, lbd, is_learnt, lits)` for every non-deleted clause of size ≥ min_len.
    pub fn for_each_clause(
        &self,
        min_len: usize,
        f: impl FnMut(ClauseRef, u32, bool, &[Literal]),
    ) {
        self.for_each_clause_from(0, min_len, f);
    }

    /// Like `for_each_clause` but starts scanning from `start_word_offset`.
    /// Use in combination with `data_len()` to iterate only newly added clauses.
    pub fn for_each_clause_from(
        &self,
        start_word_offset: usize,
        min_len: usize,
        mut f: impl FnMut(ClauseRef, u32, bool, &[Literal]),
    ) {
        let mut offset = start_word_offset;
        while offset < self.data.len() {
            let header = self.data[offset];
            let n = (header >> 16) as usize;
            let deleted = (header & 1) != 0;
            if !deleted && n >= min_len {
                let cr = ClauseRef(offset as u32);
                let lbd = (header >> 2) & 0x1FFF;
                let learnt = (header & 2) != 0;
                // SAFETY: Literal is repr(transparent) over u32
                let lits = unsafe {
                    std::slice::from_raw_parts(
                        self.data[offset + 1..].as_ptr() as *const Literal,
                        n,
                    )
                };
                f(cr, lbd, learnt, lits);
            }
            offset += n + 2;
        }
    }
}

impl Default for ClauseArena {
    fn default() -> Self {
        Self::new()
    }
}
