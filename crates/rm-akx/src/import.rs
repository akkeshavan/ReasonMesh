//! AKX import predicate (§7.3).
//!
//! A worker `W` with active assumption context `ctx_W` may apply knowledge
//! object `K = (kind, concl, asmpts, ...)` iff `ctx_W ⊇ asmpts`. Unconditional
//! knowledge (`asmpts = ∅`) is always applicable. Knowledge whose assumption
//! set partially overlaps the context is *buffered* (it may become applicable
//! on a future context change); knowledge with no overlap is *discarded*
//! (§7.3 "What to do with inapplicable knowledge").
//!
//! Import can never make a satisfiable instance UNSAT: if `IMPORT_OK` holds,
//! `F ∧ ctx_W ⊨ concl`, so importing `concl` adds a consequence already
//! entailed by the search space (§7.3 "What import cannot do").
//!
//! `canonical_key` (§7.2) is used for deduplication so a conclusion already
//! applied under the same assumptions is not applied twice.

use crate::filter::BloomFilter;
use crate::knowledge::{canonical_key, KnowledgeObject};
use crate::literal::Literal;
use crate::policy::ImportPolicy;
use rustc_hash::FxHashSet;
use serde::{Deserialize, Serialize};
use std::cmp::Ordering;

/// Decision of the import predicate for a single knowledge object.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ImportAction {
    /// `asmpts = ∅` or `ctx_W ⊇ asmpts`: safe to apply immediately.
    Apply,
    /// `ctx_W ⊅ asmpts` but `ctx_W ∩ asmpts ≠ ∅`: buffer and re-check on the
    /// next context change.
    Buffer,
    /// `ctx_W ∩ asmpts = ∅`: discard; unlikely to become applicable soon.
    Discard,
}

/// Decision on a knowledge object as it flows through the import gate.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ImportDecision {
    Applied,
    Buffered,
    Duplicate,
    DiscardedNoOverlap,
    DiscardedLowUtility,
}

/// The active assumption context of a worker: the sorted set of literals the
/// worker is currently assuming. This is `ctx_W` in the import predicate.
///
/// Kept sorted so subset tests are a linear merge (spec §7.3, "Literal ID
/// sets").
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ImportContext {
    lits: Vec<Literal>,
}

impl ImportContext {
    pub fn new() -> Self {
        ImportContext { lits: Vec::new() }
    }

    /// Build a context from an iterable of assumption literals (sorted on
    /// construction; duplicates ignored).
    pub fn from_assumptions(iter: impl IntoIterator<Item = Literal>) -> Self {
        let mut lits: Vec<Literal> = iter.into_iter().collect();
        lits.sort_unstable();
        lits.dedup();
        ImportContext { lits }
    }

    /// Insert a literal, keeping the set sorted and duplicate-free. Returns
    /// true if it was newly added.
    pub fn push(&mut self, lit: Literal) -> bool {
        match self.lits.binary_search(&lit) {
            Ok(_) => false,
            Err(pos) => {
                self.lits.insert(pos, lit);
                true
            }
        }
    }

    /// Remove a literal. Returns true if it was present.
    pub fn remove(&mut self, lit: Literal) -> bool {
        match self.lits.binary_search(&lit) {
            Ok(pos) => {
                self.lits.remove(pos);
                true
            }
            Err(_) => false,
        }
    }

    /// Set membership (binary search over the sorted set).
    pub fn contains(&self, lit: Literal) -> bool {
        self.lits.binary_search(&lit).is_ok()
    }

    /// `ctx_W ⊇ asmpts`: every assumption literal is in this context.
    ///
    /// O(|asmpts|) linear merge when `asmpts` is sorted (the documented
    /// convention for `KnowledgeObject::assumptions`); O(|asmpts| log|ctx|)
    /// fallback otherwise. Always correct.
    pub fn contains_all(&self, asmpts: &[Literal]) -> bool {
        if asmpts.iter().is_sorted() {
            let (mut i, mut j) = (0, 0);
            while j < asmpts.len() {
                if i >= self.lits.len() {
                    return false;
                }
                match self.lits[i].cmp(&asmpts[j]) {
                    Ordering::Less => i += 1,
                    Ordering::Equal => {
                        // One context element satisfies any number of identical
                        // assumption literals, so only advance the assumption
                        // cursor.
                        j += 1;
                    }
                    Ordering::Greater => return false,
                }
            }
            true
        } else {
            asmpts.iter().all(|l| self.contains(*l))
        }
    }

    pub fn literals(&self) -> &[Literal] {
        &self.lits
    }
}

/// Bounded buffer for knowledge awaiting a context match (§7.3). When full,
/// evicts the lowest-utility entry.
#[derive(Debug)]
pub struct ImportBuffer {
    cap: usize,
    entries: Vec<BufEntry>,
    keys: FxHashSet<u64>,
}

#[derive(Debug)]
struct BufEntry {
    obj: KnowledgeObject,
    key: u64,
}

impl ImportBuffer {
    pub fn new(cap: usize) -> Self {
        ImportBuffer {
            cap,
            entries: Vec::new(),
            keys: FxHashSet::default(),
        }
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Whether an object with the same canonical conclusion+assumptions is
    /// already buffered.
    pub fn contains_key(&self, key: u64) -> bool {
        self.keys.contains(&key)
    }

    /// Insert a conditional knowledge object. If already at capacity, evicts
    /// the entry with the lowest utility (duplicates resolved by id). Objects
    /// whose utility-bounded eviction would otherwise never apply are still
    /// re-checked later; eviction only trades which objects are retained.
    pub fn insert(&mut self, obj: KnowledgeObject) {
        let key = canonical_key(&obj);
        if self.keys.contains(&key) {
            return;
        }
        self.entries.push(BufEntry { obj, key });
        self.entries.sort_by(|a, b| {
            b.obj
                .utility
                .partial_cmp(&a.obj.utility)
                .unwrap_or(Ordering::Equal)
        });
        self.keys.insert(key);
        if self.entries.len() > self.cap {
            let evicted = self.entries.pop().expect("len > cap implies non-empty");
            self.keys.remove(&evicted.key);
        }
    }

    /// Re-check every buffered object against a (possibly changed) context,
    /// applying the predicate. Returns objects that became applicable and the
    /// number of objects dropped because their assumptions no longer overlap
    /// the context at all.
    pub fn recheck(
        &mut self,
        ctx: &ImportContext,
        max_out: usize,
    ) -> (Vec<KnowledgeObject>, usize) {
        let mut applied = Vec::new();
        let mut dropped = 0usize;
        let mut keep: Vec<BufEntry> = Vec::with_capacity(self.entries.len());
        for entry in self.entries.drain(..) {
            match classify_import(ctx, &entry.obj) {
                ImportAction::Apply => {
                    self.keys.remove(&entry.key);
                    if applied.len() < max_out {
                        applied.push(entry.obj);
                    }
                }
                ImportAction::Buffer => keep.push(entry),
                ImportAction::Discard => {
                    self.keys.remove(&entry.key);
                    dropped += 1;
                }
            }
        }
        self.entries = keep;
        // Entries may have been reordered on insert; sort by utility so the
        // buffer keeps its eviction ordering.
        self.entries.sort_by(|a, b| {
            b.obj
                .utility
                .partial_cmp(&a.obj.utility)
                .unwrap_or(Ordering::Equal)
        });
        (applied, dropped)
    }
}

/// The import gate: the component every worker uses to receive knowledge.
///
/// It holds the worker's current context, applies the §7.3 predicate (through
/// an optional Bloom pre-filter, spec §7.3 "Bloom pre-filter"), tracks
/// applied/discarded statistics, deduplicates via `canonical_key`, and keeps a
/// bounded utility-bounded buffer of conditional knowledge.
#[derive(Debug)]
pub struct ImportGate {
    ctx: ImportContext,
    policy: ImportPolicy,
    buffer: ImportBuffer,
    seen: FxHashSet<u64>,
    /// Optional Bloom pre-filter over `ctx`. Rebuilt on `set_context`.
    /// `None` disables the optimization (pure exact predicate).
    prefilter: Option<BloomFilter>,
}

impl ImportGate {
    pub fn new(policy: ImportPolicy) -> Self {
        let cap = policy.buffer_capacity.max(1);
        ImportGate {
            ctx: ImportContext::new(),
            policy,
            buffer: ImportBuffer::new(cap),
            seen: FxHashSet::default(),
            prefilter: None,
        }
    }

    /// As [`ImportGate::new`], but with a Bloom pre-filter sized at roughly
    /// `clbits` bits per context literal.
    pub fn with_bloom(policy: ImportPolicy, bits_per_ctx_literal: usize, num_hashes: u32) -> Self {
        let mut g = ImportGate::new(policy);
        g.prefilter = Some(BloomFilter::new(bits_per_ctx_literal.max(1), num_hashes));
        g
    }

    pub fn context(&self) -> &ImportContext {
        &self.ctx
    }

    /// Replace the worker's active assumption context and re-check the buffer.
    /// Returns objects that became applicable under the new context.
    pub fn set_context(&mut self, lits: &[Literal]) -> Vec<KnowledgeObject> {
        self.ctx = ImportContext::from_assumptions(lits.iter().copied());
        if let Some(b) = self.prefilter.as_mut() {
            *b = BloomFilter::over(&self.ctx.lits, b.num_bits(), 4);
        }
        let max_out = self.policy.max_items;
        let (applied, _dropped) = self.buffer.recheck(&self.ctx, max_out);
        applied
    }

    /// Submit a batch of knowledge to the gate. Applies the §7.3 predicate to
    /// each item, buffers partial-overlap items within bounds, and records
    /// per-bucket statistics.
    pub fn submit(&mut self, batch: &[KnowledgeObject]) -> Vec<ImportDecision> {
        let mut out = Vec::with_capacity(batch.len());
        for obj in batch {
            let decision = self.submit_one(obj);
            out.push(decision);
        }
        out
    }

    fn submit_one(&mut self, obj: &KnowledgeObject) -> ImportDecision {
        if obj.utility < self.policy.min_utility {
            return ImportDecision::DiscardedLowUtility;
        }
        let key = canonical_key(obj);
        if self.seen.contains(&key) {
            return ImportDecision::Duplicate;
        }
        // Bloom pre-filter: a "definitely absent" assumption literal proves
        // `ctx ⊉ asmpts`, so we may skip the exact subset merge. The filter
        // never has false negatives, so this is sound — but it does NOT tell
        // us whether the object still overlaps the context (Buffer vs Discard
        // still requires the overlap scan). We only pass it down to save the
        // merge in the common case.
        let non_subset = !obj.is_unconditional()
            && self
                .prefilter
                .as_ref()
                .is_some_and(|b| !b.maybe_contains_all(&obj.assumptions));
        match classify_import_with(&self.ctx, obj, non_subset) {
            ImportAction::Apply => {
                self.seen.insert(key);
                ImportDecision::Applied
            }
            ImportAction::Buffer => {
                if self.policy.max_items == 0 {
                    return ImportDecision::DiscardedNoOverlap;
                }
                self.buffer.insert(obj.clone());
                ImportDecision::Buffered
            }
            ImportAction::Discard => ImportDecision::DiscardedNoOverlap,
        }
    }

    pub fn buffer_len(&self) -> usize {
        self.buffer.len()
    }
}

/// The import predicate: `IMPORT_OK(W, K)` (spec §7.3).
pub fn classify_import(ctx: &ImportContext, obj: &KnowledgeObject) -> ImportAction {
    classify_import_with(ctx, obj, false)
}

/// The import predicate with an optional pre-computed "definitely not a
/// subset" verdict (e.g. from a Bloom pre-filter). `non_subset = true` skips
/// the exact `ctx ⊇ asmpts` merge; the overlap classification is always exact.
pub fn classify_import_with(
    ctx: &ImportContext,
    obj: &KnowledgeObject,
    non_subset: bool,
) -> ImportAction {
    if obj.is_unconditional() {
        return ImportAction::Apply;
    }
    if !non_subset && ctx.contains_all(&obj.assumptions) {
        return ImportAction::Apply;
    }
    if obj.assumptions.iter().any(|l| ctx.contains(*l)) {
        return ImportAction::Buffer;
    }
    ImportAction::Discard
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::knowledge::{ClauseKnowledge, KnowledgeId, KnowledgeKind, Scope, TrustLevel};

    fn clause_obj(
        id: u64,
        lits: &[Literal],
        assumptions: &[Literal],
        utility: f32,
    ) -> KnowledgeObject {
        KnowledgeObject {
            id: KnowledgeId(id),
            kind: KnowledgeKind::Clause(ClauseKnowledge {
                literals: lits.iter().copied().collect(),
                lbd: 1,
            }),
            assumptions: assumptions.iter().copied().collect(),
            scope: Scope::Process,
            trust: TrustLevel::Trusted,
            utility,
            proof_ref: None,
            source: 1,
        }
    }

    #[test]
    fn contains_all_merge_matches_brute_force() {
        for seed in 0..200u32 {
            let mut state: u64 = seed as u64;
            let mut rng = move || {
                state = state
                    .wrapping_mul(6364136223846793005)
                    .wrapping_add(1442695040888963407);
                (state >> 33) as u32
            };
            let ctx_lits: Vec<Literal> = (0..8)
                .map(|_| {
                    let v = 1 + (rng() % 6);
                    if rng() & 1 == 0 {
                        Literal::positive(v)
                    } else {
                        Literal::negative(v)
                    }
                })
                .collect();
            let ctx = ImportContext::from_assumptions(ctx_lits.clone());
            let asmpts: Vec<Literal> = (0..3)
                .map(|_| {
                    let v = 1 + (rng() % 6);
                    if rng() & 1 == 0 {
                        Literal::positive(v)
                    } else {
                        Literal::negative(v)
                    }
                })
                .collect();
            let expected = asmpts.iter().all(|l| ctx_lits.contains(l));
            let mut sorted = asmpts.clone();
            sorted.sort_unstable();
            let merge = ctx.contains_all(&sorted);
            assert_eq!(merge, expected);
            // unsorted fallback must agree too
            assert_eq!(ctx.contains_all(&asmpts), expected);
        }
    }

    #[test]
    fn classify_unconditional_is_always_apply() {
        let ctx = ImportContext::new();
        let obj = clause_obj(1, &[Literal::positive(1)], &[], 0.5);
        assert_eq!(classify_import(&ctx, &obj), ImportAction::Apply);
    }

    #[test]
    fn classify_subset_applies() {
        let ctx = ImportContext::from_assumptions([Literal::positive(1), Literal::negative(3)]);
        // asmpts ⊆ ctx
        let obj = clause_obj(1, &[Literal::negative(2)], &[Literal::positive(1)], 0.5);
        assert_eq!(classify_import(&ctx, &obj), ImportAction::Apply);
    }

    #[test]
    fn classify_partial_overlap_buffers() {
        let ctx = ImportContext::from_assumptions([Literal::positive(1)]);
        // overlap (x1) but not subset (also needs ¬x5)
        let obj = clause_obj(
            1,
            &[Literal::negative(2)],
            &[Literal::positive(1), Literal::negative(5)],
            0.5,
        );
        assert_eq!(classify_import(&ctx, &obj), ImportAction::Buffer);
    }

    #[test]
    fn classify_no_overlap_discards() {
        let ctx = ImportContext::from_assumptions([Literal::positive(1)]);
        // asmpts = {¬x2, ¬x5}, no overlap with {x1}
        let obj = clause_obj(
            1,
            &[Literal::negative(2)],
            &[Literal::negative(2), Literal::negative(5)],
            0.5,
        );
        assert_eq!(classify_import(&ctx, &obj), ImportAction::Discard);
    }

    #[test]
    fn classify_matches_brute_force() {
        let mut state: u64 = 2024;
        let mut rng = move || {
            state = state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            (state >> 33) as u32
        };
        for _ in 0..2000 {
            // Random context: each of 6 variables is unassigned, set, or negated.
            let mut ctx_lits = Vec::new();
            for v in 1..=6u32 {
                let r = rng() % 3;
                match r {
                    0 => {}
                    1 => ctx_lits.push(Literal::positive(v)),
                    _ => ctx_lits.push(Literal::negative(v)),
                }
            }
            let ctx = ImportContext::from_assumptions(ctx_lits.clone());

            // Random assumption set over the same variables.
            let asmpts: Vec<Literal> = (0..(1 + rng() % 4))
                .map(|_| {
                    let v = 1 + (rng() % 6);
                    if rng() & 1 == 0 {
                        Literal::positive(v)
                    } else {
                        Literal::negative(v)
                    }
                })
                .collect();
            let obj = clause_obj(1, &[Literal::positive(9)], &asmpts, 0.5);

            // Brute force: subset, overlap, or disjoint.
            let subset = asmpts.iter().all(|l| ctx_lits.contains(l));
            let overlap = asmpts.iter().any(|l| ctx_lits.contains(l));
            let expected = if asmpts.is_empty() || subset {
                ImportAction::Apply
            } else if overlap {
                ImportAction::Buffer
            } else {
                ImportAction::Discard
            };
            assert_eq!(
                classify_import(&ctx, &obj),
                expected,
                "ctx={:?} asmpts={:?}",
                ctx.literals(),
                &asmpts
            );
        }
    }

    #[test]
    fn gate_applies_buffers_and_discards() {
        let policy = ImportPolicy::default();
        let mut gate = ImportGate::new(policy);
        gate.set_context(&[Literal::positive(1)]);

        let unconditional = clause_obj(1, &[Literal::positive(2)], &[], 0.9);
        let subset = clause_obj(2, &[Literal::positive(3)], &[Literal::positive(1)], 0.9);
        let overlap = clause_obj(
            3,
            &[Literal::positive(3)],
            &[Literal::positive(1), Literal::negative(5)],
            0.8,
        );
        let disjoint = clause_obj(
            4,
            &[Literal::positive(3)],
            &[Literal::negative(2), Literal::negative(5)],
            0.7,
        );

        let decisions = gate.submit(&[unconditional.clone(), subset.clone(), overlap, disjoint]);
        assert_eq!(decisions[0], ImportDecision::Applied);
        assert_eq!(decisions[1], ImportDecision::Applied);
        assert_eq!(decisions[2], ImportDecision::Buffered);
        assert_eq!(decisions[3], ImportDecision::DiscardedNoOverlap);
        assert_eq!(gate.buffer_len(), 1);
    }

    #[test]
    fn buffered_object_applies_after_context_growth() {
        let policy = ImportPolicy::default();
        let mut gate = ImportGate::new(policy);
        gate.set_context(&[Literal::positive(1)]);
        let obj = clause_obj(
            5,
            &[Literal::positive(4)],
            &[Literal::positive(1), Literal::negative(5)],
            0.9,
        );
        let decisions = gate.submit(std::slice::from_ref(&obj));
        assert_eq!(decisions[0], ImportDecision::Buffered);
        assert_eq!(gate.buffer_len(), 1);

        // Now the worker extends its context with ¬x5: the object becomes
        // applicable and is drained by set_context.
        let mut next_ctx = vec![Literal::positive(1), Literal::negative(5)];
        next_ctx.sort_unstable();
        let ok = gate.set_context(&next_ctx);
        assert_eq!(ok.len(), 1);
        assert_eq!(ok[0].id, obj.id);
        assert_eq!(gate.buffer_len(), 0);
    }

    #[test]
    fn buffered_object_dropped_after_overlap_vanishes() {
        let policy = ImportPolicy::default();
        let mut gate = ImportGate::new(policy);
        gate.set_context(&[Literal::positive(1)]);
        let obj = clause_obj(
            5,
            &[Literal::positive(4)],
            &[Literal::positive(1), Literal::negative(5)],
            0.9,
        );
        let decisions = gate.submit(&[obj]);
        assert_eq!(decisions[0], ImportDecision::Buffered);

        // Context changes away entirely: no overlap → discarded.
        gate.set_context(&[Literal::negative(6)]);
        assert_eq!(gate.buffer_len(), 0);
    }

    #[test]
    fn gate_deduplicates_applied_conclusions() {
        let policy = ImportPolicy::default();
        let mut gate = ImportGate::new(policy);
        gate.set_context(&[]);
        let a = clause_obj(9, &[Literal::positive(2)], &[], 0.9);
        let b = clause_obj(99, &[Literal::positive(2)], &[], 0.9);
        let decisions = gate.submit(&[a, b]);
        assert_eq!(decisions[0], ImportDecision::Applied);
        assert_eq!(decisions[1], ImportDecision::Duplicate);
    }

    #[test]
    fn buffer_evicts_low_utility() {
        let policy = ImportPolicy {
            buffer_capacity: 2,
            ..ImportPolicy::default()
        };
        let mut gate = ImportGate::new(policy);
        gate.set_context(&[Literal::positive(1)]);
        let cond = |id: u64, util: f32, asmpt: Literal| {
            clause_obj(
                id,
                &[Literal::positive(4)],
                &[Literal::positive(1), asmpt],
                util,
            )
        };
        let high = cond(1, 0.9, Literal::negative(5));
        let mid = cond(2, 0.5, Literal::negative(6));
        let low = cond(3, 0.1, Literal::negative(7));
        gate.submit(&[high, mid, low]);
        assert_eq!(gate.buffer_len(), 2);
        // The evicted one must be the lowest utility.
        let ids: Vec<u64> = gate.buffer.entries.iter().map(|e| e.obj.id.0).collect();
        assert!(!ids.contains(&3));
        assert!(ids.contains(&1) && ids.contains(&2));
    }

    #[test]
    fn low_utility_is_rejected_by_policy() {
        let policy = ImportPolicy {
            min_utility: 0.5,
            ..ImportPolicy::default()
        };
        let mut gate = ImportGate::new(policy);
        gate.set_context(&[]);
        let obj = clause_obj(1, &[Literal::positive(2)], &[], 0.2);
        let d = gate.submit(&[obj]);
        assert_eq!(d[0], ImportDecision::DiscardedLowUtility);
    }

    #[test]
    fn bloom_prefilter_never_changes_decisions() {
        // Property: with the Bloom pre-filter enabled, decisions are identical
        // to the exact predicate. Bloom has no false negatives, so it can only
        // skip objects that would be DiscardedNoOverlap anyway.
        let policy = ImportPolicy::default();
        let mut exact = ImportGate::new(policy.clone());
        let mut bloom = ImportGate::with_bloom(policy, 16, 4);

        let mut state: u64 = 42;
        let mut rng = move || {
            state = state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            (state >> 33) as u32
        };

        for round in 0..50 {
            let mut ctx_lits = Vec::new();
            for v in 1..=8u32 {
                if rng() % 3 == 0 {
                    continue;
                }
                ctx_lits.push(if rng() & 1 == 0 {
                    Literal::positive(v)
                } else {
                    Literal::negative(v)
                });
            }
            let mut ctx_sorted = ctx_lits.clone();
            ctx_sorted.sort_unstable();
            let applied_exact = exact.set_context(&ctx_sorted);
            let applied_bloom = bloom.set_context(&ctx_sorted);
            assert_eq!(applied_exact.len(), applied_bloom.len());

            let batch: Vec<KnowledgeObject> = (0..20)
                .map(|i| {
                    let asmpts: Vec<Literal> = (0..(1 + rng() % 4))
                        .map(|_| {
                            let v = 1 + (rng() % 8);
                            if rng() & 1 == 0 {
                                Literal::positive(v)
                            } else {
                                Literal::negative(v)
                            }
                        })
                        .collect();
                    let util = (rng() % 10) as f32 / 10.0;
                    clause_obj(
                        100 + round as u64 * 20 + i,
                        &[Literal::positive(9)],
                        &asmpts,
                        util,
                    )
                })
                .collect();
            let d_exact = exact.submit(&batch);
            let d_bloom = bloom.submit(&batch);
            assert_eq!(d_exact, d_bloom, "round {round}");
            assert_eq!(exact.buffer_len(), bloom.buffer_len());
        }
    }
}
