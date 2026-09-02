//! Hierarchical scope routing with utility-aware promotion (spec §12.2).
//!
//! Knowledge lives at a scope level: `Local` (worker) → `Node` → `Cluster` →
//! `Global`. A [`Hierarchy`] router maintains one bounded buffer per level and
//! periodically *promotes* objects one level up, so knowledge that is valuable
//! enough to justify the bandwidth cost becomes visible to a wider audience.
//!
//! Promotion is utility-aware: an object is promoted only if its `utility`
//! score is at least [`HierarchyConfig::promotion_threshold`]. It is also
//! soundness-aware: `KnowledgeObject::promoted_scope()` gates promotion, so an
//! object's current scope can only advance one step per promotion and `Global`
//! objects never travel back down.
//!
//! Each level applies the shared §12.3 eviction / §12.4 supersede semantics.

use crate::queue::{InsertOutcome, Queue};
use crate::{BusError, EvictionPolicy, PollBudget, PublishHandle};
use rm_akx::{BusMetrics, KnowledgeBatch, Scope};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Mutex;

/// Level index for a scope, following the hierarchy order.
fn level_of(scope: Scope) -> usize {
    match scope {
        Scope::Local => 0,
        Scope::Process => 1,
        Scope::Node => 2,
        Scope::Global => 3,
    }
}

/// Scope for a level index (inverse of [`level_of`]).
fn scope_of(level: usize) -> Scope {
    match level {
        0 => Scope::Local,
        1 => Scope::Process,
        2 => Scope::Node,
        _ => Scope::Global,
    }
}

/// Configuration for the hierarchical router.
#[derive(Clone, Debug)]
pub struct HierarchyConfig {
    /// Buffer capacity at the worker-local level.
    pub local_buffer: usize,
    /// Buffer capacity at the node level.
    pub node_buffer: usize,
    /// Buffer capacity at the cluster level.
    pub cluster_buffer: usize,
    /// Buffer capacity at the global level.
    pub global_buffer: usize,
    /// Eviction policy applied at every level.
    pub eviction: EvictionPolicy,
    /// Minimum utility for an object to be promoted to the next scope.
    /// `1.0` disables promotion; `0.0` promotes everything eligible.
    pub promotion_threshold: f32,
}

impl Default for HierarchyConfig {
    fn default() -> Self {
        HierarchyConfig {
            local_buffer: 8_192,
            node_buffer: 65_536,
            cluster_buffer: 262_144,
            global_buffer: 262_144,
            eviction: EvictionPolicy::LowestUtilityThenOldest,
            promotion_threshold: 0.5,
        }
    }
}

/// Per-level metrics snapshot.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct LevelMetrics {
    /// Number of objects currently buffered at this level.
    pub buffered: usize,
    /// Capacity of this level's buffer.
    pub capacity: usize,
    /// Buffer utilization in [0.0, 1.0].
    pub utilization: f32,
}

/// Aggregate metrics for a [`Hierarchy`].
#[derive(Clone, Debug, Default, PartialEq)]
pub struct HierarchyMetrics {
    /// Per-level occupancy.
    pub levels: [LevelMetrics; 4],
    /// Total objects published by producers (before dedup/supersede).
    pub published_total: u64,
    /// Objects drained by consumers via `poll`.
    pub polled_total: u64,
    /// Objects dropped as duplicate/redundant at insert time.
    pub deduplicated: u64,
    /// Objects evicted to make room at insert time.
    pub evicted: u64,
    /// Conditional objects superseded by an unconditional version (§12.4).
    pub superseded: u64,
    /// Insert calls rejected with `BufferFull` back-pressure.
    pub backpressure: u64,
    /// Successful one-step promotions (Local→Node→Cluster→Global).
    pub promoted: u64,
    /// Promotion attempts that were duplicates/redundant at the target level.
    pub promotion_deduplicated: u64,
    /// Promotion attempts dropped because the object was already at `Global`.
    pub promotion_at_cap: u64,
    /// Promotion attempts skipped because utility < threshold.
    pub promotion_below_threshold: u64,
    /// Promotion attempts rejected because `promoted_scope()` disallows it.
    pub promotion_not_eligible: u64,
}

/// Hierarchical scope router.
///
/// Share it via `Arc<Hierarchy>`; all levels are internally synchronized.
pub struct Hierarchy {
    levels: [Mutex<Queue>; 4],
    threshold: f32,

    published: AtomicU64,
    polled: AtomicU64,
    deduplicated: AtomicU64,
    evicted: AtomicU64,
    superseded: AtomicU64,
    backpressure: AtomicU64,
    promoted: AtomicU64,
    promotion_deduplicated: AtomicU64,
    promotion_at_cap: AtomicU64,
    promotion_below_threshold: AtomicU64,
    promotion_not_eligible: AtomicU64,
}

impl Hierarchy {
    pub fn new(config: &HierarchyConfig) -> Self {
        let caps = [
            config.local_buffer,
            config.node_buffer,
            config.cluster_buffer,
            config.global_buffer,
        ];
        Hierarchy {
            levels: caps.map(|cap| Mutex::new(Queue::new(cap, config.eviction))),
            threshold: config.promotion_threshold,
            published: AtomicU64::new(0),
            polled: AtomicU64::new(0),
            deduplicated: AtomicU64::new(0),
            evicted: AtomicU64::new(0),
            superseded: AtomicU64::new(0),
            backpressure: AtomicU64::new(0),
            promoted: AtomicU64::new(0),
            promotion_deduplicated: AtomicU64::new(0),
            promotion_at_cap: AtomicU64::new(0),
            promotion_below_threshold: AtomicU64::new(0),
            promotion_not_eligible: AtomicU64::new(0),
        }
    }

    /// Insert `batch` at the given scope level. Returns the number of objects
    /// actually buffered (after dedup/eviction), mirroring `PublishHandle`.
    pub fn publish(&self, scope: Scope, batch: KnowledgeBatch) -> Result<PublishHandle, BusError> {
        let mut q = self.levels[level_of(scope)].lock().unwrap();
        let mut enqueued = 0usize;

        for obj in batch {
            match q.insert(obj) {
                Ok(InsertOutcome::Inserted {
                    superseded,
                    evicted,
                }) => {
                    if superseded > 0 {
                        self.superseded
                            .fetch_add(superseded as u64, Ordering::Relaxed);
                    }
                    if evicted > 0 {
                        self.evicted.fetch_add(evicted as u64, Ordering::Relaxed);
                    }
                    self.published.fetch_add(1, Ordering::Relaxed);
                    enqueued += 1;
                }
                Ok(InsertOutcome::Duplicate | InsertOutcome::Redundant) => {
                    self.deduplicated.fetch_add(1, Ordering::Relaxed);
                }
                Err(BusError::BufferFull) => {
                    self.backpressure.fetch_add(1, Ordering::Relaxed);
                    return Err(BusError::BufferFull);
                }
                Err(e) => return Err(e),
            }
        }
        Ok(PublishHandle { enqueued })
    }

    /// Drain up to `budget.max_items` objects from the given scope level.
    pub fn poll(&self, scope: Scope, budget: PollBudget) -> Result<KnowledgeBatch, BusError> {
        let mut q = self.levels[level_of(scope)].lock().unwrap();
        let mut batch = Vec::with_capacity(budget.max_items.min(64));
        while batch.len() < budget.max_items {
            let Some(obj) = q.pop_front() else {
                break;
            };
            self.polled.fetch_add(1, Ordering::Relaxed);
            batch.push(obj);
        }
        Ok(batch)
    }

    /// Promote every buffered object from `from` to the next level up, in
    /// FIFO order. Returns the number of objects successfully promoted.
    ///
    /// Promotion copies the object to the target level; the original stays at
    /// its current level so it remains visible to local consumers. The target
    /// deduplicates, so re-promoting the same object is idempotent. An object
    /// is only removed from the source level if the promotion *succeeds* (no
    /// data loss on back-pressure).
    pub fn promote_from(&self, from: usize) -> usize {
        if from >= 3 {
            return 0;
        }
        let to = from + 1;
        let to_scope = scope_of(to);

        let source = self.levels[from].lock().unwrap();
        let mut target = self.levels[to].lock().unwrap();

        let mut promoted = 0usize;

        for (_, obj) in source.enumerate_where(|_| true) {
            let eligible = match obj.promoted_scope() {
                Some(next) if next == to_scope => {
                    if obj.utility < self.threshold {
                        self.promotion_below_threshold
                            .fetch_add(1, Ordering::Relaxed);
                        false
                    } else {
                        true
                    }
                }
                Some(_) => {
                    self.promotion_not_eligible.fetch_add(1, Ordering::Relaxed);
                    false
                }
                None => {
                    self.promotion_at_cap.fetch_add(1, Ordering::Relaxed);
                    false
                }
            };
            if !eligible {
                continue;
            }
            let mut promoted_obj = obj;
            promoted_obj.scope = to_scope;
            match target.insert(promoted_obj) {
                Ok(InsertOutcome::Inserted {
                    superseded,
                    evicted,
                }) => {
                    promoted += 1;
                    if superseded > 0 {
                        self.superseded
                            .fetch_add(superseded as u64, Ordering::Relaxed);
                    }
                    if evicted > 0 {
                        self.evicted.fetch_add(evicted as u64, Ordering::Relaxed);
                    }
                }
                Ok(InsertOutcome::Duplicate | InsertOutcome::Redundant) => {
                    self.promotion_deduplicated.fetch_add(1, Ordering::Relaxed);
                }
                Err(_) => {
                    self.backpressure.fetch_add(1, Ordering::Relaxed);
                }
            }
        }

        self.promoted.fetch_add(promoted as u64, Ordering::Relaxed);
        promoted
    }

    /// Promote across the whole hierarchy: Local→Node→Cluster→Global, in
    /// order. Returns the total number of promotions performed.
    pub fn promote_all(&self) -> usize {
        (0..3).map(|level| self.promote_from(level)).sum()
    }

    /// Snapshot of all levels and counters.
    pub fn metrics(&self) -> HierarchyMetrics {
        let mut levels = [LevelMetrics::default(); 4];
        for (i, level) in self.levels.iter().enumerate() {
            let q = level.lock().unwrap();
            let cap = q.cap();
            levels[i] = LevelMetrics {
                buffered: q.len(),
                capacity: cap,
                utilization: if cap > 0 {
                    q.len() as f32 / cap as f32
                } else {
                    0.0
                },
            };
        }
        HierarchyMetrics {
            levels,
            published_total: self.published.load(Ordering::Relaxed),
            polled_total: self.polled.load(Ordering::Relaxed),
            deduplicated: self.deduplicated.load(Ordering::Relaxed),
            evicted: self.evicted.load(Ordering::Relaxed),
            superseded: self.superseded.load(Ordering::Relaxed),
            backpressure: self.backpressure.load(Ordering::Relaxed),
            promoted: self.promoted.load(Ordering::Relaxed),
            promotion_deduplicated: self.promotion_deduplicated.load(Ordering::Relaxed),
            promotion_at_cap: self.promotion_at_cap.load(Ordering::Relaxed),
            promotion_below_threshold: self.promotion_below_threshold.load(Ordering::Relaxed),
            promotion_not_eligible: self.promotion_not_eligible.load(Ordering::Relaxed),
        }
    }

    /// Convert to a `BusMetrics` snapshot (used by tooling that only knows the
    /// generic `KnowledgeBus` interface). Level occupancy is folded into
    /// `buffer_utilization` as the aggregate over all levels.
    pub fn bus_metrics(&self) -> BusMetrics {
        let m = self.metrics();
        let total_cap: usize = m.levels.iter().map(|l| l.capacity).sum();
        let total_used: usize = m.levels.iter().map(|l| l.buffered).sum();
        BusMetrics {
            published_total: m.published_total,
            polled_total: m.polled_total,
            deduplicated: m.deduplicated,
            evicted: m.evicted,
            superseded: m.superseded,
            backpressure: m.backpressure,
            buffer_utilization: if total_cap > 0 {
                total_used as f32 / total_cap as f32
            } else {
                0.0
            },
            ..Default::default()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rm_akx::{
        knowledge::{ClauseKnowledge, KnowledgeId, KnowledgeKind, KnowledgeObject, TrustLevel},
        literal::Literal,
    };

    fn clause_with(id: u64, lits: &[u32], assumptions: &[i32], utility: f32) -> KnowledgeObject {
        KnowledgeObject {
            id: KnowledgeId(id),
            kind: KnowledgeKind::Clause(ClauseKnowledge {
                literals: lits.iter().map(|&v| Literal::positive(v)).collect(),
                lbd: 1,
            }),
            assumptions: assumptions
                .iter()
                .map(|&l| {
                    let v = l.unsigned_abs();
                    if l > 0 {
                        Literal::positive(v)
                    } else {
                        Literal::negative(v)
                    }
                })
                .collect(),
            scope: Scope::Local,
            trust: TrustLevel::Trusted,
            utility,
            proof_ref: None,
            source: 0,
        }
    }

    fn clause(id: u64, lits: &[u32], utility: f32) -> KnowledgeObject {
        clause_with(id, lits, &[], utility)
    }

    fn under_protocol(f: impl FnOnce(&Hierarchy)) -> Hierarchy {
        let h = Hierarchy::new(&HierarchyConfig::default());
        f(&h);
        h
    }

    #[test]
    fn publish_buffers_at_scope_level() {
        let h = under_protocol(|h| {
            h.publish(Scope::Local, vec![clause(1, &[0, 1], 0.5)])
                .unwrap();
            h.publish(Scope::Node, vec![clause(2, &[2, 3], 0.5)])
                .unwrap();
        });
        assert_eq!(h.metrics().levels[0].buffered, 1);
        assert_eq!(h.metrics().levels[2].buffered, 1);
        assert_eq!(h.metrics().levels[1].buffered, 0);
        assert_eq!(h.metrics().levels[3].buffered, 0);
    }

    #[test]
    fn poll_drains_from_requested_level_only() {
        let h = under_protocol(|h| {
            h.publish(Scope::Local, vec![clause(1, &[0], 0.5)]).unwrap();
        });
        // Global has nothing; Local has one.
        let global = h.poll(Scope::Global, PollBudget { max_items: 10 }).unwrap();
        assert!(global.is_empty());
        let local = h.poll(Scope::Local, PollBudget { max_items: 10 }).unwrap();
        assert_eq!(local.len(), 1);
    }

    #[test]
    fn promotes_high_utility_up_one_level() {
        let h = under_protocol(|h| {
            h.publish(Scope::Local, vec![clause(1, &[0], 0.9)]).unwrap();
        });
        let n = h.promote_from(0);
        assert_eq!(n, 1);
        assert_eq!(h.metrics().promoted, 1);
        // Node level now holds a copy; Local still holds the original.
        assert_eq!(h.metrics().levels[1].buffered, 1);
        assert_eq!(h.metrics().levels[0].buffered, 1);
    }

    #[test]
    fn skips_below_threshold_utility() {
        let h = under_protocol(|h| {
            h.publish(Scope::Local, vec![clause(1, &[0], 0.2)]).unwrap();
        });
        let n = h.promote_from(0);
        assert_eq!(n, 0);
        assert_eq!(h.metrics().promotion_below_threshold, 1);
        assert_eq!(h.metrics().levels[1].buffered, 0);
        // Object is preserved in the source buffer.
        assert_eq!(h.metrics().levels[0].buffered, 1);
    }

    #[test]
    fn global_objects_never_promote() {
        let h = under_protocol(|h| {
            let mut obj = clause(1, &[0], 0.9);
            obj.scope = Scope::Global;
            h.publish(Scope::Global, vec![obj]).unwrap();
        });
        let n = h.promote_from(3);
        assert_eq!(n, 0);
        assert_eq!(h.metrics().promotion_at_cap, 0);
    }

    #[test]
    fn promotion_requires_single_step_up() {
        let h = under_protocol(|h| {
            // A Local object can only go to Node in one step.
            h.publish(Scope::Local, vec![clause(1, &[0], 0.9)]).unwrap();
        });
        h.promote_from(0);
        assert_eq!(h.metrics().levels[1].buffered, 1);
        assert_eq!(h.metrics().levels[2].buffered, 0);
        h.promote_from(1);
        assert_eq!(h.metrics().levels[2].buffered, 1);
    }

    #[test]
    fn full_hierarchy_promotion_chain() {
        let h = under_protocol(|h| {
            h.publish(Scope::Local, vec![clause(1, &[0], 0.9)]).unwrap();
        });
        h.promote_all();
        // Local→Node→Cluster→Global.
        assert_eq!(h.metrics().levels[3].buffered, 1);
        assert_eq!(h.metrics().promoted, 3);
    }

    #[test]
    fn re_promotion_is_idempotent() {
        let h = under_protocol(|h| {
            h.publish(Scope::Local, vec![clause(1, &[0], 0.9)]).unwrap();
        });
        h.promote_from(0);
        // Promoting again finds a duplicate at Node: nothing new inserted.
        let n = h.promote_from(0);
        assert_eq!(n, 0);
        assert_eq!(h.metrics().promotion_deduplicated, 1);
        assert_eq!(h.metrics().levels[1].buffered, 1);
    }

    #[test]
    fn promotion_supersedes_conditional_at_target() {
        let h = under_protocol(|h| {
            // Process holds a conditional (x1) under {¬x2}.
            h.publish(Scope::Process, vec![clause_with(1, &[1], &[-2], 0.5)])
                .unwrap();
            // Local derives the unconditional (x1); promote it to Process.
            h.publish(Scope::Local, vec![clause(2, &[1], 0.9)]).unwrap();
        });
        h.promote_from(0);
        assert_eq!(h.metrics().superseded, 1);
        let node = h
            .poll(Scope::Process, PollBudget { max_items: 10 })
            .unwrap();
        assert_eq!(node.len(), 1);
        assert!(node[0].is_unconditional());
    }
}
