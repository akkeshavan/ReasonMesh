//! In-process bounded knowledge bus (spec §12).
//!
//! A shared ring buffer with §12.3 eviction and §12.4 supersede semantics:
//! - objects deduplicate by canonical key;
//! - an unconditional version of a conclusion evicts buffered conditional
//!   versions of the same conclusion;
//! - under memory pressure the incoming item is compared against the
//!   lowest-utility buffered item and either replaces it or is rejected with
//!   `BusError::BufferFull` back-pressure.
//!
//! ## Sharding (D1-1)
//!
//! To reduce lock contention at 16+ workers, the bus is sharded into
//! `SHARD_COUNT` independent `Queue`s. Each object is routed by
//! `conclusion_key(obj) % SHARD_COUNT` so that all objects with the same
//! conclusion (both conditional and unconditional) always land in the same
//! shard. This preserves dedup and §12.4 supersede semantics within each
//! shard without any cross-shard coordination.
//!
//! `poll()` drains shards in round-robin order so overall FIFO fairness is
//! maintained across shards.

use crate::queue::{InsertOutcome, Queue};
use crate::{BusConfig, BusError, KnowledgeBus, PollBudget, PublishHandle};
use rm_akx::{knowledge::conclusion_key, BusMetrics, KnowledgeBatch, Scope};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Mutex;

const SHARD_COUNT: usize = 16;

/// In-process bus sharded across `SHARD_COUNT` independent queues.
///
/// All scope levels (Local, Process, Node, Global) are collapsed into one
/// set of shards for the in-process case — scope is only meaningful for
/// network transport where it controls routing.
pub struct InprocBus {
    shards: [Mutex<Queue>; SHARD_COUNT],
    // Metrics counters.
    published: AtomicU64,
    polled: AtomicU64,
    deduplicated: AtomicU64,
    evicted: AtomicU64,
    superseded: AtomicU64,
    backpressure: AtomicU64,
}

impl InprocBus {
    pub fn new(config: &BusConfig) -> Self {
        // Each shard gets capacity / SHARD_COUNT (minimum 1).
        let shard_cap = (config.process_buffer / SHARD_COUNT).max(1);
        InprocBus {
            shards: std::array::from_fn(|_| {
                Mutex::new(Queue::new(shard_cap, config.eviction))
            }),
            published: AtomicU64::new(0),
            polled: AtomicU64::new(0),
            deduplicated: AtomicU64::new(0),
            evicted: AtomicU64::new(0),
            superseded: AtomicU64::new(0),
            backpressure: AtomicU64::new(0),
        }
    }

    /// Route by conclusion_key so all objects with the same conclusion (whether
    /// conditional or unconditional) always land in the same shard. This
    /// preserves dedup and supersede semantics within each shard's Queue.
    fn shard_index(ck: u64) -> usize {
        (ck % SHARD_COUNT as u64) as usize
    }
}

impl KnowledgeBus for InprocBus {
    fn publish(&self, _scope: Scope, batch: KnowledgeBatch) -> Result<PublishHandle, BusError> {
        let mut enqueued = 0usize;

        for obj in batch {
            let si = Self::shard_index(conclusion_key(&obj));
            let mut q = self.shards[si].lock().unwrap();
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

    fn poll(&self, budget: PollBudget) -> Result<KnowledgeBatch, BusError> {
        let mut batch = Vec::with_capacity(budget.max_items.min(64));

        // Drain shards in round-robin order until budget is exhausted.
        'outer: loop {
            let before = batch.len();
            for shard in &self.shards {
                if batch.len() >= budget.max_items {
                    break 'outer;
                }
                let mut q = shard.lock().unwrap();
                if let Some(obj) = q.pop_front() {
                    self.polled.fetch_add(1, Ordering::Relaxed);
                    batch.push(obj);
                }
            }
            // If no progress was made in a full round, all shards are empty.
            if batch.len() == before {
                break;
            }
        }

        Ok(batch)
    }

    fn metrics(&self) -> BusMetrics {
        let (cap, used) = {
            let mut total_cap = 0usize;
            let mut total_used = 0usize;
            for shard in &self.shards {
                let q = shard.lock().unwrap();
                total_cap += q.cap();
                total_used += q.len();
            }
            (total_cap, total_used)
        };
        BusMetrics {
            published_total: self.published.load(Ordering::Relaxed),
            polled_total: self.polled.load(Ordering::Relaxed),
            deduplicated: self.deduplicated.load(Ordering::Relaxed),
            evicted: self.evicted.load(Ordering::Relaxed),
            superseded: self.superseded.load(Ordering::Relaxed),
            backpressure: self.backpressure.load(Ordering::Relaxed),
            buffer_utilization: if cap > 0 {
                used as f32 / cap as f32
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
    use crate::EvictionPolicy;
    use rm_akx::{
        knowledge::{
            ClauseKnowledge, KnowledgeId, KnowledgeKind, KnowledgeObject, Scope, TrustLevel,
        },
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
            scope: Scope::Process,
            trust: TrustLevel::Trusted,
            utility,
            proof_ref: None,
            source: 0,
        }
    }

    fn clause(id: u64, lits: &[u32], utility: f32) -> KnowledgeObject {
        clause_with(id, lits, &[], utility)
    }

    fn under_protocol(f: impl FnOnce(&InprocBus)) -> InprocBus {
        let bus = InprocBus::new(&BusConfig::default());
        f(&bus);
        bus
    }

    #[test]
    fn publish_and_poll() {
        let bus = under_protocol(|bus| {
            bus.publish(Scope::Process, vec![clause(1, &[0, 1, 2], 0.5)])
                .unwrap();
        });
        let polled = bus.poll(PollBudget { max_items: 10 }).unwrap();
        assert_eq!(polled.len(), 1);
        assert_eq!(bus.metrics().published_total, 1);
    }

    #[test]
    fn deduplication() {
        // Both clauses have the same literal set [0,1,2] → same conclusion_key
        // → same shard → dedup fires.
        let bus = under_protocol(|bus| {
            bus.publish(Scope::Process, vec![clause(1, &[0, 1, 2], 0.5)])
                .unwrap();
            let h = bus
                .publish(Scope::Process, vec![clause(2, &[0, 1, 2], 0.5)])
                .unwrap();
            assert_eq!(h.enqueued, 0);
        });
        assert_eq!(bus.metrics().deduplicated, 1);
    }

    #[test]
    fn unconditional_supersedes_conditional() {
        let bus = under_protocol(|bus| {
            // Conditional version of the conclusion (x1 ∨ x2) under {¬x3}.
            // Same clause literals → same shard.
            bus.publish(Scope::Process, vec![clause_with(1, &[1, 2], &[-3], 0.5)])
                .unwrap();
            // Unconditional (x1 ∨ x2) arrives: the conditional must be evicted.
            bus.publish(Scope::Process, vec![clause(2, &[1, 2], 0.4)])
                .unwrap();
        });
        assert_eq!(bus.metrics().superseded, 1);
        // Exactly one item remains: the unconditional one.
        let polled = bus.poll(PollBudget { max_items: 10 }).unwrap();
        assert_eq!(polled.len(), 1);
        assert!(polled[0].is_unconditional());
    }

    #[test]
    fn conditional_redundant_while_unconditional_present() {
        let bus = under_protocol(|bus| {
            // Same clause literals → same shard.
            bus.publish(Scope::Process, vec![clause(1, &[1, 2], 0.5)])
                .unwrap();
            // Conditional of the same conclusion under {¬x3} is redundant.
            let h = bus
                .publish(Scope::Process, vec![clause_with(2, &[1, 2], &[-3], 0.9)])
                .unwrap();
            assert_eq!(h.enqueued, 0);
        });
        assert_eq!(bus.metrics().deduplicated, 1);
        let polled = bus.poll(PollBudget { max_items: 10 }).unwrap();
        assert_eq!(polled.len(), 1);
    }

    #[test]
    fn evicts_lowest_utility_on_pressure() {
        // Use shard_cap = 2 and route three distinct conclusions through the
        // same shard. We pick literal sets whose conclusion_keys all fall in
        // the same shard: use the same shard (verified by construction — all
        // go to whatever shard their conclusion_key selects; since the shard
        // cap is 2 and they have distinct literals, at most 2 can coexist
        // before eviction). The test uses a large process_buffer so shard_cap
        // = process_buffer / 16 = 32.
        //
        // With 16 shards each of capacity 32 and LowestUtility eviction, we
        // can test eviction by filling one shard to capacity (2 items) and
        // inserting a higher-utility item.
        //
        // For simplicity: use shard_cap=2 (process_buffer=32), distinct clause
        // literals (different shards allowed — the test only needs bus-level
        // eviction count). With 16 shards of cap 2 the bus can hold 32 items;
        // but we can use three items that all map to the same shard.
        //
        // We use a BusConfig with process_buffer=32 so shard_cap=2.
        // Insert two items, then a third with higher utility; expect eviction.
        //
        // To guarantee same shard: insert items with the SAME literal set but
        // different assumption sets (so they get distinct canonical keys but
        // the same conclusion_key → same shard).
        let config = BusConfig {
            process_buffer: 32, // shard_cap = 2
            eviction: EvictionPolicy::LowestUtility,
            ..Default::default()
        };
        let bus = InprocBus::new(&config);
        // All three have literal set [100] → same conclusion_key → same shard.
        bus.publish(Scope::Process, vec![clause_with(1, &[100], &[1], 0.8)])
            .unwrap();
        bus.publish(Scope::Process, vec![clause_with(2, &[100], &[2], 0.2)])
            .unwrap();
        // Incoming (utility 0.9) exceeds the lowest (0.2): evict it.
        bus.publish(Scope::Process, vec![clause_with(3, &[100], &[3], 0.9)])
            .unwrap();
        assert_eq!(bus.metrics().evicted, 1);
        let mut polled = bus.poll(PollBudget { max_items: 10 }).unwrap();
        polled.sort_by(|a, b| a.utility.partial_cmp(&b.utility).unwrap());
        // Buffer holds the two highest-utility items.
        let ids: Vec<u64> = polled.iter().map(|o| o.id.0).collect();
        assert!(ids.contains(&1) && ids.contains(&3));
        assert!(!ids.contains(&2));
    }

    #[test]
    fn back_pressure_when_incoming_below_lowest_utility() {
        // shard_cap = 1. Find two distinct single-literal clauses in the same
        // shard (same shard index but different conclusions). The first fills
        // the shard with utility 0.9; the second (utility 0.1) cannot displace it.
        use rm_akx::knowledge::conclusion_key as ck;
        let find_pair = || -> (u32, u32) {
            for lit_a in 1u32..=2000 {
                for lit_b in (lit_a + 1)..=2000 {
                    let a = clause(0, &[lit_a], 0.9);
                    let b = clause(1, &[lit_b], 0.1);
                    if ck(&a) % SHARD_COUNT as u64 == ck(&b) % SHARD_COUNT as u64 {
                        return (lit_a, lit_b);
                    }
                }
            }
            panic!("could not find two single-literal clauses in the same shard");
        };
        let (lit_a, lit_b) = find_pair();

        let config = BusConfig {
            process_buffer: 16, // shard_cap = 1
            eviction: EvictionPolicy::LowestUtility,
            ..Default::default()
        };
        let bus = InprocBus::new(&config);
        bus.publish(Scope::Process, vec![clause(1, &[lit_a], 0.9)])
            .unwrap();
        // Incoming (0.1) does not beat the buffered item (0.9): reject.
        let result = bus.publish(Scope::Process, vec![clause(2, &[lit_b], 0.1)]);
        assert!(matches!(result, Err(BusError::BufferFull)));
        assert_eq!(bus.metrics().backpressure, 1);
    }

    #[test]
    fn oldest_policy_evicts_front() {
        // Same shard: literal [300]. shard_cap = 2.
        let config = BusConfig {
            process_buffer: 32, // shard_cap = 2
            eviction: EvictionPolicy::Oldest,
            ..Default::default()
        };
        let bus = InprocBus::new(&config);
        // Three items with same literal [300] but different assumption sets
        // so they have distinct canonical keys and all land in the same shard.
        bus.publish(Scope::Process, vec![clause_with(1, &[300], &[1], 0.1)])
            .unwrap();
        bus.publish(Scope::Process, vec![clause_with(2, &[300], &[2], 0.9)])
            .unwrap();
        bus.publish(Scope::Process, vec![clause_with(3, &[300], &[3], 0.5)])
            .unwrap();
        assert_eq!(bus.metrics().evicted, 1);
        let polled = bus.poll(PollBudget { max_items: 10 }).unwrap();
        let mut ids: Vec<u64> = polled.iter().map(|o| o.id.0).collect();
        ids.sort();
        assert_eq!(ids, vec![2, 3]);
    }

    #[test]
    fn reject_incoming_policy_always_back_pressures() {
        // Same shard: literal [400]. shard_cap = 1.
        let config = BusConfig {
            process_buffer: 16, // shard_cap = 1
            eviction: EvictionPolicy::RejectIncoming,
            ..Default::default()
        };
        let bus = InprocBus::new(&config);
        bus.publish(Scope::Process, vec![clause_with(1, &[400], &[1], 0.1)])
            .unwrap();
        let result = bus.publish(Scope::Process, vec![clause_with(2, &[400], &[2], 0.9)]);
        assert!(matches!(result, Err(BusError::BufferFull)));
    }

    #[test]
    fn poll_drains_whole_queue_respecting_budget() {
        let bus = under_protocol(|bus| {
            for i in 0..5 {
                // Use distinct literal sets so they go to distinct shards — that's fine.
                bus.publish(Scope::Process, vec![clause(i, &[i as u32 + 1000], 0.5)])
                    .unwrap();
            }
        });
        let first = bus.poll(PollBudget { max_items: 2 }).unwrap();
        assert_eq!(first.len(), 2);
        let rest = bus.poll(PollBudget { max_items: 10 }).unwrap();
        assert_eq!(rest.len(), 3);
    }

    #[test]
    fn eviction_removes_from_unconditional_index() {
        // shard_cap = 1. Two unconditionals with different literals (different
        // shards each with cap 1). Insert conditional of the first literal —
        // since the unconditional for [500] is in its shard (and was evicted
        // when the second unconditional [500] with a different assumption was
        // inserted into the *same* shard), the conditional should be accepted.
        //
        // Simpler: use Oldest eviction, same shard, shard_cap=1.
        // Insert unconditional A into shard; evict A by inserting unconditional B
        // (same shard); now insert conditional of A's conclusion: accepted.
        let config = BusConfig {
            process_buffer: 16, // shard_cap = 1
            eviction: EvictionPolicy::Oldest,
            ..Default::default()
        };
        let bus = InprocBus::new(&config);
        // literal [500]: shard = conclusion_key([500]) % 16.
        bus.publish(Scope::Process, vec![clause(1, &[500], 0.5)])
            .unwrap();
        // literal [501]: different conclusion → different shard. Doesn't evict [500].
        // We need to evict [500] from its shard. Use same literal [500] with a
        // different assumption (different canonical key, same conclusion_key → same shard).
        // But shard_cap=1 and the first item is unconditional [500] which occupies
        // the shard. Insert another unconditional of a *different* conclusion (→ different shard)
        // won't affect this shard.
        //
        // To evict the unconditional [500]: insert another unconditional item with
        // a *different* literal into the SAME shard. We need two conclusions that
        // hash to the same shard. This is hard to guarantee without knowing the hash.
        //
        // Alternative: use process_buffer large enough that each shard has cap 2,
        // so we can insert 2 unconditionals then the conditional.
        //
        // Actually let's redesign: use a single shard by checking conclusion_key.
        // For this test, we verify the semantic: an unconditional evicted from the
        // bus (via bus-level eviction) allows a conditional of the same conclusion
        // to be inserted later.
        //
        // Use LowestUtility and insert an unconditional with low utility, then
        // evict it by inserting a higher utility object of the same conclusion.
        // Then insert the conditional: since the unconditional is gone from the
        // shard, the conditional is accepted.
        //
        // Use literal [500] shard (cap=2, process_buffer=32, Oldest eviction).
        // item 1: unconditional [500], item 2: unconditional [500] with asmpt [1]
        // — wait, that's conditional not unconditional.
        //
        // The cleanest approach: use Oldest policy, shard_cap=1, and two distinct
        // conclusions in the same shard. Since we can't know which conclusions hash
        // to the same shard without computing it, use a large shard_cap and rely
        // on the LowestUtility policy to evict selectively.
        //
        // FINAL APPROACH: process_buffer=16 → shard_cap=1. Use LowestUtility.
        // Insert unconditional [500] (utility 0.3). Insert unconditional [501]
        // (utility 0.3) → different shard, no conflict. Insert conditional [500]
        // with assumption [−3] (utility 0.5) → same shard as [500], but the
        // shard is full with unconditional [500]. Since conditional [500]'s
        // conclusion has an unconditional in the shard, it's REDUNDANT (not evicted).
        // The conditional should be accepted ONLY after the unconditional is evicted.
        //
        // Simplest fix: use LowestUtility, insert the unconditional [500] with
        // utility 0.3, then insert another item with SAME conclusion but higher
        // utility to evict the unconditional — but they'd be deduped.
        //
        // Use Oldest policy, shard_cap=2. Fill the shard with items from
        // different conclusions that both map to the same shard.
        // Since we can't predict which shard, use shard_cap=65536 (large enough
        // to never need eviction for this test) and verify the semantic directly.
        //
        // Actually the test is specifically about `eviction_removes_from_unconditional_index`.
        // Let's just use a BusConfig with a large enough buffer so we can
        // place items freely, and use Oldest policy on a controlled shard.
        //
        // The REAL simplest approach: use process_buffer big enough to hold all items
        // except for the deliberate eviction. Use same-shard items via the Oldest policy.
        // Items with different literal sets → different shards → the "eviction" of the
        // unconditional in one shard doesn't help the conditional in another shard.
        // So we MUST use same-shard items.
        //
        // We can compute which shard a literal maps to and construct test items accordingly.
        // OR, we can bypass this by making the whole test use a bus with shard_count=1
        // (i.e., process_buffer=1 and SHARD_COUNT effectively 1 via cap=max(1/16,1)=1 per shard
        // but then 16 shards × 1 cap = 16 total capacity).
        //
        // Since the test is specifically checking unconditional_index cleanup on eviction,
        // the simplest approach that avoids shard routing complexity is:
        // Use literals that share a conclusion_key (same shard), using large shard_cap.
        //
        // We'll use the EXISTING test logic but with same shard:
        // literal [500] unconditional → shard S.
        // Insert another item via Oldest → evicts [500] from shard S.
        // Insert conditional [500] → accepted (unconditional was evicted).
        //
        // For the "another item" to go to shard S, its conclusion_key % 16 must == S.
        // We'll simply skip the complexity and use a bus large enough to hold both
        // the evicting item AND verify the conditional was accepted in a DIFFERENT shard.
        //
        // Actually the test intent is: after unconditional [500] is evicted from the bus,
        // a conditional of the same conclusion ([500]) can be inserted.
        // With sharding, [500] items always go to the same shard. So:
        // shard S has cap=1 (Oldest), contains unconditional [500].
        // Insert another unconditional [500] → dedup (same conclusion → Redundant).
        // We need a different conclusion in shard S. Since we can't control that,
        // use LowestUtility to evict [500] via a higher-utility item of the SAME conclusion
        // (but that's dedup).
        //
        // Resolution: the test is inherently about the unconditional index cleanup.
        // With sharding by conclusion_key, the only way to evict an unconditional
        // is by inserting another item into the same shard with the Oldest policy
        // (or by LowestUtility with an item whose conclusion_key hashes to the same shard).
        //
        // The cleanest test: use a single shared conclusion shard by having TWO distinct
        // literals that hash to the same shard. We compute this at test-time.
        drop(bus); // discard the bus from above

        // Find two distinct literals whose conclusion_keys map to the same shard.
        // conclusion_key([x]) = hash(Clause, literals=[x]) — we can compute this by
        // checking conclusion_key of clauses with single literals.
        use rm_akx::knowledge::conclusion_key as ck;
        let make_single = |v: u32| clause(0, &[v], 0.5);
        let find_pair = || -> (u32, u32) {
            for lit_a in 1u32..=1000 {
                for lit_b in (lit_a + 1)..=1000 {
                    let a = make_single(lit_a);
                    let b = make_single(lit_b);
                    if ck(&a) % SHARD_COUNT as u64 == ck(&b) % SHARD_COUNT as u64 {
                        return (lit_a, lit_b);
                    }
                }
            }
            panic!("could not find two single-literal clauses in the same shard");
        };
        let (lit_a, lit_b) = find_pair();

        let config = BusConfig {
            process_buffer: 16, // shard_cap = 1
            eviction: EvictionPolicy::Oldest,
            ..Default::default()
        };
        let bus = InprocBus::new(&config);
        // Insert unconditional [lit_a] → fills shard S.
        bus.publish(Scope::Process, vec![clause(1, &[lit_a], 0.5)])
            .unwrap();
        // Insert unconditional [lit_b] (same shard S, Oldest) → evicts [lit_a].
        bus.publish(Scope::Process, vec![clause(2, &[lit_b], 0.5)])
            .unwrap();
        // Now insert conditional [lit_a] with assumption [-3].
        // [lit_a]'s unconditional was evicted from shard S, so it's accepted.
        let h = bus
            .publish(Scope::Process, vec![clause_with(3, &[lit_a], &[-3], 0.5)])
            .unwrap();
        assert_eq!(
            h.enqueued, 1,
            "conditional accepted after unconditional evicted"
        );
    }
}
