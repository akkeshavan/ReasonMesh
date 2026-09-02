//! In-process bounded knowledge bus (spec §12).
//!
//! A shared ring buffer with §12.3 eviction and §12.4 supersede semantics:
//! - objects deduplicate by canonical key;
//! - an unconditional version of a conclusion evicts buffered conditional
//!   versions of the same conclusion;
//! - under memory pressure the incoming item is compared against the
//!   lowest-utility buffered item and either replaces it or is rejected with
//!   `BusError::BufferFull` back-pressure.

use crate::queue::{InsertOutcome, Queue};
use crate::{BusConfig, BusError, KnowledgeBus, PollBudget, PublishHandle};
use rm_akx::{BusMetrics, KnowledgeBatch, Scope};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Mutex;

/// In-process bus over a single bounded ring buffer.
///
/// All scope levels (Local, Process, Node, Global) are collapsed into one
/// buffer for the in-process case — scope is only meaningful for network
/// transport where it controls routing.
pub struct InprocBus {
    state: Mutex<Queue>,
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
        InprocBus {
            state: Mutex::new(Queue::new(config.process_buffer, config.eviction)),
            published: AtomicU64::new(0),
            polled: AtomicU64::new(0),
            deduplicated: AtomicU64::new(0),
            evicted: AtomicU64::new(0),
            superseded: AtomicU64::new(0),
            backpressure: AtomicU64::new(0),
        }
    }
}

impl KnowledgeBus for InprocBus {
    fn publish(&self, _scope: Scope, batch: KnowledgeBatch) -> Result<PublishHandle, BusError> {
        let mut q = self.state.lock().unwrap();
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

    fn poll(&self, budget: PollBudget) -> Result<KnowledgeBatch, BusError> {
        let mut q = self.state.lock().unwrap();
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

    fn metrics(&self) -> BusMetrics {
        let (cap, used) = {
            let q = self.state.lock().unwrap();
            (q.cap(), q.len())
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
        let config = BusConfig {
            process_buffer: 2,
            eviction: EvictionPolicy::LowestUtility,
            ..Default::default()
        };
        let bus = InprocBus::new(&config);
        bus.publish(Scope::Process, vec![clause(1, &[1], 0.8)])
            .unwrap();
        bus.publish(Scope::Process, vec![clause(2, &[2], 0.2)])
            .unwrap();
        // Incoming (utility 0.9) exceeds the lowest (0.2): evict it.
        bus.publish(Scope::Process, vec![clause(3, &[3], 0.9)])
            .unwrap();
        assert_eq!(bus.metrics().evicted, 1);
        let mut polled = bus.poll(PollBudget { max_items: 10 }).unwrap();
        polled.sort_by_key(|o| o.utility as u32);
        // Buffer holds the two highest-utility items.
        assert_eq!(
            polled.iter().map(|o| o.id.0).collect::<Vec<_>>(),
            vec![1, 3]
        );
    }

    #[test]
    fn back_pressure_when_incoming_below_lowest_utility() {
        let config = BusConfig {
            process_buffer: 1,
            eviction: EvictionPolicy::LowestUtility,
            ..Default::default()
        };
        let bus = InprocBus::new(&config);
        bus.publish(Scope::Process, vec![clause(1, &[1], 0.9)])
            .unwrap();
        // Incoming (0.1) does not beat the buffered item (0.9): reject.
        let result = bus.publish(Scope::Process, vec![clause(2, &[2], 0.1)]);
        assert!(matches!(result, Err(BusError::BufferFull)));
        assert_eq!(bus.metrics().backpressure, 1);
    }

    #[test]
    fn oldest_policy_evicts_front() {
        let config = BusConfig {
            process_buffer: 2,
            eviction: EvictionPolicy::Oldest,
            ..Default::default()
        };
        let bus = InprocBus::new(&config);
        bus.publish(Scope::Process, vec![clause(1, &[1], 0.1)])
            .unwrap();
        bus.publish(Scope::Process, vec![clause(2, &[2], 0.9)])
            .unwrap();
        bus.publish(Scope::Process, vec![clause(3, &[3], 0.5)])
            .unwrap();
        assert_eq!(bus.metrics().evicted, 1);
        let polled = bus.poll(PollBudget { max_items: 10 }).unwrap();
        assert_eq!(
            polled.iter().map(|o| o.id.0).collect::<Vec<_>>(),
            vec![2, 3]
        );
    }

    #[test]
    fn reject_incoming_policy_always_back_pressures() {
        let config = BusConfig {
            process_buffer: 1,
            eviction: EvictionPolicy::RejectIncoming,
            ..Default::default()
        };
        let bus = InprocBus::new(&config);
        bus.publish(Scope::Process, vec![clause(1, &[1], 0.1)])
            .unwrap();
        let result = bus.publish(Scope::Process, vec![clause(2, &[2], 0.9)]);
        assert!(matches!(result, Err(BusError::BufferFull)));
    }

    #[test]
    fn poll_drains_whole_queue_respecting_budget() {
        let bus = under_protocol(|bus| {
            for i in 0..5 {
                bus.publish(Scope::Process, vec![clause(i, &[i as u32], 0.5)])
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
        let config = BusConfig {
            process_buffer: 1,
            eviction: EvictionPolicy::Oldest,
            ..Default::default()
        };
        let bus = InprocBus::new(&config);
        bus.publish(Scope::Process, vec![clause(1, &[1], 0.5)])
            .unwrap();
        // Evicts the unconditional (x1), freeing the conclusion for reuse by a
        // conditional.
        bus.publish(Scope::Process, vec![clause(2, &[2], 0.5)])
            .unwrap();
        let h = bus
            .publish(Scope::Process, vec![clause_with(3, &[1], &[-3], 0.5)])
            .unwrap();
        assert_eq!(
            h.enqueued, 1,
            "conditional accepted after unconditional evicted"
        );
    }
}
