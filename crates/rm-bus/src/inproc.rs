//! In-process bounded knowledge bus backed by crossbeam channels.
//!
//! This is the primary bus for single-machine multi-worker configurations.
//! Multiple workers share one `InprocBus` instance via `Arc<InprocBus>`.

use crate::{BusConfig, BusError, EvictionPolicy, KnowledgeBus, PollBudget, PublishHandle};
use crossbeam_channel::{bounded, Receiver, Sender, TrySendError};
use rm_akx::{knowledge::canonical_key, BusMetrics, KnowledgeBatch, KnowledgeObject, Scope};
use rustc_hash::FxHashSet;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Mutex;

/// In-process bus using a single bounded MPMC channel.
///
/// All scope levels (Local, Process, Node, Global) are collapsed into one
/// channel for the in-process case — scope is only meaningful for network
/// transport where it controls routing.
pub struct InprocBus {
    sender: Sender<KnowledgeObject>,
    receiver: Receiver<KnowledgeObject>,
    /// Canonical keys of objects currently in the channel (approximate —
    /// items may be consumed concurrently). Used to skip obvious duplicates.
    seen: Mutex<FxHashSet<u64>>,
    // Metrics counters.
    published: AtomicU64,
    polled: AtomicU64,
    deduplicated: AtomicU64,
    evicted: AtomicU64,
}

impl InprocBus {
    pub fn new(config: &BusConfig) -> Self {
        let cap = config.process_buffer;
        let (sender, receiver) = bounded(cap);
        InprocBus {
            sender,
            receiver,
            seen: Mutex::new(FxHashSet::default()),
            published: AtomicU64::new(0),
            polled: AtomicU64::new(0),
            deduplicated: AtomicU64::new(0),
            evicted: AtomicU64::new(0),
        }
    }
}

impl KnowledgeBus for InprocBus {
    fn publish(
        &self,
        _scope: Scope,
        batch: KnowledgeBatch,
    ) -> Result<PublishHandle, BusError> {
        let mut enqueued = 0usize;
        let mut seen = self.seen.lock().unwrap();

        for obj in batch {
            let key = canonical_key(&obj);
            if seen.contains(&key) {
                self.deduplicated.fetch_add(1, Ordering::Relaxed);
                continue;
            }
            match self.sender.try_send(obj) {
                Ok(()) => {
                    seen.insert(key);
                    self.published.fetch_add(1, Ordering::Relaxed);
                    enqueued += 1;
                }
                Err(TrySendError::Full(_)) => {
                    // Channel full — signal back-pressure.
                    return Err(BusError::BufferFull);
                }
                Err(TrySendError::Disconnected(_)) => {
                    return Err(BusError::Disconnected);
                }
            }
        }
        Ok(PublishHandle { enqueued })
    }

    fn poll(&self, budget: PollBudget) -> Result<KnowledgeBatch, BusError> {
        let mut batch = Vec::with_capacity(budget.max_items.min(64));
        let mut seen = self.seen.lock().unwrap();

        for _ in 0..budget.max_items {
            match self.receiver.try_recv() {
                Ok(obj) => {
                    let key = canonical_key(&obj);
                    // Remove from seen so future identical objects can be
                    // accepted if needed (channel slot is now free).
                    seen.remove(&key);
                    batch.push(obj);
                    self.polled.fetch_add(1, Ordering::Relaxed);
                }
                Err(_) => break,
            }
        }
        Ok(batch)
    }

    fn metrics(&self) -> BusMetrics {
        let cap = self.sender.capacity().unwrap_or(0) as f32;
        let used = self.sender.len() as f32;
        BusMetrics {
            published_total: self.published.load(Ordering::Relaxed),
            polled_total: self.polled.load(Ordering::Relaxed),
            deduplicated: self.deduplicated.load(Ordering::Relaxed),
            evicted: self.evicted.load(Ordering::Relaxed),
            buffer_utilization: if cap > 0.0 { used / cap } else { 0.0 },
            ..Default::default()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rm_akx::{
        knowledge::{ClauseKnowledge, KnowledgeId, KnowledgeKind, KnowledgeObject, Scope, TrustLevel},
        literal::Literal,
    };
    fn make_clause(id: u64, lits: &[u32]) -> KnowledgeObject {
        KnowledgeObject {
            id: KnowledgeId(id),
            kind: KnowledgeKind::Clause(ClauseKnowledge {
                literals: lits.iter().map(|&v| Literal::positive(v)).collect(),
                lbd: 2,
            }),
            assumptions: Default::default(),
            scope: Scope::Process,
            trust: TrustLevel::Trusted,
            utility: 0.5,
            proof_ref: None,
            source: 0,
        }
    }

    #[test]
    fn publish_and_poll() {
        let bus = InprocBus::new(&BusConfig::default());
        let obj = make_clause(1, &[0, 1, 2]);
        bus.publish(Scope::Process, vec![obj]).unwrap();
        let polled = bus.poll(PollBudget { max_items: 10 }).unwrap();
        assert_eq!(polled.len(), 1);
    }

    #[test]
    fn deduplication() {
        let bus = InprocBus::new(&BusConfig::default());
        let obj = make_clause(1, &[0, 1, 2]);
        bus.publish(Scope::Process, vec![obj.clone()]).unwrap();
        // Second publish of the same clause should be deduplicated.
        let h = bus.publish(Scope::Process, vec![obj]).unwrap();
        assert_eq!(h.enqueued, 0);
        assert_eq!(bus.deduplicated.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn back_pressure() {
        let config = BusConfig { process_buffer: 2, ..Default::default() };
        let bus = InprocBus::new(&config);
        bus.publish(Scope::Process, vec![make_clause(1, &[0])]).unwrap();
        bus.publish(Scope::Process, vec![make_clause(2, &[1])]).unwrap();
        // Third publish should hit back-pressure.
        let result = bus.publish(Scope::Process, vec![make_clause(3, &[2])]);
        assert!(matches!(result, Err(BusError::BufferFull)));
    }
}
