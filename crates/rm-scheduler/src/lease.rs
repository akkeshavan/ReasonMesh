//! Lease tracking for distributed work units (§8.2, §13.4).
//!
//! A worker holds a lease on a partition node for `ttl`. The orchestrator
//! renews leases as workers report progress; expired leases are reaped and
//! their nodes returned to the open pool for reassignment. On lease expiry
//! the worker's `WorkUnit::shutdown` token is tripped so it abandons the
//! unit promptly.

use rm_akx::WorkUnit;
use std::collections::HashMap;
use std::time::{Duration, Instant};

use crate::{NodeId, SchedulerError};

/// A grant of ownership over a partition node to one worker.
#[derive(Clone, Debug)]
pub struct Lease {
    pub lease_id: u64,
    /// Partition node this lease covers.
    pub node_id: NodeId,
    /// Worker that holds the lease.
    pub worker_id: u32,
    /// When this lease expires.
    pub expires_at: Instant,
    /// The dispatched work unit (carries the node's cube and shutdown token).
    pub work_unit: WorkUnit,
}

impl Lease {
    pub fn is_expired(&self, now: Instant) -> bool {
        now >= self.expires_at
    }
}

/// Maps leases to their owners; owns the id counter.
#[derive(Debug, Default)]
pub struct LeaseStore {
    leases: HashMap<u64, Lease>,
    next_id: u64,
}

impl LeaseStore {
    pub fn new() -> Self {
        Self::default()
    }

    /// Grant a lease with the given TTL. Returns the new lease id.
    pub fn grant(
        &mut self,
        node_id: NodeId,
        worker_id: u32,
        work_unit: WorkUnit,
        ttl: Duration,
        now: Instant,
    ) -> u64 {
        let id = self.next_id;
        self.next_id += 1;
        self.leases.insert(
            id,
            Lease {
                lease_id: id,
                node_id,
                worker_id,
                expires_at: now + ttl,
                work_unit,
            },
        );
        id
    }

    pub fn get(&self, lease_id: u64) -> Option<&Lease> {
        self.leases.get(&lease_id)
    }

    pub fn get_mut(&mut self, lease_id: u64) -> Option<&mut Lease> {
        self.leases.get_mut(&lease_id)
    }

    /// Remove and return the lease, if present.
    pub fn release(&mut self, lease_id: u64) -> Option<Lease> {
        self.leases.remove(&lease_id)
    }

    /// Remove and return every lease (used by `cancel_all`).
    pub fn drain_all(&mut self) -> Vec<Lease> {
        std::mem::take(&mut self.leases).into_values().collect()
    }

    pub fn len(&self) -> usize {
        self.leases.len()
    }

    pub fn is_empty(&self) -> bool {
        self.leases.is_empty()
    }

    /// Collect ids of all leases that have expired by `now`, *without*
    /// removing them. Callers typically follow up with `release`.
    pub fn expired_ids(&self, now: Instant) -> Vec<u64> {
        self.leases
            .iter()
            .filter(|(_, l)| l.is_expired(now))
            .map(|(id, _)| *id)
            .collect()
    }

    /// Renew a lease's deadline. Returns an error if the lease is unknown.
    pub fn renew(
        &mut self,
        lease_id: u64,
        ttl: Duration,
        now: Instant,
    ) -> Result<(), SchedulerError> {
        match self.leases.get_mut(&lease_id) {
            Some(l) => {
                l.expires_at = now + ttl;
                Ok(())
            }
            None => Err(SchedulerError::UnknownLease(lease_id)),
        }
    }

    /// True if `lease_id` names a lease held by `worker_id`.
    pub fn is_owned_by(&self, lease_id: u64, worker_id: u32) -> bool {
        self.leases
            .get(&lease_id)
            .is_some_and(|l| l.worker_id == worker_id)
    }

    /// Collect all lease ids currently held by `worker_id`.
    pub fn leases_for_worker(&self, worker_id: u32) -> Vec<u64> {
        self.leases
            .iter()
            .filter(|(_, l)| l.worker_id == worker_id)
            .map(|(id, _)| *id)
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rm_akx::{CubePath, Priority, ProblemId, WorkBudget};

    fn unit(id: u64, assumptions: &[rm_akx::Literal]) -> WorkUnit {
        WorkUnit {
            problem: ProblemId(1),
            assumptions: assumptions.to_vec(),
            ancestry: CubePath::default(),
            priority: Priority::NORMAL,
            budget: WorkBudget::default(),
            seed: id,
            shutdown: std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false)),
        }
    }

    #[test]
    fn grant_and_renew() {
        let mut store = LeaseStore::new();
        let now = Instant::now();
        let id = store.grant(NodeId(0), 7, unit(1, &[]), Duration::from_secs(10), now);
        assert!(store.is_owned_by(id, 7));
        assert!(!store.is_owned_by(id, 8));
        store.renew(id, Duration::from_secs(30), now).unwrap();
        assert!(!store
            .get(id)
            .unwrap()
            .is_expired(now + Duration::from_secs(20)));
    }

    #[test]
    fn expiry_collects_and_releases() {
        let mut store = LeaseStore::new();
        let now = Instant::now();
        let a = store.grant(NodeId(0), 1, unit(1, &[]), Duration::from_secs(5), now);
        let b = store.grant(NodeId(1), 2, unit(2, &[]), Duration::from_secs(60), now);

        let expired = store.expired_ids(now + Duration::from_secs(6));
        assert_eq!(expired, vec![a]);

        let leased = store.release(a).unwrap();
        assert_eq!(leased.node_id, NodeId(0));
        assert_eq!(store.len(), 1);
        assert_eq!(store.get(b).unwrap().worker_id, 2);
    }

    #[test]
    fn renew_unknown_lease_errors() {
        let mut store = LeaseStore::new();
        assert!(matches!(
            store.renew(99, Duration::from_secs(1), Instant::now()),
            Err(SchedulerError::UnknownLease(99))
        ));
    }
}
