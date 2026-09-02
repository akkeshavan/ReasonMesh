//! rm-scheduler — distributed work units, leases, dynamic cube splitting, and
//! partition trees with coverage certificates (spec §8, §13).

pub mod coverage;
pub mod lease;
pub mod tree;

pub use coverage::{CoverageCertificate, CoverageError};
pub use lease::{Lease, LeaseStore};
pub use tree::{NodeId, NodeStatus, PartitionNode, PartitionTree};

use rm_akx::{CubePath, Literal, Priority, ProblemId, WorkBudget, WorkUnit};
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};
use std::time::{Duration, Instant};

/// Errors surfaced by the scheduler.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum SchedulerError {
    #[error("unknown node {0:?}")]
    UnknownNode(NodeId),
    #[error("node {0:?} is not open")]
    NotOpen(NodeId),
    #[error("node {0:?} is not a leaf")]
    NotLeaf(NodeId),
    #[error("node {0:?} already closed")]
    AlreadyClosed(NodeId),
    #[error("node {0:?} at max split depth")]
    MaxDepth(NodeId),
    #[error("invalid close status {0:?}")]
    InvalidClose(NodeStatus),
    #[error("unknown lease {0}")]
    UnknownLease(u64),
    #[error("lease {0} is not held by worker {1}")]
    LeaseNotOwned(u64, u32),
    #[error("no open work unit available")]
    NoWork,
    #[error("problem finished: {0}")]
    Finished(String),
    #[error("coverage error: {0}")]
    Coverage(#[from] CoverageError),
}

/// A validated result from a worker for a leased node.
#[derive(Clone, Debug)]
pub enum NodeResult {
    /// A complete worker proved the cube unsatisfiable.
    Unsat,
    /// A validated model was found under the cube.
    Sat,
    /// The worker abandoned the unit (cancelled externally).
    Cancelled,
    /// The worker wants to split its node into the given children.
    Split(Vec<Literal>),
}

/// Aggregated scheduling state for telemetry.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct SchedulerStats {
    pub nodes: u64,
    pub open: u64,
    pub assigned: u64,
    pub closed_sat: u64,
    pub closed_unsat: u64,
    pub cancelled: u64,
    pub leases_outstanding: u64,
    pub splits: u64,
}

/// Work-load verdict.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum Verdict {
    Unknown,
    Sat,
    Unsat,
}

/// Coordinates partition-tree, lease, and work-unit lifecycle.
pub struct Scheduler {
    tree: PartitionTree,
    leases: LeaseStore,
    problem: ProblemId,
    lease_ttl: Duration,
    shutdown: Arc<AtomicBool>,
    splits: u64,
}

impl Scheduler {
    pub fn new(problem: ProblemId, root_cube: Vec<Literal>, max_depth: Option<usize>) -> Self {
        Scheduler {
            tree: PartitionTree::new(root_cube, max_depth),
            leases: LeaseStore::new(),
            problem,
            lease_ttl: Duration::from_secs(30),
            shutdown: Arc::new(AtomicBool::new(false)),
            splits: 0,
        }
    }

    /// Set the default lease TTL (how long a worker may hold a node without
    /// renewing before it is reaped).
    pub fn with_lease_ttl(mut self, ttl: Duration) -> Self {
        self.lease_ttl = ttl;
        self
    }

    /// The scheduler-wide shutdown token. Set when a validated SAT is found or
    /// the orchestrator cancels; copied into every dispatched `WorkUnit`.
    pub fn shutdown_token(&self) -> Arc<AtomicBool> {
        Arc::clone(&self.shutdown)
    }

    pub fn tree(&self) -> &PartitionTree {
        &self.tree
    }

    pub fn leases(&self) -> &LeaseStore {
        &self.leases
    }

    /// Cancel all outstanding work: trip the global token and the per-unit
    /// tokens, then release every lease. Used on validated SAT or orchestrator
    /// shutdown.
    pub fn cancel_all(&mut self) {
        // Release pairs with the Acquire/SeqCst loads in worker loops so the
        // cancellation is visible before any subsequent memory operations.
        self.shutdown.store(true, Ordering::Release);
        for lease in self.leases.drain_all() {
            lease.work_unit.shutdown.store(true, Ordering::Release);
        }
    }

    /// Dispatch the next open node to `worker_id`. Returns the lease.
    pub fn dispatch(
        &mut self,
        worker_id: u32,
        budget: WorkBudget,
        now: Instant,
    ) -> Result<Lease, SchedulerError> {
        if self.is_finished() {
            return Err(SchedulerError::Finished(format!("{:?}", self.verdict())));
        }
        let node_id = *self
            .tree
            .open_nodes()
            .first()
            .ok_or(SchedulerError::NoWork)?;
        self.tree.assign(node_id)?;
        let cube = self.tree.cube(node_id).unwrap().to_vec();
        let unit = self.build_work_unit(node_id, cube, budget);
        let id = self
            .leases
            .grant(node_id, worker_id, unit, self.lease_ttl, now);
        Ok(self.leases.get(id).unwrap().clone())
    }

    /// Report a worker result for a lease. Returns the new verdict.
    ///
    /// - `Sat`: cancels all work and marks the node closed-SAT.
    /// - `Unsat`: closes the node; if all leaves closed-UNSAT, cancels all.
    /// - `Cancelled`: releases the lease; node returns to `Open` unless the
    ///   global shutdown was tripped.
    /// - `Split(_)`: no-op for the tree (splits go through [`Scheduler::split`]).
    pub fn on_result(
        &mut self,
        lease_id: u64,
        worker_id: u32,
        result: NodeResult,
    ) -> Result<Verdict, SchedulerError> {
        let lease = self
            .leases
            .get(lease_id)
            .ok_or(SchedulerError::UnknownLease(lease_id))?;
        if lease.worker_id != worker_id {
            return Err(SchedulerError::LeaseNotOwned(lease_id, worker_id));
        }
        let node_id = lease.node_id;
        self.leases.release(lease_id);

        match result {
            NodeResult::Sat => {
                self.tree.close(node_id, NodeStatus::ClosedSat)?;
                self.cancel_all();
                Ok(Verdict::Sat)
            }
            NodeResult::Unsat => {
                self.tree.close(node_id, NodeStatus::ClosedUnsat)?;
                if self.tree.is_unsat() {
                    self.cancel_all();
                    Ok(Verdict::Unsat)
                } else {
                    Ok(self.verdict())
                }
            }
            NodeResult::Cancelled => {
                if !self.shutdown.load(Ordering::Relaxed) {
                    self.tree.close(node_id, NodeStatus::Cancelled)?;
                    self.tree.reopen(node_id)?;
                }
                Ok(self.verdict())
            }
            NodeResult::Split(_) => Ok(self.verdict()),
        }
    }

    /// Split the node behind `lease_id` into children `parent ∪ {l_i}`,
    /// verifying `certificate`. The worker must own the lease. Returns the
    /// child node ids.
    pub fn split(
        &mut self,
        lease_id: u64,
        worker_id: u32,
        literals: Vec<Literal>,
        certificate: CoverageCertificate,
    ) -> Result<Vec<NodeId>, SchedulerError> {
        let lease = self
            .leases
            .get(lease_id)
            .ok_or(SchedulerError::UnknownLease(lease_id))?;
        if lease.worker_id != worker_id {
            return Err(SchedulerError::LeaseNotOwned(lease_id, worker_id));
        }
        let node_id = lease.node_id;
        self.leases.release(lease_id);
        let children = self.tree.split(node_id, literals, certificate)?;
        self.splits += 1;
        Ok(children)
    }

    /// Renew a lease so the worker can keep the node.
    pub fn renew_lease(
        &mut self,
        lease_id: u64,
        worker_id: u32,
        now: Instant,
    ) -> Result<(), SchedulerError> {
        if !self.leases.is_owned_by(lease_id, worker_id) {
            return Err(SchedulerError::LeaseNotOwned(lease_id, worker_id));
        }
        self.leases.renew(lease_id, self.lease_ttl, now)
    }

    /// Reap expired leases: trip their shutdown tokens and re-open their
    /// nodes so other workers can take them over. Returns the number reaped.
    pub fn reap_expired(&mut self, now: Instant) -> usize {
        let expired = self.leases.expired_ids(now);
        let mut reaped = 0;
        for id in expired {
            if let Some(lease) = self.leases.release(id) {
                lease.work_unit.shutdown.store(true, Ordering::Release);
                if self.tree.reopen(lease.node_id).is_ok() {
                    reaped += 1;
                }
            }
        }
        reaped
    }

    /// Reap every lease held by `worker_id`: trip their shutdown tokens and
    /// re-open their nodes. Returns the number of leases reaped. Used when the
    /// orchestrator declares a worker dead (heartbeat timeout).
    pub fn reap_worker(&mut self, worker_id: u32) -> usize {
        let ids = self.leases.leases_for_worker(worker_id);
        let mut reaped = 0;
        for id in ids {
            if let Some(lease) = self.leases.release(id) {
                lease.work_unit.shutdown.store(true, Ordering::Release);
                if self.tree.reopen(lease.node_id).is_ok() {
                    reaped += 1;
                }
            }
        }
        reaped
    }

    /// Global termination verdict.
    pub fn verdict(&self) -> Verdict {
        if self.tree.is_sat() {
            Verdict::Sat
        } else if self.tree.is_unsat() {
            Verdict::Unsat
        } else {
            Verdict::Unknown
        }
    }

    pub fn is_finished(&self) -> bool {
        self.verdict() != Verdict::Unknown
    }

    pub fn stats(&self) -> SchedulerStats {
        SchedulerStats {
            nodes: self.tree.node_count() as u64,
            open: self.tree.open_nodes().len() as u64,
            assigned: self.tree.active_leaves().len() as u64,
            closed_sat: self.count_status(NodeStatus::ClosedSat),
            closed_unsat: self.count_status(NodeStatus::ClosedUnsat),
            cancelled: self.count_status(NodeStatus::Cancelled),
            leases_outstanding: self.leases.len() as u64,
            splits: self.splits,
        }
    }

    fn count_status(&self, status: NodeStatus) -> u64 {
        let mut n = 0;
        for node in self.tree.nodes() {
            if node.status == status {
                n += 1;
            }
        }
        n
    }

    fn build_work_unit(&self, node_id: NodeId, cube: Vec<Literal>, budget: WorkBudget) -> WorkUnit {
        let _ = node_id;
        WorkUnit {
            problem: self.problem,
            assumptions: cube,
            ancestry: CubePath::default(),
            priority: Priority::NORMAL,
            budget,
            seed: 0,
            shutdown: Arc::clone(&self.shutdown),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scheduler() -> Scheduler {
        Scheduler::new(ProblemId(1), vec![], None).with_lease_ttl(Duration::from_secs(10))
    }

    fn budget() -> WorkBudget {
        WorkBudget {
            max_conflicts: 100,
            max_ms: 100,
        }
    }

    #[test]
    fn dispatch_assigns_root() {
        let mut s = scheduler();
        let now = Instant::now();
        let lease = s.dispatch(1, budget(), now).unwrap();
        assert_eq!(lease.node_id, NodeId(0));
        assert_eq!(lease.worker_id, 1);
        assert_eq!(s.verdict(), Verdict::Unknown);
    }

    #[test]
    fn sat_cancels_all() {
        let mut s = scheduler();
        let now = Instant::now();
        let l = s.dispatch(1, budget(), now).unwrap();
        s.on_result(l.lease_id, 1, NodeResult::Sat).unwrap();
        assert_eq!(s.verdict(), Verdict::Sat);
        assert!(s.shutdown.load(Ordering::Relaxed));
        assert_eq!(s.leases.len(), 0);
    }

    #[test]
    fn unsat_requires_all_leaves() {
        let mut s = scheduler();
        let now = Instant::now();
        // Split root into x1 / ¬x1.
        let lits = vec![Literal::positive(1), Literal::negative(1)];
        let cert = CoverageCertificate::tautology(lits.clone()).unwrap();
        let l = s.dispatch(1, budget(), now).unwrap();
        let children = s.split(l.lease_id, 1, lits, cert).unwrap();
        assert_eq!(children.len(), 2);

        // Close the first child as UNSAT (dispatch + report).
        let c1 = s.dispatch(2, budget(), now).unwrap();
        assert_eq!(
            s.on_result(c1.lease_id, 2, NodeResult::Unsat).unwrap(),
            Verdict::Unknown
        );

        // Not yet UNSAT: second leaf still open.
        assert_eq!(s.verdict(), Verdict::Unknown);

        let c2 = s.dispatch(3, budget(), now).unwrap();
        let v = s.on_result(c2.lease_id, 3, NodeResult::Unsat).unwrap();
        assert_eq!(v, Verdict::Unsat);
    }

    #[test]
    fn expired_lease_reopens_node() {
        let mut s = scheduler();
        let now = Instant::now();
        let l = s.dispatch(1, budget(), now).unwrap();
        // Worker goes silent past the TTL.
        let later = now + Duration::from_secs(11);
        let reaped = s.reap_expired(later);
        assert_eq!(reaped, 1);
        assert!(l.work_unit.shutdown.load(Ordering::Relaxed));
        assert_eq!(s.tree().get(NodeId(0)).unwrap().status, NodeStatus::Open);
        // Another worker can take it over.
        let l2 = s.dispatch(2, budget(), later).unwrap();
        assert_eq!(l2.node_id, NodeId(0));
    }

    #[test]
    fn cancelled_releases_and_reopens() {
        let mut s = scheduler();
        let now = Instant::now();
        let l = s.dispatch(1, budget(), now).unwrap();
        s.on_result(l.lease_id, 1, NodeResult::Cancelled).unwrap();
        assert_eq!(s.tree().get(NodeId(0)).unwrap().status, NodeStatus::Open);
    }

    #[test]
    fn wrong_worker_rejected() {
        let mut s = scheduler();
        let now = Instant::now();
        let l = s.dispatch(1, budget(), now).unwrap();
        assert!(matches!(
            s.on_result(l.lease_id, 2, NodeResult::Unsat),
            Err(SchedulerError::LeaseNotOwned(_, _))
        ));
    }

    #[test]
    fn split_with_invalid_coverage_rejected() {
        let mut s = scheduler();
        let now = Instant::now();
        let l = s.dispatch(1, budget(), now).unwrap();
        let bad_lits = vec![Literal::positive(1), Literal::positive(2)];
        let bad_cert = CoverageCertificate::tautology(bad_lits.clone());
        assert!(matches!(bad_cert, Err(crate::CoverageError::NotCovering)));
        // A forged certificate that doesn't match the literals is rejected.
        let cert = CoverageCertificate::tautology(vec![Literal::positive(1), Literal::negative(1)])
            .unwrap();
        assert!(s.split(l.lease_id, 1, bad_lits, cert).is_err());
    }

    #[test]
    fn deep_split_tree() {
        let mut s = scheduler();
        let now = Instant::now();
        let l = s.dispatch(1, budget(), now).unwrap();
        let lits = vec![Literal::positive(1), Literal::negative(1)];
        let cert = CoverageCertificate::tautology(lits.clone()).unwrap();
        let children = s.split(l.lease_id, 1, lits, cert).unwrap();
        // Split child 0 again on x2.
        let c0 = s.dispatch(2, budget(), now).unwrap();
        assert_eq!(c0.node_id, children[0]);
        let lits2 = vec![Literal::positive(2), Literal::negative(2)];
        let cert2 = CoverageCertificate::tautology(lits2.clone()).unwrap();
        s.split(c0.lease_id, 2, lits2, cert2).unwrap();
        assert_eq!(s.stats().nodes, 5);
        assert_eq!(s.stats().splits, 2);
    }
}
