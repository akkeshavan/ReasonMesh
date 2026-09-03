//! Orchestrator: worker lifecycle, failure recovery, and primary/hot-standby
//! high availability (spec §13.4).
//!
//! The [`Orchestrator`] wraps an `rm_scheduler::Scheduler` and adds:
//!
//! - **Worker registry:** workers must `admit` and then send heartbeats. A
//!   worker that misses `heartbeat_timeout` is declared dead; its leases are
//!   reaped (shutdown tokens tripped, nodes re-opened) so other workers can
//!   take over.
//! - **Write-ahead log (WAL):** every mutation is appended as a
//!   [`WalEntry`]. The primary persists it after each mutation.
//! - **Hot-standby:** a [`Standby`] receives/replays the WAL and keeps an
//!   in-memory shadow. On primary failure it calls [`Standby::promote`] to
//!   produce a live [`Orchestrator`] within one heartbeat interval. In-flight
//!   work continues; lease timers reset on reconnect.

use rm_akx::{Literal, ProblemId, WorkBudget};
use rm_scheduler::{
    CoverageCertificate, Lease, NodeId, NodeResult, Scheduler, SchedulerError, Verdict,
};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::time::{Duration, Instant};

/// Orchestrator configuration.
#[derive(Clone, Debug)]
pub struct OrchestratorConfig {
    /// Worker is declared dead if it misses this many heartbeats.
    pub heartbeat_timeout: Duration,
    /// How long a worker may hold a node between heartbeats without being
    /// reaped (a multiple of the heartbeat interval).
    pub lease_ttl: Duration,
    /// Maximum cube-split depth (None = unbounded).
    pub max_split_depth: Option<usize>,
}

impl Default for OrchestratorConfig {
    fn default() -> Self {
        OrchestratorConfig {
            heartbeat_timeout: Duration::from_secs(5),
            lease_ttl: Duration::from_secs(30),
            max_split_depth: None,
        }
    }
}

/// A registered worker and its liveness state.
#[derive(Clone, Debug)]
pub struct WorkerRecord {
    pub worker_id: u32,
    pub last_heartbeat: Instant,
    pub dead: bool,
}

impl WorkerRecord {
    pub fn is_alive(&self) -> bool {
        !self.dead
    }
}

/// One serializable mutation record in the write-ahead log.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum WalEntry {
    WorkerAdmitted {
        worker: u32,
    },
    Heartbeat {
        worker: u32,
    },
    /// Node dispatched to a worker (records the node + budget for replay).
    Dispatch {
        worker: u32,
        node: NodeId,
        budget_ms: u64,
        budget_conflicts: u64,
    },
    /// Terminal worker outcome for a node.
    Result {
        worker: u32,
        node: NodeId,
        outcome: WalOutcome,
    },
    /// A node was split into children (literals reconstruct the certificate).
    Split {
        worker: u32,
        node: NodeId,
        children: Vec<NodeId>,
        literals: Vec<Literal>,
    },
    /// A worker was declared dead and its leases reaped.
    WorkerDead {
        worker: u32,
    },
    /// Global cancellation (validated SAT or orchestrator shutdown).
    CancelAll,
}

/// Terminal outcome serialized into the WAL.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum WalOutcome {
    Sat,
    Unsat,
    Cancelled,
}

/// Errors from orchestrator operations.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum OrchestratorError {
    #[error("worker {0} is not registered")]
    UnknownWorker(u32),
    #[error("worker {0} is dead")]
    DeadWorker(u32),
    #[error("scheduler error: {0}")]
    Scheduler(#[from] SchedulerError),
}

/// The primary orchestrator.
pub struct Orchestrator {
    scheduler: Scheduler,
    config: OrchestratorConfig,
    workers: HashMap<u32, WorkerRecord>,
    wal: Vec<WalEntry>,
}

impl Orchestrator {
    pub fn new(problem: ProblemId, root_cube: Vec<Literal>, config: OrchestratorConfig) -> Self {
        let scheduler = Scheduler::new(problem, root_cube, config.max_split_depth)
            .with_lease_ttl(config.lease_ttl);
        Orchestrator {
            scheduler,
            config,
            workers: HashMap::new(),
            wal: Vec::new(),
        }
    }

    /// Rebuild an orchestrator by replaying a WAL (used by the standby on
    /// promotion). Replays every entry against a fresh scheduler, which is
    /// deterministic given the same ordered sequence.
    pub fn replay(
        problem: ProblemId,
        root_cube: Vec<Literal>,
        config: OrchestratorConfig,
        wal: &[WalEntry],
    ) -> Result<Self, OrchestratorError> {
        let mut o = Orchestrator::new(problem, root_cube, config.clone());
        for entry in wal {
            o.apply_replay(entry.clone())?;
        }
        o.wal = wal.to_vec();
        Ok(o)
    }

    fn find_lease_for_node(&self, worker: u32, node: NodeId) -> Result<u64, OrchestratorError> {
        self.scheduler
            .leases()
            .leases_for_worker(worker)
            .into_iter()
            .find(|id| {
                self.scheduler
                    .leases()
                    .get(*id)
                    .is_some_and(|l| l.node_id == node)
            })
            .ok_or(OrchestratorError::Scheduler(SchedulerError::UnknownNode(
                node,
            )))
    }

    fn replay_dispatch(
        &mut self,
        worker: u32,
        node: NodeId,
        budget_ms: u64,
        budget_conflicts: u64,
        now: Instant,
    ) -> Result<(), OrchestratorError> {
        let budget = WorkBudget {
            max_conflicts: budget_conflicts,
            max_ms: budget_ms,
        };
        let lease = self.scheduler.dispatch(worker, budget, now)?;
        if lease.node_id != node {
            return Err(OrchestratorError::Scheduler(SchedulerError::Finished(
                format!("WAL replay dispatched {node:?}, scheduler picked {node:?}"),
            )));
        }
        Ok(())
    }

    fn replay_result(
        &mut self,
        worker: u32,
        node: NodeId,
        outcome: WalOutcome,
    ) -> Result<(), OrchestratorError> {
        let lease_id = self.find_lease_for_node(worker, node)?;
        let result = match outcome {
            WalOutcome::Sat => NodeResult::Sat,
            WalOutcome::Unsat => NodeResult::Unsat,
            WalOutcome::Cancelled => NodeResult::Cancelled,
        };
        self.scheduler.on_result(lease_id, worker, result)?;
        Ok(())
    }

    fn replay_split(
        &mut self,
        worker: u32,
        node: NodeId,
        children: Vec<NodeId>,
        literals: Vec<Literal>,
    ) -> Result<(), OrchestratorError> {
        let lease_id = self.find_lease_for_node(worker, node)?;
        let cert = CoverageCertificate::tautology(literals).map_err(|_| {
            OrchestratorError::Scheduler(SchedulerError::Finished(
                "WAL split certificate invalid".into(),
            ))
        })?;
        let got = self
            .scheduler
            .split(lease_id, worker, cert.literals.clone(), cert)?;
        if got != children {
            return Err(OrchestratorError::Scheduler(SchedulerError::Finished(
                "WAL split produced different children".into(),
            )));
        }
        Ok(())
    }

    /// Apply a WAL entry during standby replay. Node ids are re-derived by
    /// re-running the deterministic scheduler operations.
    fn apply_replay(&mut self, entry: WalEntry) -> Result<(), OrchestratorError> {
        let now = Instant::now();
        match entry {
            WalEntry::WorkerAdmitted { worker } => {
                self.workers.insert(
                    worker,
                    WorkerRecord {
                        worker_id: worker,
                        last_heartbeat: now,
                        dead: false,
                    },
                );
            }
            WalEntry::Heartbeat { worker } => {
                if let Some(r) = self.workers.get_mut(&worker) {
                    r.last_heartbeat = now;
                }
            }
            WalEntry::Dispatch {
                worker,
                node,
                budget_ms,
                budget_conflicts,
            } => {
                self.replay_dispatch(worker, node, budget_ms, budget_conflicts, now)?;
            }
            WalEntry::Result {
                worker,
                node,
                outcome,
            } => {
                self.replay_result(worker, node, outcome)?;
            }
            WalEntry::Split {
                worker,
                node,
                children,
                literals,
            } => {
                self.replay_split(worker, node, children, literals)?;
            }
            WalEntry::WorkerDead { worker } => {
                if let Some(r) = self.workers.get_mut(&worker) {
                    r.dead = true;
                }
                self.scheduler.reap_worker(worker);
            }
            WalEntry::CancelAll => {
                self.scheduler.cancel_all();
            }
        }
        Ok(())
    }

    /// Register a worker.
    pub fn admit_worker(&mut self, worker: u32) {
        self.wal.push(WalEntry::WorkerAdmitted { worker });
        self.workers.insert(
            worker,
            WorkerRecord {
                worker_id: worker,
                last_heartbeat: Instant::now(),
                dead: false,
            },
        );
    }

    /// Record a heartbeat from `worker`. Unknown or dead workers are ignored
    /// (the entry is still logged so the standby sees the same sequence).
    pub fn heartbeat(&mut self, worker: u32) {
        self.wal.push(WalEntry::Heartbeat { worker });
        if let Some(r) = self.workers.get_mut(&worker) {
            if !r.dead {
                r.last_heartbeat = Instant::now();
                let leases = self.scheduler.leases().leases_for_worker(worker);
                let now = Instant::now();
                for id in leases {
                    let _ = self.scheduler.renew_lease(id, worker, now);
                }
            }
        }
    }

    /// Check every worker's heartbeat; declare stale workers dead and reap
    /// their leases. Returns the ids declared dead this round.
    pub fn reap_stale(&mut self) -> Vec<u32> {
        let now = Instant::now();
        let mut dead: Vec<u32> = Vec::new();
        for (id, record) in &self.workers {
            if !record.dead && now - record.last_heartbeat > self.config.heartbeat_timeout {
                dead.push(*id);
            }
        }
        for id in &dead {
            self.wal.push(WalEntry::WorkerDead { worker: *id });
            if let Some(r) = self.workers.get_mut(id) {
                r.dead = true;
            }
            self.scheduler.reap_worker(*id);
        }
        dead
    }

    /// Dispatch a node to `worker` (which must be registered and alive).
    pub fn dispatch(
        &mut self,
        worker: u32,
        budget: WorkBudget,
    ) -> Result<Lease, OrchestratorError> {
        let record = self
            .workers
            .get(&worker)
            .ok_or(OrchestratorError::UnknownWorker(worker))?;
        if record.dead {
            return Err(OrchestratorError::DeadWorker(worker));
        }
        let lease = self.scheduler.dispatch(worker, budget, Instant::now())?;
        self.wal.push(WalEntry::Dispatch {
            worker,
            node: lease.node_id,
            budget_ms: budget.max_ms,
            budget_conflicts: budget.max_conflicts,
        });
        Ok(lease)
    }

    /// Report a terminal worker outcome.
    pub fn on_result(
        &mut self,
        lease: &Lease,
        worker: u32,
        result: NodeResult,
    ) -> Result<Verdict, OrchestratorError> {
        let outcome = match result {
            NodeResult::Sat => WalOutcome::Sat,
            NodeResult::Unsat => WalOutcome::Unsat,
            NodeResult::Cancelled => WalOutcome::Cancelled,
            NodeResult::Split(_) => {
                return Ok(self.scheduler.verdict());
            }
        };
        self.wal.push(WalEntry::Result {
            worker,
            node: lease.node_id,
            outcome,
        });
        let verdict = self.scheduler.on_result(lease.lease_id, worker, result)?;
        if verdict != Verdict::Unknown {
            self.wal.push(WalEntry::CancelAll);
        }
        Ok(verdict)
    }

    /// Split the node behind `lease` into children, recording the certificate.
    pub fn split(
        &mut self,
        lease: &Lease,
        worker: u32,
        literals: Vec<Literal>,
        certificate: CoverageCertificate,
    ) -> Result<Vec<NodeId>, OrchestratorError> {
        let children =
            self.scheduler
                .split(lease.lease_id, worker, literals.clone(), certificate)?;
        self.wal.push(WalEntry::Split {
            worker,
            node: lease.node_id,
            children: children.clone(),
            literals,
        });
        Ok(children)
    }

    pub fn verdict(&self) -> Verdict {
        self.scheduler.verdict()
    }

    pub fn is_finished(&self) -> bool {
        self.scheduler.is_finished()
    }

    pub fn worker(&self, worker: u32) -> Option<&WorkerRecord> {
        self.workers.get(&worker)
    }

    pub fn workers(&self) -> &HashMap<u32, WorkerRecord> {
        &self.workers
    }

    pub fn scheduler(&self) -> &Scheduler {
        &self.scheduler
    }

    /// The write-ahead log accumulated so far.
    pub fn wal(&self) -> &[WalEntry] {
        &self.wal
    }

    /// Serialize the WAL for persistence/replication.
    pub fn wal_to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string(&self.wal)
    }

    pub fn lease_count(&self) -> usize {
        self.scheduler.leases().len()
    }
}

/// A hot-standby that mirrors the primary's WAL. On primary failure it
/// promotes to a live [`Orchestrator`].
pub struct Standby {
    problem: ProblemId,
    root_cube: Vec<Literal>,
    config: OrchestratorConfig,
    wal: Vec<WalEntry>,
}

impl Standby {
    pub fn new(problem: ProblemId, root_cube: Vec<Literal>, config: OrchestratorConfig) -> Self {
        Standby {
            problem,
            root_cube,
            config,
            wal: Vec::new(),
        }
    }

    /// Append entries received from the primary.
    pub fn append(&mut self, entries: &[WalEntry]) {
        self.wal.extend_from_slice(entries);
    }

    pub fn wal_len(&self) -> usize {
        self.wal.len()
    }

    /// Become primary: replay the WAL into a fresh orchestrator. Fails if the
    /// WAL is inconsistent.
    pub fn promote(&self) -> Result<Orchestrator, OrchestratorError> {
        Orchestrator::replay(
            self.problem,
            self.root_cube.clone(),
            self.config.clone(),
            &self.wal,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn budget() -> WorkBudget {
        WorkBudget {
            max_conflicts: 100,
            max_ms: 100,
        }
    }

    fn cfg() -> OrchestratorConfig {
        OrchestratorConfig {
            heartbeat_timeout: Duration::from_millis(50),
            lease_ttl: Duration::from_secs(10),
            max_split_depth: None,
        }
    }

    fn root_split_literals() -> Vec<Literal> {
        vec![Literal::positive(1), Literal::negative(1)]
    }

    #[test]
    fn admit_dispatch_result_sat() {
        let mut o = Orchestrator::new(ProblemId(1), vec![], cfg());
        o.admit_worker(1);
        let lease = o.dispatch(1, budget()).unwrap();
        o.on_result(&lease, 1, NodeResult::Sat).unwrap();
        assert_eq!(o.verdict(), Verdict::Sat);
        // WAL ends with CancelAll after a terminal verdict.
        assert!(matches!(o.wal().last(), Some(WalEntry::CancelAll)));
    }

    #[test]
    fn dispatch_requires_registered_worker() {
        let mut o = Orchestrator::new(ProblemId(1), vec![], cfg());
        assert!(matches!(
            o.dispatch(1, budget()),
            Err(OrchestratorError::UnknownWorker(1))
        ));
    }

    #[test]
    fn stale_worker_is_reaped() {
        let mut o = Orchestrator::new(ProblemId(1), vec![], cfg());
        o.admit_worker(1);
        let lease = o.dispatch(1, budget()).unwrap();
        // No heartbeats: worker goes stale and is declared dead.
        std::thread::sleep(Duration::from_millis(80));
        let dead = o.reap_stale();
        assert_eq!(dead, vec![1]);
        assert!(o.worker(1).unwrap().dead);
        // Lease was reaped: node back to open, zero outstanding leases.
        assert_eq!(o.lease_count(), 0);
        assert_eq!(o.scheduler().tree().open_nodes(), vec![NodeId(0)]);
        let _ = lease;
    }

    #[test]
    fn heartbeat_keeps_worker_alive() {
        let mut o = Orchestrator::new(ProblemId(1), vec![], cfg());
        o.admit_worker(1);
        o.dispatch(1, budget()).unwrap();
        // Heartbeat every 20ms keeps the worker alive past the 50ms timeout.
        for _ in 0..6 {
            std::thread::sleep(Duration::from_millis(20));
            o.heartbeat(1);
        }
        assert!(o.reap_stale().is_empty());
        assert!(o.worker(1).unwrap().is_alive());
    }

    #[test]
    fn worker_failure_recovers_work() {
        let mut o = Orchestrator::new(ProblemId(1), vec![], cfg());
        o.admit_worker(1);
        let lease = o.dispatch(1, budget()).unwrap();
        let node = lease.node_id;
        // Worker 1 dies; another worker must be able to pick the node up.
        std::thread::sleep(Duration::from_millis(80));
        o.reap_stale();
        o.admit_worker(2);
        let lease2 = o.dispatch(2, budget()).unwrap();
        assert_eq!(lease2.node_id, node);
    }

    #[test]
    fn split_recorded_in_wal() {
        let mut o = Orchestrator::new(ProblemId(1), vec![], cfg());
        o.admit_worker(1);
        let lease = o.dispatch(1, budget()).unwrap();
        let lits = root_split_literals();
        let cert = CoverageCertificate::tautology(lits.clone()).unwrap();
        let children = o.split(&lease, 1, lits.clone(), cert).unwrap();
        assert_eq!(children.len(), 2);
        assert!(o.wal().iter().any(|e| matches!(e, WalEntry::Split { .. })));
    }

    #[test]
    fn standby_promotes_to_matching_orchestrator() {
        let mut primary = Orchestrator::new(ProblemId(1), vec![], cfg());
        primary.admit_worker(1);
        primary.admit_worker(2);
        let l1 = primary.dispatch(1, budget()).unwrap();
        let lits = root_split_literals();
        let cert = CoverageCertificate::tautology(lits.clone()).unwrap();
        let children = primary.split(&l1, 1, lits, cert).unwrap();

        // Standby mirrors everything.
        let mut standby = Standby::new(ProblemId(1), vec![], cfg());
        standby.append(primary.wal());

        // A dispatch + result on the standby's shadow must replay to the same
        // verdict as the primary.
        let promoted = standby.promote().unwrap();
        assert_eq!(promoted.wal(), primary.wal());

        // Both agree on the current tree shape.
        assert_eq!(
            promoted.scheduler().tree().node_count(),
            primary.scheduler().tree().node_count()
        );
        let _ = children;
    }

    #[test]
    fn standby_catches_up_with_split_and_result() {
        let mut primary = Orchestrator::new(ProblemId(1), vec![], cfg());
        primary.admit_worker(1);
        primary.admit_worker(2);
        let l1 = primary.dispatch(1, budget()).unwrap();
        let lits = root_split_literals();
        let cert = CoverageCertificate::tautology(lits.clone()).unwrap();
        let children = primary.split(&l1, 1, lits, cert).unwrap();

        // Close both children UNSAT.
        let c1 = primary.dispatch(2, budget()).unwrap();
        assert_eq!(c1.node_id, children[0]);
        primary.on_result(&c1, 2, NodeResult::Unsat).unwrap();
        let c2 = primary.dispatch(2, budget()).unwrap();
        assert_eq!(c2.node_id, children[1]);
        primary.on_result(&c2, 2, NodeResult::Unsat).unwrap();
        assert_eq!(primary.verdict(), Verdict::Unsat);

        // Standby replays to the same verdict.
        let mut standby = Standby::new(ProblemId(1), vec![], cfg());
        standby.append(primary.wal());
        let promoted = standby.promote().unwrap();
        assert_eq!(promoted.verdict(), Verdict::Unsat);
        assert_eq!(promoted.lease_count(), 0);
    }

    #[test]
    fn wal_json_roundtrip() {
        let mut o = Orchestrator::new(ProblemId(1), vec![], cfg());
        o.admit_worker(1);
        o.dispatch(1, budget()).unwrap();
        let json = o.wal_to_json().unwrap();
        let parsed: Vec<WalEntry> = serde_json::from_str(&json).unwrap();
        assert_eq!(parsed, o.wal());
    }
}
