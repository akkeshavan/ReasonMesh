//! Shared coordinator state and all mutations.
//!
//! All state lives behind a `parking_lot::Mutex` so mutations are synchronous
//! and brief — no async work is done under the lock. The long-poll mechanism
//! uses a separate `tokio::sync::Semaphore` whose permit count tracks the
//! number of tasks currently in the queue.

use crate::job::*;
use std::collections::{HashMap, VecDeque};
use std::time::{Duration, Instant};
use uuid::Uuid;

pub struct WorkerInfo {
    pub id: u32,
    pub last_seen: Instant,
}

pub struct CoordinatorState {
    pub batch_jobs: HashMap<JobId, BatchJob>,
    pub cube_jobs: HashMap<JobId, CubeJob>,
    /// Pending tasks not yet claimed by a worker.
    pub task_queue: VecDeque<Task>,
    /// Tasks currently held by a worker (lease in force).
    pub in_flight: HashMap<TaskId, InFlightTask>,
    pub workers: HashMap<u32, WorkerInfo>,
    pub lease_ttl: Duration,
}

impl CoordinatorState {
    pub fn new(lease_ttl: Duration) -> Self {
        CoordinatorState {
            batch_jobs: HashMap::new(),
            cube_jobs: HashMap::new(),
            task_queue: VecDeque::new(),
            in_flight: HashMap::new(),
            workers: HashMap::new(),
            lease_ttl,
        }
    }

    // ── Submit ────────────────────────────────────────────────────────────────

    /// Enqueue a batch of independent SMT scripts.
    /// Returns `(job_id, task_count)` — caller adds `task_count` semaphore permits.
    pub fn submit_batch(&mut self, scripts: Vec<String>, max_conflicts: u64) -> (JobId, usize) {
        let job_id = Uuid::new_v4();
        let count = scripts.len();
        for (i, script) in scripts.into_iter().enumerate() {
            self.task_queue.push_back(Task {
                id: Uuid::new_v4(),
                kind: TaskKind::Batch {
                    job_id,
                    script_index: i,
                    script,
                    max_conflicts,
                },
            });
        }
        self.batch_jobs.insert(job_id, BatchJob::new(job_id, count));
        (job_id, count)
    }

    /// Enqueue a cube-and-conquer job (one open root node initially).
    /// Returns `(job_id, 1)` — caller adds 1 semaphore permit.
    pub fn submit_cube(&mut self, script: String, max_conflicts: u64) -> (JobId, usize) {
        let job_id = Uuid::new_v4();
        let base_script = strip_check_sat(&script).to_owned();
        let job = CubeJob::new(job_id, base_script, max_conflicts);

        let task_script = job.script_for(0).unwrap();
        self.task_queue.push_back(Task {
            id: Uuid::new_v4(),
            kind: TaskKind::Cube {
                job_id,
                node_id: 0,
                script: task_script,
                max_conflicts,
            },
        });
        self.cube_jobs.insert(job_id, job);
        (job_id, 1)
    }

    // ── Dispatch ──────────────────────────────────────────────────────────────

    /// Pop the next queued task and mark it in-flight.
    /// Caller must have already consumed a semaphore permit.
    pub fn pop_task(&mut self, worker_id: u32, now: Instant) -> Option<Task> {
        let task = self.task_queue.pop_front()?;

        if let TaskKind::Cube {
            job_id, node_id, ..
        } = &task.kind
        {
            if let Some(job) = self.cube_jobs.get_mut(job_id) {
                if let Some(node) = job.get_node_mut(*node_id) {
                    node.status = CubeNodeStatus::Assigned;
                    node.task_id = Some(task.id);
                }
            }
        }

        self.in_flight.insert(
            task.id,
            InFlightTask {
                task: task.clone(),
                worker_id,
                deadline: now + self.lease_ttl,
            },
        );
        Some(task)
    }

    // ── Report result ─────────────────────────────────────────────────────────

    /// Record a worker result. Returns `(job_complete, new_task_count)`.
    /// Caller adds `new_task_count` semaphore permits (cube splits push new tasks).
    pub fn report_result(
        &mut self,
        task_id: TaskId,
        worker_id: u32,
        code: u32,
        model: String,
        split: Option<Vec<String>>,
        now: Instant,
    ) -> Result<(bool, usize), String> {
        let inf = self
            .in_flight
            .remove(&task_id)
            .ok_or_else(|| format!("unknown task {task_id}"))?;
        if inf.worker_id != worker_id {
            self.in_flight.insert(task_id, inf);
            return Err(format!("task {task_id} not owned by worker {worker_id}"));
        }

        match inf.task.kind.clone() {
            TaskKind::Batch {
                job_id,
                script_index,
                ..
            } => {
                let complete = self
                    .batch_jobs
                    .get_mut(&job_id)
                    .map(|j| j.record(script_index, TaskResult { code, model }))
                    .unwrap_or(false);
                Ok((complete, 0))
            }
            TaskKind::Cube {
                job_id,
                node_id,
                max_conflicts,
                ..
            } => {
                let new_tasks =
                    self.process_cube_result(job_id, node_id, max_conflicts, code, split);
                let done = self
                    .cube_jobs
                    .get(&job_id)
                    .map(|j| j.status == JobStatus::Complete)
                    .unwrap_or(false);
                let _ = now;
                Ok((done, new_tasks))
            }
        }
    }

    fn process_cube_result(
        &mut self,
        job_id: JobId,
        node_id: u64,
        max_conflicts: u64,
        code: u32,
        split: Option<Vec<String>>,
    ) -> usize {
        // Gather immutable data first, then mutate.
        let (parent_assertions, base_script) = match self.cube_jobs.get(&job_id) {
            None => return 0,
            Some(j) => {
                let pa = j
                    .nodes
                    .iter()
                    .find(|n| n.id == node_id)
                    .map(|n| n.extra_assertions.clone())
                    .unwrap_or_default();
                (pa, j.base_script.clone())
            }
        };

        match code {
            0 => {
                // SAT: mark leaf, finish job.
                let job = self.cube_jobs.get_mut(&job_id).unwrap();
                if let Some(n) = job.get_node_mut(node_id) {
                    n.status = CubeNodeStatus::ClosedSat;
                }
                job.status = JobStatus::Complete;
                job.verdict = Some(Verdict::Sat);
                0
            }
            1 => {
                // UNSAT: close leaf, check if all done.
                let job = self.cube_jobs.get_mut(&job_id).unwrap();
                if let Some(n) = job.get_node_mut(node_id) {
                    n.status = CubeNodeStatus::ClosedUnsat;
                }
                if job.is_unsat() {
                    job.status = JobStatus::Complete;
                    job.verdict = Some(Verdict::Unsat);
                }
                0
            }
            _ if split.is_some() => {
                // Worker requests a cube split.
                let branches = split.unwrap();
                let branch_count = branches.len();

                // Prepare new child nodes and tasks (before mutating the job).
                let mut new_nodes: Vec<CubeNode> = Vec::with_capacity(branch_count);
                let mut new_tasks: Vec<Task> = Vec::with_capacity(branch_count);

                let start_id = {
                    let job = self.cube_jobs.get(&job_id).unwrap();
                    job.next_node_id
                };

                for (i, branch_assertion) in branches.into_iter().enumerate() {
                    let child_id = start_id + i as u64;
                    let mut assertions = parent_assertions.clone();
                    assertions.push(branch_assertion);

                    // Build script for this child directly from base + assertions.
                    let mut script = base_script.clone();
                    script.push('\n');
                    for a in &assertions {
                        script.push_str(a);
                        script.push('\n');
                    }
                    script.push_str("(check-sat)\n");

                    new_nodes.push(CubeNode {
                        id: child_id,
                        parent: Some(node_id),
                        extra_assertions: assertions,
                        status: CubeNodeStatus::Open,
                        task_id: None,
                    });
                    new_tasks.push(Task {
                        id: Uuid::new_v4(),
                        kind: TaskKind::Cube {
                            job_id,
                            node_id: child_id,
                            script,
                            max_conflicts,
                        },
                    });
                }

                // Now mutate: mark parent interior, add children.
                {
                    let job = self.cube_jobs.get_mut(&job_id).unwrap();
                    job.next_node_id += branch_count as u64;
                    for node in new_nodes {
                        job.nodes.push(node);
                    }
                    // Parent node becomes interior (status stays Assigned, which is fine;
                    // it won't be re-dispatched since it now has children).
                }

                for task in new_tasks {
                    self.task_queue.push_back(task);
                }
                branch_count
            }
            _ => {
                // UNKNOWN: re-queue the same node for retry.
                let job = self.cube_jobs.get_mut(&job_id).unwrap();
                if let Some(n) = job.get_node_mut(node_id) {
                    n.status = CubeNodeStatus::Open;
                    n.task_id = None;
                }
                let script = job.script_for(node_id).unwrap_or_default();
                self.task_queue.push_back(Task {
                    id: Uuid::new_v4(),
                    kind: TaskKind::Cube {
                        job_id,
                        node_id,
                        script,
                        max_conflicts,
                    },
                });
                1
            }
        }
    }

    // ── Lease management ──────────────────────────────────────────────────────

    pub fn renew_lease(
        &mut self,
        task_id: TaskId,
        worker_id: u32,
        now: Instant,
    ) -> Result<(), String> {
        let entry = self
            .in_flight
            .get_mut(&task_id)
            .ok_or_else(|| format!("unknown task {task_id}"))?;
        if entry.worker_id != worker_id {
            return Err(format!("task {task_id} not owned by worker {worker_id}"));
        }
        entry.deadline = now + self.lease_ttl;
        Ok(())
    }

    /// Reap expired leases, re-queuing their tasks.
    /// Returns count of re-queued tasks — caller adds that many semaphore permits.
    pub fn reap_expired(&mut self, now: Instant) -> usize {
        let expired: Vec<TaskId> = self
            .in_flight
            .iter()
            .filter(|(_, t)| t.deadline <= now)
            .map(|(id, _)| *id)
            .collect();
        let mut requeued = 0;
        for task_id in expired {
            if let Some(inf) = self.in_flight.remove(&task_id) {
                if let TaskKind::Cube {
                    job_id, node_id, ..
                } = &inf.task.kind
                {
                    if let Some(job) = self.cube_jobs.get_mut(job_id) {
                        if let Some(node) = job.get_node_mut(*node_id) {
                            node.status = CubeNodeStatus::Open;
                            node.task_id = None;
                        }
                    }
                }
                self.task_queue.push_back(inf.task);
                requeued += 1;
            }
        }
        requeued
    }

    /// Reap workers whose heartbeat has timed out, re-queuing their tasks.
    /// Returns count of re-queued tasks — caller adds that many semaphore permits.
    pub fn reap_dead_workers(&mut self, timeout: Duration, now: Instant) -> usize {
        let dead: Vec<u32> = self
            .workers
            .values()
            .filter(|w| now.duration_since(w.last_seen) > timeout)
            .map(|w| w.id)
            .collect();
        let mut requeued = 0;
        for wid in dead {
            self.workers.remove(&wid);
            let tasks: Vec<TaskId> = self
                .in_flight
                .iter()
                .filter(|(_, t)| t.worker_id == wid)
                .map(|(id, _)| *id)
                .collect();
            for tid in tasks {
                if let Some(inf) = self.in_flight.remove(&tid) {
                    self.task_queue.push_back(inf.task);
                    requeued += 1;
                }
            }
        }
        requeued
    }

    pub fn touch_worker(&mut self, worker_id: u32, now: Instant) {
        self.workers.insert(
            worker_id,
            WorkerInfo {
                id: worker_id,
                last_seen: now,
            },
        );
    }

    pub fn stats(&self) -> StatusStats {
        StatusStats {
            batch_jobs: self.batch_jobs.len(),
            cube_jobs: self.cube_jobs.len(),
            tasks_queued: self.task_queue.len(),
            tasks_in_flight: self.in_flight.len(),
            workers_active: self.workers.len(),
        }
    }
}

fn strip_check_sat(s: &str) -> &str {
    let t = s.trim_end();
    t.strip_suffix("(check-sat)")
        .map(str::trim_end)
        .unwrap_or(t)
}

#[derive(Clone, Debug, serde::Serialize)]
pub struct StatusStats {
    pub batch_jobs: usize,
    pub cube_jobs: usize,
    pub tasks_queued: usize,
    pub tasks_in_flight: usize,
    pub workers_active: usize,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn state() -> CoordinatorState {
        CoordinatorState::new(Duration::from_secs(30))
    }

    fn now() -> Instant {
        Instant::now()
    }

    // ── Batch (Regime B) ──────────────────────────────────────────────────

    #[test]
    fn batch_submit_creates_tasks() {
        let mut s = state();
        let scripts = vec!["(check-sat)".into(), "(check-sat)".into()];
        let (job_id, count) = s.submit_batch(scripts, 0);
        assert_eq!(count, 2);
        assert_eq!(s.task_queue.len(), 2);
        assert!(s.batch_jobs.contains_key(&job_id));
        assert_eq!(s.stats().tasks_queued, 2);
    }

    #[test]
    fn batch_pop_and_complete() {
        let mut s = state();
        let (job_id, _) = s.submit_batch(vec!["(check-sat)".into()], 0);

        let task = s.pop_task(1, now()).unwrap();
        assert_eq!(s.task_queue.len(), 0);
        assert_eq!(s.in_flight.len(), 1);

        let (done, new_tasks) = s
            .report_result(task.id, 1, 1, "".into(), None, now())
            .unwrap();
        assert!(done);
        assert_eq!(new_tasks, 0);
        assert_eq!(s.batch_jobs[&job_id].status, JobStatus::Complete);
        assert!(s.in_flight.is_empty());
    }

    #[test]
    fn batch_all_scripts_must_complete() {
        let mut s = state();
        let scripts = vec!["(check-sat)".into(); 3];
        let (job_id, _) = s.submit_batch(scripts, 0);
        let t1 = s.pop_task(1, now()).unwrap();
        let t2 = s.pop_task(2, now()).unwrap();
        let t3 = s.pop_task(3, now()).unwrap();

        let (d, _) = s
            .report_result(t1.id, 1, 1, "".into(), None, now())
            .unwrap();
        assert!(!d);
        let (d, _) = s
            .report_result(t2.id, 2, 1, "".into(), None, now())
            .unwrap();
        assert!(!d);
        let (d, _) = s
            .report_result(t3.id, 3, 1, "".into(), None, now())
            .unwrap();
        assert!(d);
        assert_eq!(s.batch_jobs[&job_id].pending, 0);
    }

    #[test]
    fn wrong_worker_rejected() {
        let mut s = state();
        s.submit_batch(vec!["(check-sat)".into()], 0);
        let task = s.pop_task(1, now()).unwrap();
        let err = s.report_result(task.id, 99, 1, "".into(), None, now());
        assert!(err.is_err());
        // Task should still be in-flight.
        assert_eq!(s.in_flight.len(), 1);
    }

    // ── Cube (Regime A) ───────────────────────────────────────────────────

    #[test]
    fn cube_submit_one_root_task() {
        let mut s = state();
        let (job_id, count) = s.submit_cube("(check-sat)".into(), 0);
        assert_eq!(count, 1);
        assert_eq!(s.task_queue.len(), 1);
        assert!(s.cube_jobs.contains_key(&job_id));
    }

    #[test]
    fn cube_unsat_single_node() {
        let mut s = state();
        let (job_id, _) = s.submit_cube("(check-sat)".into(), 0);
        let task = s.pop_task(1, now()).unwrap();
        let (done, _) = s
            .report_result(task.id, 1, 1, "".into(), None, now())
            .unwrap();
        assert!(done);
        assert_eq!(s.cube_jobs[&job_id].verdict, Some(Verdict::Unsat));
    }

    #[test]
    fn cube_sat_finishes_immediately() {
        let mut s = state();
        let (job_id, _) = s.submit_cube("(check-sat)".into(), 0);
        let task = s.pop_task(1, now()).unwrap();
        let (done, _) = s
            .report_result(task.id, 1, 0, "x=1".into(), None, now())
            .unwrap();
        assert!(done);
        assert_eq!(s.cube_jobs[&job_id].verdict, Some(Verdict::Sat));
    }

    #[test]
    fn cube_split_creates_children() {
        let mut s = state();
        let (job_id, _) = s.submit_cube("(declare-const x Bool)\n(check-sat)".into(), 100);
        let task = s.pop_task(1, now()).unwrap();

        // Worker splits on x: branch "(assert x)" and "(assert (not x))".
        let split = Some(vec!["(assert x)".into(), "(assert (not x))".into()]);
        let (done, new_count) = s
            .report_result(task.id, 1, 2, "".into(), split, now())
            .unwrap();
        assert!(!done);
        assert_eq!(new_count, 2);
        assert_eq!(s.task_queue.len(), 2);
        assert_eq!(s.cube_jobs[&job_id].nodes.len(), 3); // root + 2 children
    }

    #[test]
    fn cube_split_then_both_unsat() {
        let mut s = state();
        let (job_id, _) = s.submit_cube("(check-sat)".into(), 100);
        let root_task = s.pop_task(1, now()).unwrap();

        // Split root into two branches.
        let split = Some(vec!["(assert true)".into(), "(assert false)".into()]);
        s.report_result(root_task.id, 1, 2, "".into(), split, now())
            .unwrap();

        // Close first child as UNSAT.
        let c1 = s.pop_task(2, now()).unwrap();
        let (d, _) = s
            .report_result(c1.id, 2, 1, "".into(), None, now())
            .unwrap();
        assert!(!d, "second child still open");

        // Close second child as UNSAT → job complete.
        let c2 = s.pop_task(3, now()).unwrap();
        let (d, _) = s
            .report_result(c2.id, 3, 1, "".into(), None, now())
            .unwrap();
        assert!(d, "both children UNSAT → complete");
        assert_eq!(s.cube_jobs[&job_id].verdict, Some(Verdict::Unsat));
    }

    // ── Lease management ──────────────────────────────────────────────────

    #[test]
    fn expired_lease_requeues_task() {
        let mut s = state();
        s.submit_batch(vec!["(check-sat)".into()], 0);
        let _ = s.pop_task(1, now());
        assert_eq!(s.in_flight.len(), 1);
        assert_eq!(s.task_queue.len(), 0);

        // Simulate expiry by passing a "now" far in the future.
        let far_future = Instant::now() + Duration::from_secs(9999);
        let requeued = s.reap_expired(far_future);
        assert_eq!(requeued, 1);
        assert_eq!(s.in_flight.len(), 0);
        assert_eq!(s.task_queue.len(), 1);
    }

    #[test]
    fn dead_worker_requeues_tasks() {
        let mut s = state();
        s.submit_batch(vec!["(check-sat)".into(), "(check-sat)".into()], 0);
        s.pop_task(7, now());
        s.pop_task(7, now());
        s.touch_worker(7, now());

        let far_future = Instant::now() + Duration::from_secs(9999);
        let requeued = s.reap_dead_workers(Duration::from_secs(60), far_future);
        assert_eq!(requeued, 2);
        assert_eq!(s.task_queue.len(), 2);
        assert_eq!(s.in_flight.len(), 0);
    }

    #[test]
    fn lease_renewal_extends_deadline() {
        let mut s = state();
        s.submit_batch(vec!["(check-sat)".into()], 0);
        let task = s.pop_task(1, now()).unwrap();

        // Renew succeeds.
        s.renew_lease(task.id, 1, now()).unwrap();

        // Wrong worker is rejected.
        assert!(s.renew_lease(task.id, 99, now()).is_err());
    }

    // ── Strip (check-sat) ─────────────────────────────────────────────────

    #[test]
    fn strip_check_sat_removes_suffix() {
        assert_eq!(strip_check_sat("(check-sat)"), "");
        assert_eq!(
            strip_check_sat("(assert true)\n(check-sat)"),
            "(assert true)"
        );
        assert_eq!(strip_check_sat("(assert true)"), "(assert true)");
    }
}
