//! Job and task types for the distributed coordinator.
//!
//! Two regimes:
//!   - **Regime B (proof farm):** array of independent SMT scripts; each is one `Task`.
//!   - **Regime A (cube-and-conquer):** one hard problem split into a `CubeJob` tree;
//!     each leaf cube is one `Task`. Workers may split their leaf further by
//!     reporting a `split` with a list of new SMT-LIB 2 assertion strings.

use serde::{Deserialize, Serialize};
use std::time::Instant;
use uuid::Uuid;

pub type JobId = Uuid;
pub type TaskId = Uuid;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum JobStatus {
    Pending,
    Running,
    Complete,
}

// ── Task result ───────────────────────────────────────────────────────────────

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TaskResult {
    /// 0 = SAT, 1 = UNSAT, 2 = UNKNOWN
    pub code: u32,
    pub model: String,
}

// ── Regime B: batch (proof farm) ─────────────────────────────────────────────

pub struct BatchJob {
    pub id: JobId,
    pub results: Vec<Option<TaskResult>>,
    pub pending: usize,
    pub status: JobStatus,
}

impl BatchJob {
    pub fn new(id: JobId, count: usize) -> Self {
        BatchJob {
            id,
            results: vec![None; count],
            pending: count,
            status: if count == 0 {
                JobStatus::Complete
            } else {
                JobStatus::Running
            },
        }
    }

    /// Record a result at `index`. Returns true when all results are in.
    pub fn record(&mut self, index: usize, result: TaskResult) -> bool {
        if self.results[index].is_none() {
            self.results[index] = Some(result);
            if self.pending > 0 {
                self.pending -= 1;
            }
        }
        if self.pending == 0 {
            self.status = JobStatus::Complete;
        }
        self.pending == 0
    }
}

// ── Regime A: cube-and-conquer ────────────────────────────────────────────────

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Verdict {
    Sat,
    Unsat,
    Unknown,
}

pub struct CubeJob {
    pub id: JobId,
    /// SMT-LIB 2 without trailing `(check-sat)`.
    pub base_script: String,
    pub max_conflicts: u64,
    pub nodes: Vec<CubeNode>,
    pub next_node_id: u64,
    pub status: JobStatus,
    pub verdict: Option<Verdict>,
}

impl CubeJob {
    pub fn new(id: JobId, base_script: String, max_conflicts: u64) -> Self {
        CubeJob {
            id,
            base_script,
            max_conflicts,
            nodes: vec![CubeNode::root()],
            next_node_id: 1,
            status: JobStatus::Running,
            verdict: None,
        }
    }

    /// Build the full SMT-LIB 2 script for `node_id` (base + cube assertions + check-sat).
    pub fn script_for(&self, node_id: u64) -> Option<String> {
        let node = self.nodes.iter().find(|n| n.id == node_id)?;
        let mut s = self.base_script.clone();
        s.push('\n');
        for a in &node.extra_assertions {
            s.push_str(a);
            s.push('\n');
        }
        s.push_str("(check-sat)\n");
        Some(s)
    }

    pub fn get_node_mut(&mut self, id: u64) -> Option<&mut CubeNode> {
        self.nodes.iter_mut().find(|n| n.id == id)
    }

    /// True iff every leaf is ClosedUnsat.
    pub fn is_unsat(&self) -> bool {
        // Interior = nodes that appear as parent of at least one other node.
        let has_children: std::collections::HashSet<u64> =
            self.nodes.iter().filter_map(|n| n.parent).collect();
        self.nodes
            .iter()
            .all(|n| has_children.contains(&n.id) || n.status == CubeNodeStatus::ClosedUnsat)
    }

    pub fn is_sat(&self) -> bool {
        self.nodes
            .iter()
            .any(|n| n.status == CubeNodeStatus::ClosedSat)
    }

    pub fn open_node_ids(&self) -> Vec<u64> {
        self.nodes
            .iter()
            .filter(|n| n.status == CubeNodeStatus::Open)
            .map(|n| n.id)
            .collect()
    }
}

#[derive(Clone, Debug)]
pub struct CubeNode {
    pub id: u64,
    pub parent: Option<u64>,
    /// Extra SMT-LIB 2 `(assert ...)` lines prepended for this cube branch.
    pub extra_assertions: Vec<String>,
    pub status: CubeNodeStatus,
    pub task_id: Option<TaskId>,
}

impl CubeNode {
    fn root() -> Self {
        CubeNode {
            id: 0,
            parent: None,
            extra_assertions: vec![],
            status: CubeNodeStatus::Open,
            task_id: None,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum CubeNodeStatus {
    Open,
    Assigned,
    ClosedSat,
    ClosedUnsat,
    Cancelled,
}

// ── Task dispatched to a remote worker ───────────────────────────────────────

#[derive(Clone, Debug)]
pub struct Task {
    pub id: TaskId,
    pub kind: TaskKind,
}

#[derive(Clone, Debug)]
pub enum TaskKind {
    Batch {
        job_id: JobId,
        script_index: usize,
        script: String,
        max_conflicts: u64,
    },
    Cube {
        job_id: JobId,
        node_id: u64,
        script: String,
        max_conflicts: u64,
    },
}

impl Task {
    pub fn max_conflicts(&self) -> u64 {
        match &self.kind {
            TaskKind::Batch { max_conflicts, .. } => *max_conflicts,
            TaskKind::Cube { max_conflicts, .. } => *max_conflicts,
        }
    }

    pub fn script(&self) -> &str {
        match &self.kind {
            TaskKind::Batch { script, .. } => script,
            TaskKind::Cube { script, .. } => script,
        }
    }
}

pub struct InFlightTask {
    pub task: Task,
    pub worker_id: u32,
    pub deadline: Instant,
}
