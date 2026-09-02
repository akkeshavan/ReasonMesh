use crate::literal::Literal;
use serde::{Deserialize, Serialize};
use smallvec::SmallVec;
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};

// ---------------------------------------------------------------------------
// Problem identity
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub struct ProblemId(pub u64);

// ---------------------------------------------------------------------------
// Work budget
// ---------------------------------------------------------------------------

/// Describes how much work a worker is allowed to perform in one `step` call.
#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub struct WorkBudget {
    /// Maximum number of CDCL conflicts (or equivalent work units).
    pub max_conflicts: u64,
    /// Maximum wall-clock milliseconds. Workers should check this periodically.
    pub max_ms: u64,
}

impl Default for WorkBudget {
    fn default() -> Self {
        WorkBudget {
            max_conflicts: 5_000,
            max_ms: 500,
        }
    }
}

// ---------------------------------------------------------------------------
// Priority
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Serialize, Deserialize)]
pub struct Priority(pub u32);

impl Priority {
    pub const LOW: Priority = Priority(0);
    pub const NORMAL: Priority = Priority(100);
    pub const HIGH: Priority = Priority(200);
}

// ---------------------------------------------------------------------------
// Cube path (ancestry)
// ---------------------------------------------------------------------------

/// Records the sequence of splits that produced this work unit from the root.
/// Used for duplication detection and partition tree maintenance.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct CubePath {
    /// Each entry is the assumption literal added at that split level.
    pub steps: SmallVec<[Literal; 16]>,
}

impl CubePath {
    pub fn depth(&self) -> usize {
        self.steps.len()
    }

    pub fn extend(&self, lit: Literal) -> Self {
        let mut child = self.clone();
        child.steps.push(lit);
        child
    }
}

// ---------------------------------------------------------------------------
// Work unit
// ---------------------------------------------------------------------------

/// A unit of work dispatched to a reasoner.
///
/// Represents "solve the original problem restricted to `assumptions`."
/// A worker may either close the unit (SAT/UNSAT) or split it into children.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct WorkUnit {
    pub problem: ProblemId,
    /// Assumption literals that restrict the search space for this unit.
    /// `ctx_W` in the import predicate is exactly these literals.
    /// Stored as Vec for serde; callers may wrap in Arc<[_]> for cheap sharing.
    pub assumptions: Vec<Literal>,
    pub ancestry: CubePath,
    pub priority: Priority,
    pub budget: WorkBudget,
    /// Random seed for this worker's heuristics. Changing this seed is the
    /// primary diversification mechanism in a portfolio.
    pub seed: u64,
    /// Set to `true` by the orchestrator when this unit should be abandoned
    /// (SAT found elsewhere, orchestrator shutdown, lease expired).
    /// Workers MUST poll this at least once per conflict and return
    /// `ReasonerEvent::Cancelled` promptly when it fires.
    #[serde(skip)]
    pub shutdown: Arc<AtomicBool>,
}

impl WorkUnit {
    pub fn is_cancelled(&self) -> bool {
        self.shutdown.load(Ordering::Relaxed)
    }

    pub fn assumption_slice(&self) -> &[Literal] {
        &self.assumptions
    }
}

// ---------------------------------------------------------------------------
// Partial model
// ---------------------------------------------------------------------------

/// A (possibly partial) variable assignment, proposed by a worker.
/// Must be independently validated before SAT is declared.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PartialModel {
    /// `assignments[i] = Some(true/false)` if variable `i` is assigned.
    pub assignments: Vec<Option<bool>>,
    /// The work unit this model was found under.
    pub work_unit_ancestry: CubePath,
}

impl PartialModel {
    pub fn get(&self, var: u32) -> Option<bool> {
        self.assignments.get(var as usize).copied().flatten()
    }

    pub fn is_complete(&self) -> bool {
        self.assignments.iter().all(|a| a.is_some())
    }
}
