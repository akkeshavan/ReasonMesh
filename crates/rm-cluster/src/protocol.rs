use serde::{Deserialize, Serialize};

/// Messages sent from the coordinator to a worker.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum CoordMsg {
    /// Sent once immediately after connection: the full CNF problem.
    Problem {
        num_vars: u32,
        /// Each inner Vec is one clause as signed DIMACS literals.
        clauses: Vec<Vec<i32>>,
    },
    /// Assign a cube to this worker.  `assumptions` are signed DIMACS literals
    /// that are forced true for this sub-problem.
    AssignCube {
        cube_id: u32,
        assumptions: Vec<i32>,
    },
    /// SAT found elsewhere — stop current work immediately.
    Cancel,
}

/// Messages sent from a worker to the coordinator.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum WorkerMsg {
    /// Worker solved its cube and found it satisfiable.
    CubeSat { cube_id: u32 },
    /// Worker solved its cube and found it unsatisfiable.
    CubeUnsat { cube_id: u32 },
}
