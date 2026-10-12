pub mod coordinator;
pub mod framing;
pub mod protocol;
pub mod worker_node;

pub use coordinator::{BoundCoordinator, ClusterCoordinator};
pub use worker_node::ClusterWorkerNode;

/// Result of a cluster solve.
#[derive(Debug, Clone)]
pub enum ClusterResult {
    Sat,
    Unsat,
    /// All workers disconnected before a result was established.
    Failed(String),
}
