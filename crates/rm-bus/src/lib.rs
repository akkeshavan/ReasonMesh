pub mod hierarchy;
pub mod inproc;
pub mod net;
pub mod policy;
pub mod queue;

pub use policy::{BusConfig, EvictionPolicy};

use rm_akx::{BusMetrics, KnowledgeBatch, Scope};
use thiserror::Error;

// ---------------------------------------------------------------------------
// Bus error
// ---------------------------------------------------------------------------

#[derive(Debug, Error)]
pub enum BusError {
    #[error("buffer full; producer must back off")]
    BufferFull,
    #[error("transport disconnected")]
    Disconnected,
    #[error("schema version mismatch; message dropped")]
    SchemaRejected,
    #[error("internal error: {0}")]
    Internal(String),
}

// ---------------------------------------------------------------------------
// Publish handle
// ---------------------------------------------------------------------------

/// Returned by a successful `publish`; allows the caller to track delivery.
/// For in-process buses this is a no-op wrapper; for network buses it may
/// carry a future or a sequence number.
pub struct PublishHandle {
    /// Number of objects actually enqueued (after deduplication).
    pub enqueued: usize,
}

// ---------------------------------------------------------------------------
// Poll budget
// ---------------------------------------------------------------------------

/// How many objects to drain from the bus in one poll call.
#[derive(Clone, Copy, Debug)]
pub struct PollBudget {
    pub max_items: usize,
}

impl Default for PollBudget {
    fn default() -> Self {
        PollBudget { max_items: 256 }
    }
}

// ---------------------------------------------------------------------------
// KnowledgeBus trait
// ---------------------------------------------------------------------------

/// Transport-independent AKX knowledge bus.
///
/// # Back-pressure
/// `publish` returns `Err(BusError::BufferFull)` when the scope-level buffer
/// is at capacity and the incoming item has lower utility than the lowest item
/// in the buffer. The caller should back off for one step before retrying.
///
/// # Deduplication
/// Objects are deduplicated by `rm_akx::knowledge::canonical_key` before
/// insertion. An unconditional version of a conclusion evicts all conditional
/// versions of the same conclusion already in the buffer.
pub trait KnowledgeBus: Send + Sync {
    /// Publish a batch of knowledge objects at the given scope.
    fn publish(&self, scope: Scope, batch: KnowledgeBatch) -> Result<PublishHandle, BusError>;

    /// Non-blocking poll; returns an empty batch if nothing is available.
    fn poll(&self, budget: PollBudget) -> Result<KnowledgeBatch, BusError>;

    /// Current operational metrics snapshot.
    fn metrics(&self) -> BusMetrics;
}
