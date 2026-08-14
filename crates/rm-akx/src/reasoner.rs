use crate::knowledge::{KnowledgeId, KnowledgeKindTag, KnowledgeObject};
use crate::policy::ExportPolicy;
use crate::work::{PartialModel, WorkBudget, WorkUnit};
use serde::{Deserialize, Serialize};
use smallvec::SmallVec;
use std::sync::Arc;
use thiserror::Error;

// ---------------------------------------------------------------------------
// Identity types
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub struct ReasonerId(pub u32);

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub struct WorkerId(pub u32);

// ---------------------------------------------------------------------------
// Hardware classification
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub enum HardwareClass {
    Cpu,
    Gpu,
    /// Specialized co-processor or FPGA.
    Accelerator,
}

// ---------------------------------------------------------------------------
// Capabilities
// ---------------------------------------------------------------------------

/// What a reasoner can produce and consume, and what guarantees it provides.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Capabilities {
    /// Knowledge kinds this worker can emit.
    pub can_produce: SmallVec<[KnowledgeKindTag; 4]>,
    /// Knowledge kinds this worker can import and use.
    pub can_consume: SmallVec<[KnowledgeKindTag; 4]>,
    /// Worker runs a complete algorithm; its `UnsatLocal` events may close partitions.
    pub is_complete: bool,
    /// Worker emits checkable proof fragments alongside results.
    pub produces_proofs: bool,
    pub hardware: HardwareClass,
}

// ---------------------------------------------------------------------------
// Reasoner event
// ---------------------------------------------------------------------------

/// Returned by `Reasoner::step`; tells the scheduler what happened.
#[derive(Debug)]
pub enum ReasonerEvent {
    /// Worker made progress; call `export` to drain new knowledge.
    Progress,
    /// Worker found a satisfying assignment under its active assumptions.
    /// The model must be independently validated before SAT is declared.
    SatCandidate { model: Arc<PartialModel> },
    /// Worker proved UNSAT under its active assumptions.
    /// Only meaningful when `Capabilities::is_complete == true`.
    UnsatLocal { proof_ref: Option<crate::knowledge::ProofRef> },
    /// Budget exhausted with no conclusion; return and reschedule.
    BudgetExhausted,
    /// Worker needs a fresh WorkUnit to continue.
    NeedWork,
    /// Worker acknowledged cancellation and is stopping cleanly.
    Cancelled,
    /// Unrecoverable error; the scheduler must restart this worker.
    InternalError(ReasonerError),
}

// ---------------------------------------------------------------------------
// Checkpoint
// ---------------------------------------------------------------------------

/// Lightweight snapshot the orchestrator can persist for fault recovery.
///
/// A seed-deterministic worker only needs the work unit and seed.
/// Stateful workers may serialize an opaque internal blob.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Checkpoint {
    pub worker_id: WorkerId,
    pub work_unit: WorkUnit,
    /// Opaque solver-internal state blob. `None` for seed-deterministic workers.
    pub internal_state: Option<Vec<u8>>,
    /// Highest `KnowledgeId` imported before this checkpoint.
    pub knowledge_watermark: crate::knowledge::KnowledgeId,
}

// ---------------------------------------------------------------------------
// Batch types
// ---------------------------------------------------------------------------

/// A batch of knowledge objects ready for import or export.
pub type KnowledgeBatch = Vec<KnowledgeObject>;

// ---------------------------------------------------------------------------
// Stats
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct ImportStats {
    pub received: u32,
    pub applied: u32,
    pub buffered: u32,
    pub discarded_no_overlap: u32,
    pub discarded_duplicate: u32,
}

// ---------------------------------------------------------------------------
// Error
// ---------------------------------------------------------------------------

#[derive(Debug, Error)]
pub enum ReasonerError {
    #[error("out of memory: {0}")]
    OutOfMemory(String),
    #[error("internal theory error: {0}")]
    TheoryError(String),
    #[error("proof generation failed: {0}")]
    ProofError(String),
    #[error("serialization error: {0}")]
    Serialization(String),
    #[error("cancelled")]
    Cancelled,
}

// ---------------------------------------------------------------------------
// The Reasoner trait
// ---------------------------------------------------------------------------

/// Core interface every reasoning worker must implement.
///
/// # Import contract
/// Implementors MUST apply the AKX import predicate (spec §7.3) before using
/// any knowledge object with a non-empty assumption set:
///   `IMPORT_OK(self, K)  ≡  self.ctx() ⊇ K.assumptions`
pub trait Reasoner: Send {
    fn id(&self) -> ReasonerId;
    fn capabilities(&self) -> Capabilities;

    /// Import a batch of knowledge objects.
    ///
    /// The implementation is responsible for running the import predicate
    /// and updating `ImportStats` accordingly.
    fn import(&mut self, batch: KnowledgeBatch) -> Result<ImportStats, ReasonerError>;

    /// Run for at most `budget` units of work.
    fn step(&mut self, budget: crate::work::WorkBudget) -> Result<ReasonerEvent, ReasonerError>;

    /// Snapshot knowledge for export. Takes `&self` to allow concurrent scheduling.
    ///
    /// The scheduler maintains a per-worker `KnowledgeId` watermark externally;
    /// `policy` carries the watermark so this call returns only new items.
    fn export(&self, policy: &ExportPolicy) -> Result<KnowledgeBatch, ReasonerError>;

    /// Return a checkpoint for fault recovery, or `None` for stateless workers.
    fn checkpoint(&self) -> Result<Option<Checkpoint>, ReasonerError>;
}
