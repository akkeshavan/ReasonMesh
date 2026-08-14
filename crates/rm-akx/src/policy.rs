use crate::knowledge::{KnowledgeId, KnowledgeKindTag, Scope};
use serde::{Deserialize, Serialize};
use smallvec::SmallVec;

/// Controls what a worker exports in a given call to `Reasoner::export`.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ExportPolicy {
    /// Only export knowledge objects with ID > watermark.
    pub watermark: KnowledgeId,
    /// Maximum number of objects to return per call.
    pub max_items: usize,
    /// Only export objects with utility >= this threshold.
    pub min_utility: f32,
    /// Maximum scope the caller is willing to accept in this batch.
    pub max_scope: Scope,
    /// If non-empty, restrict to these knowledge kinds.
    pub kind_filter: SmallVec<[KnowledgeKindTag; 4]>,
}

impl Default for ExportPolicy {
    fn default() -> Self {
        ExportPolicy {
            watermark: KnowledgeId(0),
            max_items: 256,
            min_utility: 0.0,
            max_scope: Scope::Global,
            kind_filter: SmallVec::new(),
        }
    }
}

/// Controls import behaviour for a worker.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ImportPolicy {
    /// Maximum number of objects to integrate per import call.
    pub max_items: usize,
    /// Reject objects with utility below this threshold.
    pub min_utility: f32,
    /// Maximum number of conditional objects buffered awaiting context match.
    pub buffer_capacity: usize,
}

impl Default for ImportPolicy {
    fn default() -> Self {
        ImportPolicy {
            max_items: 512,
            min_utility: 0.0,
            buffer_capacity: 1024,
        }
    }
}
