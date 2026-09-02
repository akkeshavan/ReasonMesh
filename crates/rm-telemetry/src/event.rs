//! Trace events.
//!
//! Every event carries an envelope with a timeline-local monotonic sequence
//! number, the originating worker, and a wall-clock timestamp used only for
//! timing metrics (never for replay ordering). Event payloads map to the
//! mandatory metric categories of spec §16.2: Search, Knowledge, Network,
//! Work units, and Outcome.

use crate::meta::{Nanos, Outcome};
use rm_akx::knowledge::{KnowledgeId, KnowledgeKindTag};
use serde::{Deserialize, Serialize};

/// One entry in a `.rmtrace` log.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Event {
    /// Monotonic sequence within this event's timeline (worker). The reader
    /// verifies these are strictly increasing per timeline; this is what makes
    /// logical ordering deterministic under replay.
    pub seq: u64,
    /// Owning worker id (`rm_akx::reasoner::WorkerId`).
    pub worker: u32,
    /// Wall clock (ns since epoch) at record time. Timing metrics only.
    pub at_nanos: Nanos,
    pub kind: EventKind,
}

/// Why a knowledge object stopped being relevant.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum DiscardReason {
    /// Import predicate failed: this worker's context does not entail the
    /// object's assumption set (§7.3).
    ContextIncompatible,
    Duplicate,
    Evicted,
    Superseded,
}

/// Why a message was dropped at the bus level.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum DropReason {
    QueueFull,
    BackPressure,
    Deduplicated,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum EventKind {
    // Outcome (spec §16.2 "Outcome")
    RunFinished {
        outcome: Outcome,
    },

    // Search (§16.2 "Search")
    Decision {
        var: u32,
    },
    Conflict {
        /// Decision level of the conflict.
        level: u32,
        learnt_len: usize,
        learnt_lbd: u32,
    },
    Propagation {
        count: u64,
    },
    Restart {
        /// `1` for restarts that preserved the assumption floor, `0` for
        /// full restarts.
        assumed: u32,
    },
    /// A phase boundary in the run (e.g. "root", "cube-split", "import").
    Phase {
        name: String,
    },
    /// Aggregate search counters captured at a point in time (e.g. end of
    /// run). Overwrites per-event counters in `RunMetrics` rather than adding.
    SearchSummary {
        decisions: u64,
        propagations: u64,
        conflicts: u64,
        restarts: u64,
    },

    // Knowledge (§16.2 "Knowledge")
    KnowledgeGenerated {
        id: KnowledgeId,
        kind: KnowledgeKindTag,
        size: usize,
        lbd: u32,
    },
    KnowledgeImported {
        id: KnowledgeId,
        kind: KnowledgeKindTag,
        /// 1 if the import predicate passed and the object was applied, 0 if
        /// it was accepted but buffered.
        applied: u8,
    },
    KnowledgeDiscarded {
        id: KnowledgeId,
        kind: KnowledgeKindTag,
        reason: DiscardReason,
    },

    // Work units (§16.2 "Search"/§16.2 "Reliability")
    WorkUnitAssigned {
        id: KnowledgeId,
        path: String,
    },
    WorkUnitCompleted {
        id: KnowledgeId,
        outcome: Outcome,
    },
    WorkUnitSplit {
        id: KnowledgeId,
        into: u32,
    },

    // Bus / network (§16.2 "Network")
    BatchPublished {
        from: u32,
        to: u32,
        count: u32,
        bytes: u64,
    },
    BatchReceived {
        from: u32,
        to: u32,
        count: u32,
        bytes: u64,
    },
    BatchDropped {
        from: u32,
        to: u32,
        count: u32,
        reason: DropReason,
    },
}
