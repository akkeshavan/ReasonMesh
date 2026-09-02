//! Run metrics.
//!
//! `RunMetrics` folds an event stream into the machine-readable counters of
//! spec §16.2. A run that ends with `UNKNOWN` due to a budget should always
//! also emit a metrics summary so the harness has reproducible numbers.

use crate::event::{Event, EventKind};
use crate::meta::{Nanos, Outcome};
use rm_akx::knowledge::KnowledgeKindTag;
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

/// Aggregated counters for a run.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct RunMetrics {
    pub outcome: Option<Outcome>,

    // Search
    pub decisions: u64,
    pub propagations: u64,
    pub conflicts: u64,
    pub restarts: u64,

    // Knowledge, by kind
    pub generated: u64,
    pub imported: u64,
    pub used: u64,
    pub discarded: u64,
    pub generated_by_kind: BTreeMap<KnowledgeKindTag, u64>,
    pub imported_by_kind: BTreeMap<KnowledgeKindTag, u64>,

    // Network
    pub bytes_sent: u64,
    pub bytes_received: u64,
    pub messages_dropped: u64,

    // Work units
    pub work_units_completed: u64,

    // Timing
    /// Wall time from first event to `RunFinished` (ns). `None` until the run
    /// finishes.
    pub wall_nanos: Option<Nanos>,
}

impl RunMetrics {
    /// Record one event into the counters.
    pub fn record(&mut self, e: &Event) {
        match &e.kind {
            EventKind::RunFinished { outcome } => {
                self.outcome = Some(*outcome);
            }
            EventKind::Decision { .. } => self.decisions += 1,
            EventKind::Propagation { count } => self.propagations += *count,
            EventKind::Conflict { .. } => self.conflicts += 1,
            EventKind::Restart { .. } => self.restarts += 1,
            EventKind::KnowledgeGenerated { kind, .. } => {
                self.generated += 1;
                *self.generated_by_kind.entry(*kind).or_insert(0) += 1;
            }
            EventKind::KnowledgeImported { applied, kind, .. } => {
                self.imported += 1;
                if *applied == 1 {
                    self.used += 1;
                }
                *self.imported_by_kind.entry(*kind).or_insert(0) += 1;
            }
            EventKind::KnowledgeDiscarded { .. } => self.discarded += 1,
            EventKind::BatchPublished { bytes, .. } => self.bytes_sent += *bytes,
            EventKind::BatchReceived { bytes, .. } => self.bytes_received += *bytes,
            EventKind::BatchDropped { count, .. } => self.messages_dropped += *count as u64,
            EventKind::WorkUnitCompleted { .. } => self.work_units_completed += 1,
            EventKind::Phase { .. }
            | EventKind::WorkUnitAssigned { .. }
            | EventKind::WorkUnitSplit { .. } => {}
            EventKind::SearchSummary {
                decisions,
                propagations,
                conflicts,
                restarts,
            } => {
                // Snapshot: authoritative, overwrites per-event counts.
                self.decisions = *decisions;
                self.propagations = *propagations;
                self.conflicts = *conflicts;
                self.restarts = *restarts;
            }
        }
    }

    /// Folds a (already deterministically ordered) event list. Uses the first
    /// event's timestamp as the start of the wall-clock window.
    pub fn summarize(events: &[Event]) -> Self {
        let mut m = RunMetrics::default();
        for e in events {
            m.record(e);
        }
        if let Some(first) = events.first() {
            if let Some(last) = events
                .iter()
                .find(|e| matches!(e.kind, EventKind::RunFinished { .. }))
            {
                m.wall_nanos = Some(last.at_nanos.saturating_sub(first.at_nanos));
            }
        }
        m
    }

    /// Pretty-printed summary for `reasonmesh replay` diagnostics.
    pub fn render(&self) -> String {
        let mut s = String::new();
        s.push_str(&format!("outcome: {}\n", self.outcome_label()));
        s.push_str(&format!(
            "conflicts: {} decisions: {} propagations: {} restarts: {}\n",
            self.conflicts, self.decisions, self.propagations, self.restarts
        ));
        s.push_str(&format!(
            "knowledge: generated {} imported {} used {} discarded {}\n",
            self.generated, self.imported, self.used, self.discarded
        ));
        for (kind, n) in &self.generated_by_kind {
            s.push_str(&format!("  generated {:?}: {}\n", kind, n));
        }
        s.push_str(&format!(
            "network: bytes sent {} received {} dropped messages {}\n",
            self.bytes_sent, self.bytes_received, self.messages_dropped
        ));
        s.push_str(&format!(
            "work units completed: {}\n",
            self.work_units_completed
        ));
        if let Some(w) = self.wall_nanos {
            s.push_str(&format!("wall time: {:.3} s\n", w as f64 / 1e9));
        }
        s
    }

    fn outcome_label(&self) -> &'static str {
        match self.outcome {
            Some(Outcome::Sat) => "SAT",
            Some(Outcome::Unsat) => "UNSAT",
            Some(Outcome::Unknown) => "UNKNOWN",
            None => "INCOMPLETE",
        }
    }
}
