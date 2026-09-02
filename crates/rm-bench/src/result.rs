//! Benchmark results and summary scoring (PAR-2 / PAR-10, spec §16.2).

use crate::manifest::Expected;
use rm_telemetry::Outcome;
use serde::{Deserialize, Serialize};
use std::time::Duration;

/// §16.2 "Knowledge" exchange metrics for a multi-worker run: what actually
/// flowed through the shared bus and past each worker's import gate. Absent
/// for single-worker runs. Lets the G1 gate tell "no sharing benefit" apart
/// from "sharing happened but the knowledge was useless".
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct KnowledgeMetrics {
    /// Objects workers exported to the bus (before bus dedup/eviction).
    pub exported: u64,
    /// Objects actually enqueued on the bus (after dedup/eviction).
    pub published: u64,
    /// Objects polled from the bus by workers.
    pub received: u64,
    /// Polled objects applied through a worker's import gate.
    pub applied: u64,
    /// Polled objects buffered awaiting context match.
    pub buffered: u64,
    /// Polled objects discarded (no overlap, duplicate, or low utility).
    pub discarded: u64,
    /// Bus-level aggregates over the whole run.
    pub bus_published: u64,
    pub bus_deduplicated: u64,
    pub bus_evicted: u64,
    pub bus_backpressure: u64,
}

/// Outcome of one external baseline solver on one problem.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BaselineResult {
    pub name: String,
    pub outcome: Outcome,
    pub wall: Duration,
    pub timed_out: bool,
}

/// Result of solving a single problem.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ProblemResult {
    pub name: String,
    pub outcome: Outcome,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub expected: Option<Expected>,
    /// Whether the outcome matched the pinned expected verdict (if any).
    pub matches_expected: bool,
    /// Wall time spent solving this problem.
    pub wall: Duration,
    /// True if the wall-clock timeout hit before a verdict.
    pub timed_out: bool,
    pub conflicts: u64,
    pub decisions: u64,
    pub propagations: u64,
    pub restarts: u64,
    /// §16.2 knowledge-exchange diagnostics; set on multi-worker runs only.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub knowledge: Option<KnowledgeMetrics>,
    /// External baseline results for this problem (empty when no baselines configured).
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub baselines: Vec<BaselineResult>,
    /// Trace file written for this problem, if requested.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub trace: Option<String>,
}

/// Aggregated scoring over the whole run.
#[derive(Clone, Copy, Debug, Default, Serialize, Deserialize)]
pub struct RunSummary {
    pub problems: usize,
    pub solved: usize,
    pub unsolved: usize,
    /// Sum over solved problems of wall time, ns.
    pub solved_total_ns: u128,
    /// PAR-2 score in ns (unsolved penalized at 2x the timeout).
    pub par2_ns: u128,
    /// PAR-10 score in ns (unsolved penalized at 10x the timeout).
    pub par10_ns: u128,
    /// Wall-clock timeout used for penalty computation.
    pub timeout_ns: u128,
}

impl RunSummary {
    /// Compute PAR-2 and PAR-10 over the given results with the given timeout.
    pub fn compute(problems: usize, results: &[ProblemResult], timeout: Duration) -> Self {
        let timeout_ns = timeout.as_nanos();
        let solved = results
            .iter()
            .filter(|r| r.outcome != Outcome::Unknown)
            .count();
        let solved_total_ns: u128 = results
            .iter()
            .filter(|r| r.outcome != Outcome::Unknown)
            .map(|r| r.wall.as_nanos())
            .sum();
        let unsolved = problems.saturating_sub(solved);
        let base = solved_total_ns + timeout_ns.saturating_mul(unsolved as u128);
        RunSummary {
            problems,
            solved,
            unsolved,
            solved_total_ns,
            par2_ns: base + timeout_ns.saturating_mul(unsolved as u128),
            par10_ns: base + timeout_ns.saturating_mul(unsolved as u128 * 9),
            timeout_ns,
        }
    }
}

/// The complete, machine-readable result of a benchmark run.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ManifestRun {
    pub schema_version: u32,
    pub manifest: String,
    pub solver_version: String,
    pub git_revision: String,
    /// Wall-clock duration of the whole run.
    pub run_wall: Duration,
    pub problems: Vec<ProblemResult>,
    pub summary: RunSummary,
}

impl ManifestRun {
    /// Serialize as pretty JSON, the canonical machine-readable format.
    pub fn to_json_pretty(&self) -> String {
        serde_json::to_string_pretty(self).expect("ManifestRun serializes infallibly")
    }
}
