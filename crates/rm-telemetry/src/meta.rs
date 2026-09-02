//! Run metadata: the header of a `.rmtrace` replay log.
//!
//! The trace header captures everything needed to reproduce a run:
//! seeds, worker configuration, command line, solver version, and hardware.
//! Exact timing need not replay, but logical event ordering within a worker
//! must (spec §15.3).

use serde::{Deserialize, Serialize};

/// Bumped whenever the trace schema changes incompatibly.
pub const TRACE_SCHEMA_VERSION: u32 = 1;

/// A monotonic wall-clock instant in nanoseconds since the UNIX epoch.
pub type Nanos = u128;

/// Machine-readable final verdict of a run.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Outcome {
    Sat,
    Unsat,
    Unknown,
}

/// Static description of the hardware a run executed on.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HardwareMeta {
    pub os: String,
    pub arch: String,
    pub cpu_count: usize,
}

impl HardwareMeta {
    /// Snapshot the current machine. Best-effort; never fails.
    pub fn current() -> Self {
        HardwareMeta {
            os: std::env::consts::OS.to_string(),
            arch: std::env::consts::ARCH.to_string(),
            cpu_count: std::thread::available_parallelism().map_or(1, |n| n.get()),
        }
    }
}

/// Everything the tracer knows about the run before the first event.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RunMeta {
    pub schema_version: u32,
    /// Solver crate version (set from `CARGO_PKG_VERSION`).
    pub solver_version: String,
    /// Source revision, if a `GIT_REVISION` env var is set at build time.
    pub git_revision: String,
    pub command_line: String,
    /// Number of worker threads participating.
    pub num_workers: u32,
    /// Random seed per worker. `seeds[i]` belongs to worker id `i`.
    pub seeds: Vec<u64>,
    /// Deterministic single-worker mode (spec §15.3).
    pub deterministic: bool,
    pub hardware: HardwareMeta,
    /// UNIX timestamp (ns) when the run started.
    pub started_at: Nanos,
}

impl RunMeta {
    /// Build metadata for a deterministic single-worker run.
    pub fn deterministic(solver: &str, command_line: String, seed: u64) -> Self {
        RunMeta {
            schema_version: TRACE_SCHEMA_VERSION,
            solver_version: solver.to_string(),
            git_revision: option_env!("GIT_REVISION").unwrap_or("unknown").to_string(),
            command_line,
            num_workers: 1,
            seeds: vec![seed],
            deterministic: true,
            hardware: HardwareMeta::current(),
            started_at: now_nanos(),
        }
    }
}

/// Current UNIX time in nanoseconds.
pub fn now_nanos() -> Nanos {
    use std::time::{SystemTime, UNIX_EPOCH};
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |d| d.as_nanos())
}
