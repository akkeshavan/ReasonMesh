//! rm-bench — benchmark manifests and runner (spec §16, §22.2).
//!
//! A benchmark is fully described by a versioned TOML manifest; the runner
//! executes it against the production solver and emits machine-readable
//! results (JSON) with PAR-2/PAR-10 scoring and independent model validation.

pub mod manifest;
pub mod result;
pub mod run;

pub use manifest::{Expected, Manifest, ManifestError, OutputConfig, Problem, SolverConfig};
pub use result::{ManifestRun, ProblemResult, RunSummary};
pub use run::{run_manifest, RunError};
