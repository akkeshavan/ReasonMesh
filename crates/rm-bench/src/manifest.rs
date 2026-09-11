//! Benchmark manifest: the versioned, machine-readable description of a run.
//!
//! Per the configuration principle (spec §22.2), a run must be describable by
//! a versioned manifest so the command line never becomes the experiment
//! specification. Every paper experiment has a pinned manifest under
//! `experiments/` (spec §8, §16).

use serde::{Deserialize, Serialize};
use std::path::{Path, PathBuf};
use thiserror::Error;

/// Bumped on any incompatible manifest schema change.
pub const MANIFEST_SCHEMA_VERSION: u32 = 1;

#[derive(Debug, Error)]
pub enum ManifestError {
    #[error("cannot read manifest {path}: {source}")]
    Read {
        path: String,
        #[source]
        source: std::io::Error,
    },
    #[error("cannot parse manifest {path}: {source}")]
    Parse {
        path: String,
        #[source]
        source: toml::de::Error,
    },
    #[error("unsupported schema version {found} (this build supports {expected})")]
    SchemaVersion { found: u32, expected: u32 },
}

/// Expected verdict for a problem, when the manifest pins one.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Expected {
    Sat,
    Unsat,
}

impl std::fmt::Display for Expected {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expected::Sat => write!(f, "SAT"),
            Expected::Unsat => write!(f, "UNSAT"),
        }
    }
}

/// A single problem in the benchmark set.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Problem {
    /// Short unique name used in results.
    pub name: String,
    /// Path to the problem file (DIMACS for M0; SMT-LIB later).
    pub file: PathBuf,
    /// Pinned expected verdict, if known.
    #[serde(default)]
    pub expect: Option<Expected>,
}

/// Solving strategy: portfolio of parallel CDCL workers, or cube-and-conquer.
#[derive(Clone, Debug, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum SolverStrategy {
    #[default]
    Portfolio,
    CubeConquer,
}

/// Cube-and-conquer parameters. Only used when `strategy = "cubeconquer"`.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(default)]
pub struct CubeAndConquerConfig {
    /// Lookahead depth for the initial cube set: 2 → at most 4 cubes.
    pub initial_depth: u32,
    /// Per-cube conflict budget before resplitting.
    pub initial_budget: u64,
    /// Maximum conflict budget (doubles on each resplit, capped here).
    pub max_budget: u64,
}

impl Default for CubeAndConquerConfig {
    fn default() -> Self {
        CubeAndConquerConfig {
            initial_depth: 2,
            initial_budget: 5_000,
            max_budget: 2_000_000,
        }
    }
}

/// Solver configuration shared across the run.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(default)]
pub struct SolverConfig {
    pub workers: u32,
    pub seed: u64,
    pub deterministic: bool,
    /// Exchange learned clauses between workers (baseline 3, spec §16.3).
    /// `false` runs an isolated multi-worker portfolio (baseline 2), which is
    /// the control for the G1 gate (§18): "does asynchronous clause exchange
    /// improve multi-core SAT over isolated portfolios?"
    pub clause_sharing: bool,
    /// Only share clauses whose estimated utility is at least this. A higher
    /// threshold filters out junk (high-LBD) learned clauses — the §18
    /// "knowledge utility" lever. `0.0` shares everything.
    pub export_min_utility: f32,
    /// Only apply imported clauses whose estimated utility is at least this.
    /// `0.0` applies everything that reaches the gate.
    pub import_min_utility: f32,
    /// Per-problem conflict budget. `None` means unlimited.
    pub max_conflicts_per_problem: Option<u64>,
    /// Per-problem wall-clock budget in seconds.
    pub timeout_secs: u64,
    /// Enable GPU-accelerated WalkSAT phase guidance (Metal on Apple Silicon).
    /// When true, each solver gets a MetalAccelerator; falls back silently to
    /// CPU walk if Metal is unavailable.
    #[serde(default)]
    pub gpu: bool,
    /// Solving strategy: "portfolio" (default) or "cubeconquer".
    #[serde(default)]
    pub strategy: SolverStrategy,
}

impl Default for SolverConfig {
    fn default() -> Self {
        SolverConfig {
            workers: 1,
            seed: 1,
            deterministic: true,
            clause_sharing: true,
            // Sanctioned by the G1 gate (§18): unfiltered exchange (0.0/0.0)
            // measures no better than an isolated portfolio, while exchanging
            // only LBD≤3 clauses (utility 0.25) and importing only LBD≤6
            // (0.143) consistently improves it. Utility = 1/(1+lbd).
            export_min_utility: 0.25,
            import_min_utility: 0.143,
            max_conflicts_per_problem: Some(100_000),
            timeout_secs: 300,
            gpu: false,
            strategy: SolverStrategy::Portfolio,
        }
    }
}

/// Output configuration: where results and traces go.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(default)]
pub struct OutputConfig {
    /// Directory for results and traces. Created if missing.
    pub dir: PathBuf,
    /// Write a `.rmtrace` per problem alongside the result.
    pub trace: bool,
}

impl Default for OutputConfig {
    fn default() -> Self {
        OutputConfig {
            dir: PathBuf::from("results"),
            trace: false,
        }
    }
}

/// An external solver run alongside ReasonMesh for comparison.
///
/// Single-worker (default): `{binary} {cnf_file} {args...}` — one process,
/// wait for verdict.
///
/// Portfolio (`workers > 1`): `workers` processes launched simultaneously,
/// each with an independent seed (`{seed_flag} {worker_index}` appended when
/// `seed_flag` is set). The first to produce a SAT/UNSAT verdict wins; all
/// others are killed. Wall time is the winner's elapsed time — this is the
/// fair apples-to-apples comparison against a ReasonMesh N-worker portfolio.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BaselineConfig {
    /// Short label used in results (e.g. `"cadical-4t"`).
    pub name: String,
    /// Executable name or absolute path (resolved via PATH).
    pub binary: String,
    /// Arguments appended after the CNF file path (all workers share these).
    #[serde(default)]
    pub args: Vec<String>,
    /// Number of parallel instances to race. Default 1 = single process.
    #[serde(default = "default_workers")]
    pub workers: u32,
    /// CLI flag for the random seed, e.g. `"--seed"` for CaDiCaL.
    /// Worker `i` gets `{seed_flag} {i}` appended. Empty = no seed arg.
    #[serde(default)]
    pub seed_flag: String,
}

fn default_workers() -> u32 {
    1
}

/// A complete benchmark run description.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Manifest {
    pub schema_version: u32,
    pub name: String,
    #[serde(default)]
    pub description: String,
    #[serde(default)]
    pub solver: SolverConfig,
    #[serde(default)]
    pub output: OutputConfig,
    /// External solvers to run in parallel with ReasonMesh for comparison.
    /// Each baseline runs on every problem with the same timeout.
    #[serde(default)]
    pub baselines: Vec<BaselineConfig>,
    #[serde(default)]
    pub problems: Vec<Problem>,
    /// Cube-and-conquer parameters.  Required when `solver.strategy = "cubeconquer"`.
    #[serde(default)]
    pub cube_and_conquer: Option<CubeAndConquerConfig>,
}

impl Manifest {
    /// Parse a manifest from TOML text.
    pub fn parse(input: &str) -> Result<Self, ManifestError> {
        let m: Manifest = toml::from_str(input).map_err(|source| ManifestError::Parse {
            path: "<input>".into(),
            source,
        })?;
        if m.schema_version != MANIFEST_SCHEMA_VERSION {
            return Err(ManifestError::SchemaVersion {
                found: m.schema_version,
                expected: MANIFEST_SCHEMA_VERSION,
            });
        }
        Ok(m)
    }

    /// Load a manifest from a file.
    pub fn load(path: &Path) -> Result<Self, ManifestError> {
        let text = std::fs::read_to_string(path).map_err(|source| ManifestError::Read {
            path: path.display().to_string(),
            source,
        })?;
        let mut m: Manifest = toml::from_str(&text).map_err(|source| ManifestError::Parse {
            path: path.display().to_string(),
            source,
        })?;
        if m.schema_version != MANIFEST_SCHEMA_VERSION {
            return Err(ManifestError::SchemaVersion {
                found: m.schema_version,
                expected: MANIFEST_SCHEMA_VERSION,
            });
        }
        // Resolve problem paths relative to the manifest directory so manifests
        // are relocatable.
        let base = path
            .parent()
            .map(Path::to_path_buf)
            .unwrap_or_else(|| PathBuf::from("."));
        for p in &mut m.problems {
            if p.file.is_relative() {
                p.file = base.join(&p.file);
            }
        }
        Ok(m)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const VALID: &str = r#"
schema_version = 1
name = "smoke"
description = "M0 smoke test"

[solver]
workers = 1
seed = 42
deterministic = true
max_conflicts_per_problem = 1000
timeout_secs = 30

[output]
dir = "results/smoke"
trace = true

[[problems]]
name = "unsat-2v"
file = "benchmarks/unsat.cnf"
expect = "unsat"

[[problems]]
name = "sat-3v"
file = "benchmarks/sat.cnf"
"#;

    #[test]
    fn parses_valid_manifest() {
        let m = Manifest::parse(VALID).unwrap();
        assert_eq!(m.name, "smoke");
        assert_eq!(m.solver.workers, 1);
        assert_eq!(m.solver.seed, 42);
        assert_eq!(m.problems.len(), 2);
        assert_eq!(m.problems[0].expect, Some(Expected::Unsat));
        assert_eq!(m.problems[1].expect, None);
        assert!(m.output.trace);
    }

    #[test]
    fn rejects_old_schema() {
        let bad = VALID.replace("schema_version = 1", "schema_version = 0");
        let err = Manifest::parse(&bad).unwrap_err();
        assert!(matches!(
            err,
            ManifestError::SchemaVersion {
                found: 0,
                expected: 1
            }
        ));
    }

    #[test]
    fn defaults_fill_solver_and_output() {
        let minimal = r#"
schema_version = 1
name = "min"
[[problems]]
name = "a"
file = "a.cnf"
"#;
        let m = Manifest::parse(minimal).unwrap();
        assert_eq!(m.solver.timeout_secs, 300);
        assert_eq!(m.solver.max_conflicts_per_problem, Some(100_000));
        assert_eq!(m.output.dir, PathBuf::from("results"));
        assert!(m.solver.clause_sharing);
        assert_eq!(m.solver.export_min_utility, 0.25);
        assert_eq!(m.solver.import_min_utility, 0.143);
        assert!(!m.output.trace);
    }

    #[test]
    fn parses_clause_sharing_flag() {
        let isolated = VALID.replace("[solver]", "[solver]\nclause_sharing = false\n");
        let m = Manifest::parse(&isolated).unwrap();
        assert!(!m.solver.clause_sharing);
    }

    #[test]
    fn parses_knowledge_utility_thresholds() {
        let m = Manifest::parse(&VALID.replace(
            "[solver]",
            "[solver]\nexport_min_utility = 0.2\nimport_min_utility = 0.16\n",
        ))
        .unwrap();
        assert_eq!(m.solver.export_min_utility, 0.2);
        assert_eq!(m.solver.import_min_utility, 0.16);
        // Absent fields default to the G1-sanctioned selective thresholds.
        let m = Manifest::parse(VALID).unwrap();
        assert_eq!(m.solver.export_min_utility, 0.25);
        assert_eq!(m.solver.import_min_utility, 0.143);
    }
}
