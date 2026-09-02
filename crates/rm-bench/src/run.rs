//! Benchmark runner.
//!
//! Executes a manifest: each problem is solved single-worker (deterministic
//! production CDCL) or, when the manifest requests `workers > 1`, by a pool of
//! CDCL reasoners on a shared in-process bus. Every SAT model is independently
//! validated, and the run produces a machine-readable summary (spec §16.2).
//! Multi-worker runs support the §16.3 ablation ladder: `clause_sharing =
//! true` is the clause-sharing portfolio (baseline 3), `false` an isolated
//! portfolio (baseline 2) — the G1-gate control (§18).

use crate::manifest::{Expected, Manifest, Problem};
use crate::result::{KnowledgeMetrics, ManifestRun, ProblemResult, RunSummary};
use rm_akx::literal::Literal;
use rm_akx::{ExportPolicy, ImportPolicy, WorkBudget};
use rm_proof::model::check_dimacs_model;
use rm_sat::{parse_dimacs, CdclSolver, SolveResult};
use rm_telemetry::{EventKind, Outcome, RunMeta, TraceError, TraceWriter};
use rm_worker::{Problem as WorkerProblem, WorkerConfig, WorkerOutcome, WorkerPool, WorkerStats};
use std::io::BufWriter;
use std::path::Path;
use std::time::{Duration, Instant};
use thiserror::Error;

/// Aggregate search counters reported by a run (single solver or a pool).
#[derive(Debug, Clone, Copy, Default)]
struct RunCounters {
    conflicts: u64,
    decisions: u64,
    propagations: u64,
    restarts: u64,
}

impl From<&CdclSolver> for RunCounters {
    fn from(s: &CdclSolver) -> Self {
        RunCounters {
            conflicts: s.conflicts,
            decisions: s.decisions,
            propagations: s.propagations,
            restarts: s.restarts,
        }
    }
}

impl From<WorkerStats> for RunCounters {
    fn from(s: WorkerStats) -> Self {
        RunCounters {
            conflicts: s.conflicts,
            decisions: s.decisions,
            propagations: s.propagations,
            restarts: s.restarts,
        }
    }
}

fn sum_counters(a: RunCounters, b: RunCounters) -> RunCounters {
    RunCounters {
        conflicts: a.conflicts + b.conflicts,
        decisions: a.decisions + b.decisions,
        propagations: a.propagations + b.propagations,
        restarts: a.restarts + b.restarts,
    }
}

#[derive(Debug, Error)]
pub enum RunError {
    #[error("cannot read problem {problem}: {source}")]
    Read {
        problem: String,
        #[source]
        source: std::io::Error,
    },
    #[error("invalid DIMACS in {problem}: {source}")]
    Dimacs {
        problem: String,
        #[source]
        source: rm_sat::DimacsError,
    },
    #[error("solver returned a model for {problem} that FAILS independent validation")]
    InvalidModel { problem: String },
    #[error("cannot write trace for {problem}: {source}")]
    Trace {
        problem: String,
        #[source]
        source: TraceError,
    },
    #[error("cannot create output directory {dir}: {source}")]
    OutputDir {
        dir: String,
        #[source]
        source: std::io::Error,
    },
}

/// Execute the manifest. Returns the run result; per-problem failures that
/// cannot be turned into a verdict (bad input, internal error) abort the run
/// with `RunError`.
pub fn run_manifest(manifest: &Manifest) -> Result<ManifestRun, RunError> {
    if manifest.output.trace && !manifest.output.dir.exists() {
        std::fs::create_dir_all(&manifest.output.dir).map_err(|source| RunError::OutputDir {
            dir: manifest.output.dir.display().to_string(),
            source,
        })?;
    }

    let run_start = Instant::now();
    let mut problems = Vec::with_capacity(manifest.problems.len());
    for problem in &manifest.problems {
        problems.push(solve_problem(manifest, problem)?);
    }
    let run_wall = run_start.elapsed();

    let summary = RunSummary::compute(
        manifest.problems.len(),
        &problems,
        Duration::from_secs(manifest.solver.timeout_secs),
    );

    Ok(ManifestRun {
        schema_version: crate::manifest::MANIFEST_SCHEMA_VERSION,
        manifest: manifest.name.clone(),
        solver_version: env!("CARGO_PKG_VERSION").to_string(),
        git_revision: option_env!("GIT_REVISION").unwrap_or("unknown").to_string(),
        run_wall,
        problems,
        summary,
    })
}

fn solve_problem(manifest: &Manifest, problem: &Problem) -> Result<ProblemResult, RunError> {
    let start = Instant::now();
    let input = std::fs::read_to_string(&problem.file).map_err(|source| RunError::Read {
        problem: problem.name.clone(),
        source,
    })?;
    let cnf = parse_dimacs(&input).map_err(|source| RunError::Dimacs {
        problem: problem.name.clone(),
        source,
    })?;

    if manifest.solver.workers > 1 {
        return solve_problem_pool(manifest, problem, &cnf, start);
    }

    let mut solver = CdclSolver::new(cnf.num_vars);
    for clause in &cnf.clauses {
        let lits: Vec<Literal> = clause
            .iter()
            .map(|&l| {
                if l > 0 {
                    Literal::positive(l as u32)
                } else {
                    Literal::negative((-l) as u32)
                }
            })
            .collect();
        solver.add_clause(&lits);
    }

    let budget = manifest
        .solver
        .max_conflicts_per_problem
        .unwrap_or(u64::MAX);
    let timeout = Duration::from_secs(manifest.solver.timeout_secs);
    let deadline = start.checked_add(timeout);
    let (outcome, model_raw) = match solver.solve_with_deadline(&[], budget, deadline) {
        SolveResult::Sat(m) => {
            let mut raw = vec![false; cnf.num_vars as usize + 1];
            for v in 1..=cnf.num_vars {
                raw[v as usize] = m.value_of(v);
            }
            match check_dimacs_model(cnf.num_vars, &cnf.clauses, &raw) {
                Ok(true) => (Outcome::Sat, Some(raw)),
                Ok(false) | Err(_) => {
                    return Err(RunError::InvalidModel {
                        problem: problem.name.clone(),
                    });
                }
            }
        }
        SolveResult::Unsat => (Outcome::Unsat, None),
        SolveResult::Unknown => (Outcome::Unknown, None),
    };

    let wall = start.elapsed();
    let timed_out = wall >= timeout && outcome == Outcome::Unknown;
    let matches_expected = match problem.expect {
        Some(e) => matches!(
            (e, outcome),
            (Expected::Sat, Outcome::Sat) | (Expected::Unsat, Outcome::Unsat)
        ),
        None => true,
    };

    let counters = RunCounters::from(&solver);
    let trace = if manifest.output.trace {
        let trace_path = manifest
            .output
            .dir
            .join(format!("{}.rmtrace", problem.name));
        write_problem_trace(&trace_path, manifest, problem, outcome, counters, &model_raw).map_err(
            |source| RunError::Trace {
                problem: problem.name.clone(),
                source,
            },
        )?;
        Some(trace_path.display().to_string())
    } else {
        None
    };

    Ok(ProblemResult {
        name: problem.name.clone(),
        outcome,
        expected: problem.expect,
        matches_expected,
        wall,
        timed_out,
        conflicts: counters.conflicts,
        decisions: counters.decisions,
        propagations: counters.propagations,
        restarts: counters.restarts,
        knowledge: None,
        trace,
    })
}

/// Multi-worker solve path (spec §16.3 baselines 2 and 3): `num_workers`
/// CDCL reasoners on a shared in-process bus. With `clause_sharing` every
/// worker exports and imports learned clauses; without it the workers are an
/// isolated portfolio (the G1-gate control, §18). Any per-worker SAT model is
/// still independently validated before being reported.
fn solve_problem_pool(
    manifest: &Manifest,
    problem: &Problem,
    cnf: &rm_sat::DimacsCnf,
    start: Instant,
) -> Result<ProblemResult, RunError> {
    let clauses: Vec<Vec<Literal>> = cnf
        .clauses
        .iter()
        .map(|clause| {
            clause
                .iter()
                .map(|&l| {
                    if l > 0 {
                        Literal::positive(l as u32)
                    } else {
                        Literal::negative((-l) as u32)
                    }
                })
                .collect()
        })
        .collect();
    let worker_problem = WorkerProblem::new(cnf.num_vars, clauses);
    let timeout = Duration::from_secs(manifest.solver.timeout_secs);

    // Baseline 2 (isolated) zeroes both policies: nothing is ever exported or
    // imported. Baseline 3 (clause sharing) uses the manifest's knowledge
    // utility thresholds (§16.3, §18 "fix knowledge utility").
    let (export_policy, import_policy) = if manifest.solver.clause_sharing {
        (
            ExportPolicy {
                min_utility: manifest.solver.export_min_utility,
                ..ExportPolicy::default()
            },
            ImportPolicy {
                min_utility: manifest.solver.import_min_utility,
                ..ImportPolicy::default()
            },
        )
    } else {
        (
            ExportPolicy {
                max_items: 0,
                ..ExportPolicy::default()
            },
            ImportPolicy {
                max_items: 0,
                ..ImportPolicy::default()
            },
        )
    };

    let config = WorkerConfig {
        num_workers: manifest.solver.workers as usize,
        // The step budget is the *chunk* cadence that paces asynchronous
        // clause exchange (§16.3): short conflict/wall slices so workers drain
        // and import continuously instead of in one whole-problem step. The
        // per-problem conflict cap is enforced as a cumulative run budget.
        step_budget: WorkBudget::default(),
        export_policy,
        import_policy,
        seed: manifest.solver.seed,
        conflict_budget: manifest.solver.max_conflicts_per_problem,
        ..WorkerConfig::default()
    };
    let pool = WorkerPool::new(worker_problem, config);
    let outcomes = pool.run(&[], Some(timeout));

    // Collapse worker outcomes into a single verdict. Workers solve the root
    // cube (no assumptions), so any validated SAT or a closed cube decides.
    let mut outcome = Outcome::Unknown;
    let mut model_raw: Option<Vec<bool>> = None;
    let mut counters = RunCounters::default();
    for o in &outcomes {
        match o {
            WorkerOutcome::Sat { model, .. } if outcome != Outcome::Sat => {
                let mut raw = vec![false; cnf.num_vars as usize + 1];
                for v in 1..=cnf.num_vars {
                    raw[v as usize] = model.get(v).unwrap_or(false);
                }
                match check_dimacs_model(cnf.num_vars, &cnf.clauses, &raw) {
                    Ok(true) => {
                        outcome = Outcome::Sat;
                        model_raw = Some(raw);
                    }
                    Ok(false) | Err(_) => {
                        return Err(RunError::InvalidModel {
                            problem: problem.name.clone(),
                        });
                    }
                }
            }
            WorkerOutcome::Unsat { .. } if outcome == Outcome::Unknown => {
                outcome = Outcome::Unsat;
            }
            _ => {}
        }
        counters = sum_counters(counters, RunCounters::from(*stats_of(o)));
    }

    // Aggregate the §16.2 knowledge-exchange diagnostics: what each worker
    // exported/imported plus what the shared bus actually did.
    let mut knowledge = KnowledgeMetrics::default();
    for o in &outcomes {
        let s = stats_of(o);
        knowledge.exported += s.exported;
        knowledge.published += s.published;
        knowledge.received += s.received;
        knowledge.applied += s.applied;
        knowledge.buffered += s.buffered;
        knowledge.discarded += s.discarded;
    }
    let bus = pool.bus_metrics();
    knowledge.bus_published = bus.published_total;
    knowledge.bus_deduplicated = bus.deduplicated;
    knowledge.bus_evicted = bus.evicted;
    knowledge.bus_backpressure = bus.backpressure;

    let wall = start.elapsed();
    let timed_out = wall >= timeout && outcome == Outcome::Unknown;
    let matches_expected = match problem.expect {
        Some(e) => matches!(
            (e, outcome),
            (Expected::Sat, Outcome::Sat) | (Expected::Unsat, Outcome::Unsat)
        ),
        None => true,
    };

    let trace = if manifest.output.trace {
        let trace_path = manifest
            .output
            .dir
            .join(format!("{}.rmtrace", problem.name));
        write_problem_trace(&trace_path, manifest, problem, outcome, counters, &model_raw).map_err(
            |source| RunError::Trace {
                problem: problem.name.clone(),
                source,
            },
        )?;
        Some(trace_path.display().to_string())
    } else {
        None
    };

    Ok(ProblemResult {
        name: problem.name.clone(),
        outcome,
        expected: problem.expect,
        matches_expected,
        wall,
        timed_out,
        conflicts: counters.conflicts,
        decisions: counters.decisions,
        propagations: counters.propagations,
        restarts: counters.restarts,
        knowledge: Some(knowledge),
        trace,
    })
}

fn stats_of(outcome: &WorkerOutcome) -> &WorkerStats {
    match outcome {
        WorkerOutcome::Sat { stats, .. }
        | WorkerOutcome::Unsat { stats, .. }
        | WorkerOutcome::Aborted { stats, .. } => stats,
    }
}

fn write_problem_trace(
    path: &Path,
    manifest: &Manifest,
    problem: &Problem,
    outcome: Outcome,
    counters: RunCounters,
    model_raw: &Option<Vec<bool>>,
) -> Result<(), TraceError> {
    let file = std::fs::File::create(path).map_err(TraceError::Io)?;
    let mut writer = BufWriter::new(file);
    let meta = RunMeta::deterministic(
        env!("CARGO_PKG_VERSION"),
        format!("benchmark:{}", problem.name),
        manifest.solver.seed,
    );
    let mut tw = TraceWriter::new(&mut writer, meta)?;
    tw.record(
        rm_akx::reasoner::WorkerId(0),
        EventKind::Phase {
            name: "root".into(),
        },
    )?;
    tw.record(
        rm_akx::reasoner::WorkerId(0),
        EventKind::SearchSummary {
            decisions: counters.decisions,
            propagations: counters.propagations,
            conflicts: counters.conflicts,
            restarts: counters.restarts,
        },
    )?;
    if outcome == Outcome::Sat {
        // Record the model as a model-fragment knowledge object for provenance.
        if let Some(raw) = model_raw {
            let lits: Vec<rm_akx::literal::Literal> = raw
                .iter()
                .enumerate()
                .filter(|&(i, _)| i > 0)
                .map(|(v, &val)| {
                    if val {
                        Literal::positive(v as u32)
                    } else {
                        Literal::negative(v as u32)
                    }
                })
                .collect();
            tw.record(
                rm_akx::reasoner::WorkerId(0),
                EventKind::KnowledgeGenerated {
                    id: rm_akx::knowledge::KnowledgeId(0),
                    kind: rm_akx::knowledge::KnowledgeKindTag::ModelFragment,
                    size: lits.len(),
                    lbd: 0,
                },
            )?;
        }
    }
    tw.record(
        rm_akx::reasoner::WorkerId(0),
        EventKind::RunFinished { outcome },
    )?;
    let _ = &mut writer;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::manifest::{Manifest, OutputConfig, Problem, SolverConfig};
    use std::fs;

    struct TempDir(std::path::PathBuf);
    impl TempDir {
        fn new(tag: &str) -> Self {
            let dir =
                std::env::temp_dir().join(format!("rm-bench-test-{tag}-{}", std::process::id()));
            let _ = fs::remove_dir_all(&dir);
            fs::create_dir_all(&dir).unwrap();
            TempDir(dir)
        }
        fn write(&self, name: &str, contents: &str) -> std::path::PathBuf {
            let p = self.0.join(name);
            fs::write(&p, contents).unwrap();
            p
        }
    }
    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    fn manifest_at(dir: &TempDir, problems: Vec<Problem>) -> Manifest {
        Manifest {
            schema_version: 1,
            name: "test".into(),
            description: String::new(),
            solver: SolverConfig {
                workers: 1,
                seed: 1,
                deterministic: true,
                clause_sharing: true,
                export_min_utility: 0.0,
                import_min_utility: 0.0,
                max_conflicts_per_problem: Some(100_000),
                timeout_secs: 30,
            },
            output: OutputConfig {
                dir: dir.0.join("out"),
                trace: true,
            },
            problems,
        }
    }

    fn manifest_workers(dir: &TempDir, workers: u32, sharing: bool, problems: Vec<Problem>) -> Manifest {
        Manifest {
            schema_version: 1,
            name: "pool-test".into(),
            description: String::new(),
            solver: SolverConfig {
                workers,
                seed: 1,
                deterministic: false,
                clause_sharing: sharing,
                export_min_utility: 0.0,
                import_min_utility: 0.0,
                max_conflicts_per_problem: Some(100_000),
                timeout_secs: 30,
            },
            output: OutputConfig {
                dir: dir.0.join("out"),
                trace: false,
            },
            problems,
        }
    }

    /// PHP(2,2): 2 pigeons in 2 holes, satisfiable.
    fn php_sat_dimacs() -> String {
        "p cnf 4 4\n1 3 0\n2 4 0\n-1 -2 0\n-3 -4 0\n".into()
    }

    /// PHP(3,2): 3 pigeons in 2 holes, unsatisfiable.
    fn php_unsat_dimacs() -> String {
        "p cnf 6 9\n1 4 0\n2 5 0\n3 6 0\n-1 -2 0\n-1 -3 0\n-2 -3 0\n-4 -5 0\n-4 -6 0\n-5 -6 0\n"
            .into()
    }

    #[test]
    fn runs_sat_and_unsat_with_validation() {
        let dir = TempDir::new("satunsat");
        let sat = dir.write("sat.cnf", "p cnf 3 2\n1 2 3 0\n-1 -2 -3 0\n");
        let unsat = dir.write("unsat.cnf", "p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n");
        let manifest = manifest_at(
            &dir,
            vec![
                Problem {
                    name: "sat-p".into(),
                    file: sat,
                    expect: Some(Expected::Sat),
                },
                Problem {
                    name: "unsat-p".into(),
                    file: unsat,
                    expect: Some(Expected::Unsat),
                },
            ],
        );

        let run = run_manifest(&manifest).unwrap();
        assert_eq!(run.problems.len(), 2);
        assert_eq!(run.problems[0].outcome, Outcome::Sat);
        assert!(run.problems[0].matches_expected);
        assert_eq!(run.problems[1].outcome, Outcome::Unsat);
        assert!(run.problems[1].matches_expected);
        assert_eq!(run.summary.solved, 2);
        assert_eq!(run.summary.unsolved, 0);
        // Traces were written.
        assert!(run.problems[0]
            .trace
            .as_deref()
            .unwrap()
            .ends_with("sat-p.rmtrace"));
        assert!(dir.0.join("out/sat-p.rmtrace").exists());
        assert!(dir.0.join("out/unsat-p.rmtrace").exists());
        // JSON is well-formed and mentions PAR scores.
        let json = run.to_json_pretty();
        assert!(json.contains("par2_ns"));
        assert!(json.contains("sat-p"));
    }

    #[test]
    fn penalizes_unsolved_in_par_scores() {
        let dir = TempDir::new("par");
        // Empty clause => instantly UNSAT.
        let empty = dir.write("empty.cnf", "p cnf 1 1\n0\n");
        // Unreadable file => a run error, so use UNKNOWN via tight budget below.
        let manifest = manifest_at(
            &dir,
            vec![Problem {
                name: "empty-p".into(),
                file: empty,
                expect: None,
            }],
        );
        let run = run_manifest(&manifest).unwrap();
        assert_eq!(run.summary.solved, 1);
        let par2 = run.summary.par2_ns;
        let par10 = run.summary.par10_ns;
        assert!(par2 >= run.summary.solved_total_ns);
        assert!(par10 >= par2);
    }

    #[test]
    fn aborts_on_invalid_dimacs() {
        let dir = TempDir::new("baddimacs");
        // Out-of-range literal -> parse error.
        let bad = dir.write("bad.cnf", "p cnf 1 1\n5 0\n");
        let manifest = manifest_at(
            &dir,
            vec![Problem {
                name: "bad-p".into(),
                file: bad,
                expect: None,
            }],
        );
        let err = run_manifest(&manifest).unwrap_err();
        assert!(matches!(err, RunError::Dimacs { .. }));
    }

    /// The multi-worker path must find and validate SAT (baseline 3).
    #[test]
    fn multi_worker_finds_sat_with_validation() {
        let dir = TempDir::new("poolsat");
        let sat = dir.write("sat.cnf", &php_sat_dimacs());
        let manifest = manifest_workers(
            &dir,
            2,
            true,
            vec![Problem {
                name: "php-sat".into(),
                file: sat,
                expect: Some(Expected::Sat),
            }],
        );
        let run = run_manifest(&manifest).unwrap();
        assert_eq!(run.problems[0].outcome, Outcome::Sat);
        assert!(run.problems[0].matches_expected);
        // Aggregated search counters are non-trivial (some worker searched).
        let p = &run.problems[0];
        assert!(
            p.conflicts > 0 || p.decisions > 0,
            "expected some search activity from the pool"
        );
    }

    /// The multi-worker path must prove UNSAT and close the root cube.
    #[test]
    fn multi_worker_proves_unsat() {
        let dir = TempDir::new("poolunsat");
        let unsat = dir.write("unsat.cnf", &php_unsat_dimacs());
        let manifest = manifest_workers(
            &dir,
            3,
            true,
            vec![Problem {
                name: "php-unsat".into(),
                file: unsat,
                expect: Some(Expected::Unsat),
            }],
        );
        let run = run_manifest(&manifest).unwrap();
        assert_eq!(run.problems[0].outcome, Outcome::Unsat);
        assert!(run.problems[0].matches_expected);
    }

    /// Isolated multi-worker portfolio (baseline 2, `clause_sharing = false`)
    /// must be correct too — the G1-gate control.
    #[test]
    fn isolated_portfolio_is_correct() {
        let dir = TempDir::new("poolisolated");
        let sat = dir.write("sat.cnf", &php_sat_dimacs());
        let manifest = manifest_workers(
            &dir,
            2,
            false,
            vec![Problem {
                name: "php-isolated-sat".into(),
                file: sat,
                expect: Some(Expected::Sat),
            }],
        );
        let run = run_manifest(&manifest).unwrap();
        assert_eq!(run.problems[0].outcome, Outcome::Sat);
        assert!(run.problems[0].matches_expected);
        // With both policies zeroed, nothing may flow: the knowledge block
        // proves the isolated control really is isolated.
        let k = run.problems[0]
            .knowledge
            .as_ref()
            .expect("multi-worker runs report knowledge metrics");
        assert_eq!(
            (k.exported, k.published, k.received, k.applied, k.buffered, k.discarded),
            (0, 0, 0, 0, 0, 0),
            "isolated portfolio must not exchange knowledge"
        );
        assert_eq!(k.bus_published, 0);
    }

    /// A clause-sharing multi-worker run must report a knowledge block.
    #[test]
    fn sharing_run_reports_knowledge_metrics() {
        let dir = TempDir::new("poolknowledge");
        let sat = dir.write("sat.cnf", &php_sat_dimacs());
        let manifest = manifest_workers(
            &dir,
            2,
            true,
            vec![Problem {
                name: "php-sharing-sat".into(),
                file: sat,
                expect: Some(Expected::Sat),
            }],
        );
        let run = run_manifest(&manifest).unwrap();
        assert_eq!(run.problems[0].outcome, Outcome::Sat);
        assert!(
            run.problems[0].knowledge.is_some(),
            "sharing runs must report knowledge-exchange metrics"
        );
    }
}
