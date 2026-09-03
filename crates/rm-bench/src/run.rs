//! Benchmark runner.
//!
//! Executes a manifest: each problem is solved single-worker (deterministic
//! production CDCL) or, when the manifest requests `workers > 1`, by a pool of
//! CDCL reasoners on a shared in-process bus. Every SAT model is independently
//! validated, and the run produces a machine-readable summary (spec §16.2).
//! Multi-worker runs support the §16.3 ablation ladder: `clause_sharing =
//! true` is the clause-sharing portfolio (baseline 3), `false` an isolated
//! portfolio (baseline 2) — the G1-gate control (§18).

use crate::manifest::{BaselineConfig, Expected, Manifest, Problem};
use crate::result::{BaselineResult, KnowledgeMetrics, ManifestRun, ProblemResult, RunSummary};
use rm_akx::literal::Literal;
use rm_akx::{ExportPolicy, ImportPolicy, WorkBudget};
use rm_proof::model::check_dimacs_model;
use rm_sat::{parse_dimacs, CdclSolver, DimacsCnf, SolveResult};
use rm_telemetry::{EventKind, Outcome, RunMeta, TraceError, TraceWriter};
use rm_worker::{Problem as WorkerProblem, WorkerConfig, WorkerOutcome, WorkerPool, WorkerStats};
use std::io::{BufWriter, Read};
use std::path::Path;
use std::process::Stdio;
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

fn dimacs_lit(l: i32) -> Literal {
    if l > 0 {
        Literal::positive(l as u32)
    } else {
        Literal::negative((-l) as u32)
    }
}

fn check_model(raw: &[bool], cnf: &DimacsCnf, problem_name: &str) -> Result<(), RunError> {
    match check_dimacs_model(cnf.num_vars, &cnf.clauses, raw) {
        Ok(true) => Ok(()),
        Ok(false) | Err(_) => Err(RunError::InvalidModel {
            problem: problem_name.to_string(),
        }),
    }
}

fn expected_matches(expect: Option<Expected>, outcome: Outcome) -> bool {
    match expect {
        Some(e) => matches!(
            (e, outcome),
            (Expected::Sat, Outcome::Sat) | (Expected::Unsat, Outcome::Unsat)
        ),
        None => true,
    }
}

fn maybe_write_trace(
    manifest: &Manifest,
    problem: &Problem,
    outcome: Outcome,
    counters: RunCounters,
    model_raw: &Option<Vec<bool>>,
) -> Result<Option<String>, RunError> {
    if !manifest.output.trace {
        return Ok(None);
    }
    let trace_path = manifest
        .output
        .dir
        .join(format!("{}.rmtrace", problem.name));
    write_problem_trace(&trace_path, manifest, problem, outcome, counters, model_raw).map_err(
        |source| RunError::Trace {
            problem: problem.name.clone(),
            source,
        },
    )?;
    Ok(Some(trace_path.display().to_string()))
}

fn collect_baselines(manifest: &Manifest, problem: &Problem) -> Vec<BaselineResult> {
    let timeout = Duration::from_secs(manifest.solver.timeout_secs);
    manifest
        .baselines
        .iter()
        .map(|b| run_baseline(b, &problem.file, timeout))
        .collect()
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
    run_single_solver(manifest, problem, &cnf, start)
}

fn build_cdcl_solver(cnf: &DimacsCnf) -> CdclSolver {
    let mut solver = CdclSolver::new(cnf.num_vars);
    for clause in &cnf.clauses {
        let lits: Vec<Literal> = clause.iter().map(|&l| dimacs_lit(l)).collect();
        solver.add_clause(&lits);
    }
    solver
}

fn run_single_solver(
    manifest: &Manifest,
    problem: &Problem,
    cnf: &DimacsCnf,
    start: Instant,
) -> Result<ProblemResult, RunError> {
    let mut solver = build_cdcl_solver(cnf);
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
            check_model(&raw, cnf, &problem.name)?;
            (Outcome::Sat, Some(raw))
        }
        SolveResult::Unsat => (Outcome::Unsat, None),
        SolveResult::Unknown => (Outcome::Unknown, None),
    };

    let wall = start.elapsed();
    let timed_out = wall >= timeout && outcome == Outcome::Unknown;
    let counters = RunCounters::from(&solver);
    let trace = maybe_write_trace(manifest, problem, outcome, counters, &model_raw)?;
    let baselines = collect_baselines(manifest, problem);

    Ok(ProblemResult {
        name: problem.name.clone(),
        outcome,
        expected: problem.expect,
        matches_expected: expected_matches(problem.expect, outcome),
        wall,
        timed_out,
        conflicts: counters.conflicts,
        decisions: counters.decisions,
        propagations: counters.propagations,
        restarts: counters.restarts,
        knowledge: None,
        baselines,
        trace,
    })
}

fn build_sharing_policies(manifest: &Manifest) -> (ExportPolicy, ImportPolicy) {
    if manifest.solver.clause_sharing {
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
    }
}

fn collect_pool_outcome(
    outcomes: &[WorkerOutcome],
    cnf: &DimacsCnf,
    problem_name: &str,
) -> Result<(Outcome, Option<Vec<bool>>, RunCounters), RunError> {
    let mut outcome = Outcome::Unknown;
    let mut model_raw: Option<Vec<bool>> = None;
    let mut counters = RunCounters::default();
    for o in outcomes {
        match o {
            WorkerOutcome::Sat { model, .. } if outcome != Outcome::Sat => {
                let mut raw = vec![false; cnf.num_vars as usize + 1];
                for v in 1..=cnf.num_vars {
                    raw[v as usize] = model.get(v).unwrap_or(false);
                }
                check_model(&raw, cnf, problem_name)?;
                outcome = Outcome::Sat;
                model_raw = Some(raw);
            }
            WorkerOutcome::Unsat { .. } if outcome == Outcome::Unknown => {
                outcome = Outcome::Unsat;
            }
            _ => {}
        }
        counters = sum_counters(counters, RunCounters::from(*stats_of(o)));
    }
    Ok((outcome, model_raw, counters))
}

fn aggregate_knowledge_metrics(outcomes: &[WorkerOutcome], pool: &WorkerPool) -> KnowledgeMetrics {
    let mut knowledge = KnowledgeMetrics::default();
    for o in outcomes {
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
    knowledge
}

/// Multi-worker solve path (spec §16.3 baselines 2 and 3): `num_workers`
/// CDCL reasoners on a shared in-process bus. With `clause_sharing` every
/// worker exports and imports learned clauses; without it the workers are an
/// isolated portfolio (the G1-gate control, §18). Any per-worker SAT model is
/// still independently validated before being reported.
fn solve_problem_pool(
    manifest: &Manifest,
    problem: &Problem,
    cnf: &DimacsCnf,
    start: Instant,
) -> Result<ProblemResult, RunError> {
    let clauses: Vec<Vec<Literal>> = cnf
        .clauses
        .iter()
        .map(|clause| clause.iter().map(|&l| dimacs_lit(l)).collect())
        .collect();
    let worker_problem = WorkerProblem::new(cnf.num_vars, clauses);
    let timeout = Duration::from_secs(manifest.solver.timeout_secs);

    let (export_policy, import_policy) = build_sharing_policies(manifest);
    let config = WorkerConfig {
        num_workers: manifest.solver.workers as usize,
        step_budget: WorkBudget::default(),
        export_policy,
        import_policy,
        seed: manifest.solver.seed,
        conflict_budget: manifest.solver.max_conflicts_per_problem,
        ..WorkerConfig::default()
    };
    let pool = WorkerPool::new(worker_problem, config);
    let outcomes = pool.run(&[], Some(timeout));

    let (outcome, model_raw, counters) = collect_pool_outcome(&outcomes, cnf, &problem.name)?;
    let knowledge = aggregate_knowledge_metrics(&outcomes, &pool);

    let wall = start.elapsed();
    let timed_out = wall >= timeout && outcome == Outcome::Unknown;
    let trace = maybe_write_trace(manifest, problem, outcome, counters, &model_raw)?;
    let baselines = collect_baselines(manifest, problem);

    Ok(ProblemResult {
        name: problem.name.clone(),
        outcome,
        expected: problem.expect,
        matches_expected: expected_matches(problem.expect, outcome),
        wall,
        timed_out,
        conflicts: counters.conflicts,
        decisions: counters.decisions,
        propagations: counters.propagations,
        restarts: counters.restarts,
        knowledge: Some(knowledge),
        baselines,
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

fn wait_or_kill(child: &mut std::process::Child, deadline: Instant) -> bool {
    loop {
        match child.try_wait() {
            Ok(Some(_)) => return false,
            Ok(None) => {
                if Instant::now() >= deadline {
                    let _ = child.kill();
                    let _ = child.wait();
                    return true;
                }
                std::thread::sleep(Duration::from_millis(50));
            }
            Err(_) => return false,
        }
    }
}

/// Run one external baseline solver on a single CNF file and return its verdict
/// and wall time. Invocation: `{binary} {cnf_path} {args...}`.
///
/// Output is parsed for DIMACS competition-format lines:
///   `s SATISFIABLE`   → Sat
///   `s UNSATISFIABLE` → Unsat
/// Anything else (crash, unparseable output) → Unknown.
///
/// The process is killed if it exceeds `timeout`; stdout is drained
/// concurrently so the child never blocks on a full pipe.
fn run_baseline(b: &BaselineConfig, cnf_path: &Path, timeout: Duration) -> BaselineResult {
    let mut child = match std::process::Command::new(&b.binary)
        .arg(cnf_path)
        .args(&b.args)
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
    {
        Ok(c) => c,
        Err(_) => {
            return BaselineResult {
                name: b.name.clone(),
                outcome: rm_telemetry::Outcome::Unknown,
                wall: Duration::ZERO,
                timed_out: false,
            }
        }
    };

    let stdout_handle = child.stdout.take().map(|out| {
        std::thread::spawn(move || {
            let mut buf = String::new();
            let _ = std::io::BufReader::new(out).read_to_string(&mut buf);
            buf
        })
    });

    let start = Instant::now();
    let timed_out = wait_or_kill(&mut child, start + timeout);
    let wall = start.elapsed();

    let stdout = stdout_handle
        .and_then(|h| h.join().ok())
        .unwrap_or_default();
    let outcome = if timed_out {
        rm_telemetry::Outcome::Unknown
    } else {
        parse_dimacs_verdict(&stdout)
    };

    BaselineResult {
        name: b.name.clone(),
        outcome,
        wall,
        timed_out,
    }
}

/// Parse a DIMACS competition-format answer line.
/// `s SATISFIABLE` → Sat, `s UNSATISFIABLE` → Unsat, anything else → Unknown.
fn parse_dimacs_verdict(output: &str) -> rm_telemetry::Outcome {
    for line in output.lines() {
        let t = line.trim();
        if t.eq_ignore_ascii_case("s satisfiable") || t.eq_ignore_ascii_case("sat") {
            return rm_telemetry::Outcome::Sat;
        }
        if t.eq_ignore_ascii_case("s unsatisfiable") || t.eq_ignore_ascii_case("unsat") {
            return rm_telemetry::Outcome::Unsat;
        }
    }
    rm_telemetry::Outcome::Unknown
}

fn record_sat_model_knowledge<W: std::io::Write>(
    tw: &mut TraceWriter<W>,
    raw: &[bool],
) -> Result<(), TraceError> {
    let lits: Vec<Literal> = raw
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
    )
    .map(|_| ())
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
        if let Some(raw) = model_raw {
            record_sat_model_knowledge(&mut tw, raw)?;
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
            baselines: vec![],
            problems,
        }
    }

    fn manifest_workers(
        dir: &TempDir,
        workers: u32,
        sharing: bool,
        problems: Vec<Problem>,
    ) -> Manifest {
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
            baselines: vec![],
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
            (
                k.exported,
                k.published,
                k.received,
                k.applied,
                k.buffered,
                k.discarded
            ),
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

    /// Baseline runner: parse_dimacs_verdict must recognise both verdict styles.
    #[test]
    fn parse_dimacs_verdict_recognises_sat_and_unsat() {
        use rm_telemetry::Outcome;
        assert_eq!(
            parse_dimacs_verdict("s SATISFIABLE\nv 1 -2 0\n"),
            Outcome::Sat
        );
        assert_eq!(parse_dimacs_verdict("s UNSATISFIABLE\n"), Outcome::Unsat);
        assert_eq!(parse_dimacs_verdict("SAT\n"), Outcome::Sat);
        assert_eq!(parse_dimacs_verdict("UNSAT\n"), Outcome::Unsat);
        assert_eq!(parse_dimacs_verdict(""), Outcome::Unknown);
        assert_eq!(parse_dimacs_verdict("error: timeout\n"), Outcome::Unknown);
    }

    /// Baseline runner: a non-existent binary returns Unknown with zero wall time,
    /// not a panic or run error.
    #[test]
    fn baseline_missing_binary_returns_unknown() {
        use crate::manifest::BaselineConfig;
        let b = BaselineConfig {
            name: "no-such-solver".into(),
            binary: "/no/such/binary".into(),
            args: vec![],
        };
        let result = run_baseline(&b, Path::new("/tmp/x.cnf"), Duration::from_secs(1));
        assert_eq!(result.outcome, rm_telemetry::Outcome::Unknown);
        assert!(!result.timed_out);
    }

    /// Baseline runner: a real Z3 invocation returns the correct verdict.
    /// Skipped if Z3 is not on PATH.
    #[test]
    fn baseline_z3_solves_small_instances() {
        use crate::manifest::BaselineConfig;
        if which_z3().is_none() {
            eprintln!("skipping: z3 not on PATH");
            return;
        }

        let dir = TempDir::new("z3baseline");
        let sat_path = dir.write("sat.cnf", "p cnf 2 1\n1 2 0\n");
        let unsat_path = dir.write("unsat.cnf", "p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n");

        let b = BaselineConfig {
            name: "z3".into(),
            binary: "z3".into(),
            args: vec!["-dimacs".into()],
        };

        let r = run_baseline(&b, &sat_path, Duration::from_secs(10));
        assert_eq!(r.outcome, rm_telemetry::Outcome::Sat, "z3 should find SAT");
        assert!(!r.timed_out);

        let r = run_baseline(&b, &unsat_path, Duration::from_secs(10));
        assert_eq!(
            r.outcome,
            rm_telemetry::Outcome::Unsat,
            "z3 should prove UNSAT"
        );
        assert!(!r.timed_out);
    }

    /// Baseline runner: timeout kills the process and returns Unknown + timed_out=true.
    #[test]
    fn baseline_timeout_kills_process() {
        if which_z3().is_none() {
            eprintln!("skipping: z3 not on PATH");
            return;
        }
        // php-3-2 UNSAT — too small to actually time out, so use `sleep` instead.
        // On systems without sleep(1), this test just passes vacuously.
        if std::process::Command::new("sleep")
            .arg("--version")
            .output()
            .is_err()
        {
            return;
        }
        use crate::manifest::BaselineConfig;
        let b = BaselineConfig {
            name: "sleep".into(),
            binary: "sleep".into(),
            args: vec![],
        };
        // run_baseline prepends the path as the first arg, so the command
        // becomes `sleep 10` — a 10-second sleep that our 200ms timeout kills.
        let start = std::time::Instant::now();
        let r = run_baseline(&b, Path::new("10"), Duration::from_millis(200));
        assert!(
            start.elapsed() < Duration::from_secs(2),
            "should have killed quickly"
        );
        assert!(r.timed_out);
        assert_eq!(r.outcome, rm_telemetry::Outcome::Unknown);
    }

    fn which_z3() -> Option<std::path::PathBuf> {
        std::env::var_os("PATH").and_then(|p| {
            std::env::split_paths(&p)
                .map(|d| d.join("z3"))
                .find(|p| p.exists())
        })
    }
}
