use clap::{Parser, Subcommand};
use rm_akx::literal::Literal;
use rm_bench::{run_manifest, Manifest};
use rm_proof::model::check_dimacs_model;
use rm_proof::proof_file::ProofFile as RmProofFile;
use rm_proof::{ProofError, ProofFile, ProofStatus};
use rm_sat::{parse_dimacs, CdclSolver, SolveResult};
use rm_smt::{SmtError, SmtSolver, SmtStatus};
use rm_telemetry::{
    now_nanos, Event, EventKind, Outcome, RunMeta, TraceError, TraceReader, TraceWriter,
};
use std::io::{BufWriter, Write};
use std::path::PathBuf;
/// Exit codes follow the SAT competition convention:
/// 10 = SAT, 20 = UNSAT, 0 = UNKNOWN/TIMEOUT, 3 = internal error (invalid model).
const EXIT_SAT: i32 = 10;
const EXIT_UNSAT: i32 = 20;
const EXIT_UNKNOWN: i32 = 0;
const EXIT_INTERNAL_ERROR: i32 = 3;

#[derive(Parser)]
#[command(name = "reasonmesh", version, about = "ReasonMesh SMT solver")]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Solve a problem file: DIMACS CNF or SMT-LIB 2.7 (QF_BV) input.
    Solve {
        /// Path to the problem file.
        file: PathBuf,
        /// Number of CPU worker threads.
        #[arg(long, default_value = "1")]
        workers: u32,
        /// Random seed.
        #[arg(long, default_value = "1")]
        seed: u64,
        /// Run deterministically (single worker, fixed seed).
        #[arg(long)]
        deterministic: bool,
        /// Disable GPU workers.
        #[arg(long)]
        no_gpu: bool,
        /// Stop after this many conflicts (default: unlimited).
        #[arg(long)]
        max_conflicts: Option<u64>,
        /// Write a replay trace (`.rmtrace`) of this run to the given path.
        #[arg(long)]
        trace: Option<PathBuf>,
        /// Write a proof certificate (`.rmproof`) to this path.
        /// SAT instances write a model proof; UNSAT instances write a DRUP proof.
        #[arg(long)]
        proof_out: Option<PathBuf>,
    },
    /// Replay a captured trace for debugging.
    Replay { trace: PathBuf },
    /// Verify an UNSAT proof/certificate.
    CheckProof { proof: PathBuf },
    /// Run a benchmark manifest.
    Benchmark { manifest: PathBuf },
}

/// Read and validate a `.rmtrace` file, printing the run summary.
fn replay_trace(path: &std::path::Path) -> Result<(), TraceError> {
    let file = std::fs::File::open(path).map_err(TraceError::Io)?;
    let reader = TraceReader::open(std::io::BufReader::new(file))?;
    let meta = reader.meta();
    println!(
        "trace: {} solver={} workers={} deterministic={}",
        path.display(),
        meta.solver_version,
        meta.num_workers,
        meta.deterministic
    );
    println!("events: {}", reader.events().len());
    println!("{}", reader.summarize().render());
    Ok(())
}

/// Solve a DIMACS instance, returning the exit code and the events recorded
/// during the run (for the optional trace output).
fn run_solve(
    file: &std::path::Path,
    max_conflicts: Option<u64>,
    proof_out: Option<&std::path::Path>,
) -> (i32, Vec<Event>) {
    let mut events: Vec<Event> = Vec::new();

    let input = match std::fs::read_to_string(file) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: cannot read {}: {e}", file.display());
            return (EXIT_INTERNAL_ERROR, events);
        }
    };

    let is_smt = file.extension().is_some_and(|e| e == "smt2" || e == "smt");
    if is_smt {
        return run_smt_solve(&input, max_conflicts, events);
    }

    let cnf = match parse_dimacs(&input) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("error: invalid DIMACS in {}: {e}", file.display());
            return (EXIT_INTERNAL_ERROR, events);
        }
    };

    let mut solver = CdclSolver::new(cnf.num_vars);
    if proof_out.is_some() {
        solver.enable_proof_logging();
    }
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

    let budget = max_conflicts.unwrap_or(u64::MAX);
    let result = solver.solve(&[], budget);
    let proof_log = solver.take_proof_log();

    let outcome = match result {
        SolveResult::Sat(m) => {
            // Independent validation: the model must satisfy the original
            // clauses, checked by code sharing nothing with the solver
            // internals (rm-proof).
            let mut raw = vec![false; cnf.num_vars as usize + 1];
            for v in 1..=cnf.num_vars {
                raw[v as usize] = m.value_of(v);
            }
            match check_dimacs_model(cnf.num_vars, &cnf.clauses, &raw) {
                Ok(true) => {
                    println!("s SATISFIABLE");
                    for v in 1..=cnf.num_vars {
                        println!("v {} {}", if raw[v as usize] { "" } else { "-" }, v);
                    }
                    // Write SAT proof if requested.
                    if let Some(path) = proof_out {
                        emit_proof_file(path, |w| {
                            RmProofFile::write_sat(cnf.num_vars, &cnf.clauses, &raw, w)
                        });
                    }
                    Outcome::Sat
                }
                Ok(false) => {
                    eprintln!(
                        "error: solver returned a model that FAILS independent \
                         validation; this is a bug"
                    );
                    return (EXIT_INTERNAL_ERROR, events);
                }
                Err(e) => {
                    eprintln!("error: cannot validate solver model ({e}); this is a bug");
                    return (EXIT_INTERNAL_ERROR, events);
                }
            }
        }
        SolveResult::Unsat => {
            println!("s UNSATISFIABLE");
            // Write UNSAT proof if requested.
            if let (Some(path), Some(drup)) = (proof_out, proof_log) {
                emit_proof_file(path, |w| {
                    RmProofFile::write_unsat(cnf.num_vars, &cnf.clauses, &drup, w)
                });
            }
            Outcome::Unsat
        }
        SolveResult::Unknown => {
            println!("s UNKNOWN");
            Outcome::Unknown
        }
    };

    // Record trace events (root phase, aggregate search counters, outcome).
    let mut seq = 0u64;
    let mut push = |events: &mut Vec<Event>, kind: EventKind| {
        seq += 1;
        events.push(Event {
            seq,
            worker: 0,
            at_nanos: now_nanos(),
            kind,
        });
    };
    push(
        &mut events,
        EventKind::Phase {
            name: "root".into(),
        },
    );
    push(
        &mut events,
        EventKind::SearchSummary {
            decisions: solver.decisions,
            propagations: solver.propagations,
            conflicts: solver.conflicts,
            restarts: solver.restarts,
        },
    );
    push(&mut events, EventKind::RunFinished { outcome });

    let code = match outcome {
        Outcome::Sat => EXIT_SAT,
        Outcome::Unsat => EXIT_UNSAT,
        Outcome::Unknown => EXIT_UNKNOWN,
    };
    (code, events)
}

/// Solve an SMT-LIB (QF_BV) input.
fn run_smt_solve(
    input: &str,
    max_conflicts: Option<u64>,
    mut events: Vec<Event>,
) -> (i32, Vec<Event>) {
    let solver = match SmtSolver::parse(input) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: invalid SMT-LIB input: {e}");
            return (EXIT_INTERNAL_ERROR, events);
        }
    };

    let budget = max_conflicts.unwrap_or(u64::MAX);
    let (status, model) = match solver.solve(budget) {
        Ok(r) => (r.status, r.values),
        Err(SmtError::UnsupportedLogic(logic)) => {
            eprintln!("error: logic {logic} is not supported yet (QF_BV only)");
            return (EXIT_UNKNOWN, events);
        }
        Err(e) => {
            eprintln!("error: {e}");
            return (EXIT_INTERNAL_ERROR, events);
        }
    };

    // Record trace events.
    let mut seq = 0u64;
    let mut push = |events: &mut Vec<Event>, kind: EventKind| {
        seq += 1;
        events.push(Event {
            seq,
            worker: 0,
            at_nanos: now_nanos(),
            kind,
        });
    };
    push(
        &mut events,
        EventKind::Phase {
            name: "root".into(),
        },
    );

    let (code, outcome) = match status {
        SmtStatus::Sat => {
            println!("s SATISFIABLE");
            if !model.is_empty() {
                println!("(model");
                for (name, value) in &model {
                    println!("  (define-fun {name} () {value})");
                }
                println!(")");
            }
            (EXIT_SAT, Outcome::Sat)
        }
        SmtStatus::Unsat => {
            println!("s UNSATISFIABLE");
            (EXIT_UNSAT, Outcome::Unsat)
        }
        SmtStatus::Unknown => {
            println!("s UNKNOWN");
            (EXIT_UNKNOWN, Outcome::Unknown)
        }
    };
    push(&mut events, EventKind::RunFinished { outcome });
    (code, events)
}

/// Write a `RunMeta` header plus events to a `.rmtrace` file.
fn write_trace(
    path: &std::path::Path,
    seed: u64,
    command_line: String,
    events: Vec<Event>,
) -> Result<(), TraceError> {
    let file = std::fs::File::create(path).map_err(TraceError::Io)?;
    let mut writer = BufWriter::new(file);
    let mut tw = TraceWriter::new(
        &mut writer,
        RunMeta::deterministic(env!("CARGO_PKG_VERSION"), command_line, seed),
    )?;
    for event in events {
        // record_at reassigns per-timeline sequence numbers monotonically; the
        // timestamps (timing metrics only) are preserved from the run.
        tw.record_at(rm_akx::reasoner::WorkerId(0), event.at_nanos, event.kind)?;
    }
    writer.flush().map_err(TraceError::Io)?;
    Ok(())
}

/// Write a proof file, reporting errors to stderr (non-fatal — the solve
/// result is still printed correctly even if proof writing fails).
fn emit_proof_file(path: &std::path::Path, write: impl FnOnce(&mut dyn std::io::Write) -> std::io::Result<()>) {
    match std::fs::File::create(path) {
        Ok(f) => {
            let mut w = std::io::BufWriter::new(f);
            if let Err(e) = write(&mut w) {
                eprintln!("warning: could not write proof to {}: {e}", path.display());
            }
        }
        Err(e) => eprintln!("warning: could not create proof file {}: {e}", path.display()),
    }
}

/// Verify a `.rmproof` file. Returns exit code: 0 = valid, 1 = invalid, 3 = error.
fn run_check_proof(path: &std::path::Path) -> i32 {
    let file = match std::fs::File::open(path) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("check-proof: cannot open {}: {e}", path.display());
            return EXIT_INTERNAL_ERROR;
        }
    };
    let proof = match ProofFile::parse(file) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("check-proof: parse error: {e}");
            return EXIT_INTERNAL_ERROR;
        }
    };
    match proof.verify() {
        Ok(()) => {
            match proof.status {
                ProofStatus::Sat => {
                    println!("VALID SAT model ({} vars, {} clauses)", proof.num_vars, proof.clauses.len());
                    EXIT_SAT
                }
                ProofStatus::Unsat => {
                    let steps = proof.drup.len();
                    println!("VALID UNSAT proof ({} vars, {} clauses, {steps} DRUP steps)", proof.num_vars, proof.clauses.len());
                    EXIT_UNSAT
                }
            }
        }
        Err(ProofError::UnsatNotSupported) => {
            eprintln!("check-proof: UNSAT status declared but no DRUP steps found in file");
            EXIT_UNKNOWN
        }
        Err(ProofError::BadModel) => {
            eprintln!("check-proof: INVALID SAT proof — model falsifies a clause");
            1
        }
        Err(e) => {
            eprintln!("check-proof: INVALID: {e}");
            1
        }
    }
}

fn main() {
    env_logger::init();
    let cli = Cli::parse();

    match cli.command {
        Command::Solve {
            file,
            workers,
            seed,
            deterministic,
            no_gpu,
            max_conflicts,
            trace,
            proof_out,
        } => {
            let workers = if deterministic { 1 } else { workers };
            log::info!(
                "solve: {} workers={} seed={}",
                file.display(),
                workers,
                seed
            );
            let _ = no_gpu; // no GPU backend yet (M5)

            let command_line = std::env::args().collect::<Vec<_>>().join(" ");
            let (code, events) = run_solve(&file, max_conflicts, proof_out.as_deref());
            if let Some(trace_path) = trace {
                match write_trace(&trace_path, seed, command_line, events) {
                    Ok(()) => log::info!("trace written to {}", trace_path.display()),
                    Err(e) => eprintln!("error: cannot write trace {}: {e}", trace_path.display()),
                }
            }
            std::process::exit(code);
        }
        Command::Replay { trace } => match replay_trace(&trace) {
            Ok(()) => std::process::exit(0),
            Err(e) => {
                eprintln!("error: {e}");
                std::process::exit(EXIT_INTERNAL_ERROR);
            }
        },
        Command::CheckProof { proof } => {
            std::process::exit(run_check_proof(&proof));
        }
        Command::Benchmark { manifest } => match Manifest::load(&manifest) {
            Ok(m) => match run_manifest(&m) {
                Ok(run) => {
                    let out = run.to_json_pretty();
                    println!("{out}");
                    std::process::exit(0);
                }
                Err(e) => {
                    eprintln!("error: benchmark run failed: {e}");
                    std::process::exit(EXIT_INTERNAL_ERROR);
                }
            },
            Err(e) => {
                eprintln!(
                    "error: invalid benchmark manifest {}: {e}",
                    manifest.display()
                );
                std::process::exit(EXIT_INTERNAL_ERROR);
            }
        },
    }
}
