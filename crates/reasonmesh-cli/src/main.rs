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
use rm_bus::{BusConfig, BusError, KnowledgeBus, PollBudget, PublishHandle};
use rm_bus::inproc::InprocBus;
use rm_akx::{BusMetrics, KnowledgeBatch, Scope};
use std::io::{BufWriter, Write};
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Duration;

/// Dual-queue bus: workers publish to both a local bus (for intra-node sharing)
/// and an export bus (drained exclusively by the cross-node bridge thread).
/// Workers import from the local bus, which the bridge also writes incoming
/// remote clauses into. This prevents the bridge from stealing locally-needed
/// clauses while still forwarding all exported clauses to remote nodes.
struct BroadcastBus {
    local: Arc<InprocBus>,
    export: Arc<InprocBus>,
    /// Clauses that could not be enqueued in the export bus (buffer full).
    /// These are never forwarded to remote peers. Tracked for operator
    /// visibility — silent export loss was the original bug.
    export_dropped: std::sync::atomic::AtomicU64,
}

impl BroadcastBus {
    fn new(config: &BusConfig) -> Self {
        BroadcastBus {
            local: Arc::new(InprocBus::new(config)),
            export: Arc::new(InprocBus::new(config)),
            export_dropped: std::sync::atomic::AtomicU64::new(0),
        }
    }
    fn export_bus(&self) -> Arc<InprocBus> { Arc::clone(&self.export) }
    fn local_bus(&self) -> Arc<InprocBus> { Arc::clone(&self.local) }
    fn export_dropped_total(&self) -> u64 {
        self.export_dropped.load(Ordering::Relaxed)
    }
}

impl KnowledgeBus for BroadcastBus {
    fn publish(&self, scope: Scope, batch: KnowledgeBatch) -> Result<PublishHandle, BusError> {
        // Export bus: bridge reads this exclusively. Silently dropping here
        // means those clauses are never shared with remote peers, so we count
        // the loss explicitly rather than swallowing it.
        match self.export.publish(scope, batch.clone()) {
            Ok(_) => {}
            Err(BusError::BufferFull) => {
                self.export_dropped
                    .fetch_add(batch.len() as u64, Ordering::Relaxed);
            }
            Err(_) => {}
        }
        // Local bus: workers read this; back-pressure propagates to caller.
        self.local.publish(scope, batch)
    }
    fn poll(&self, budget: PollBudget) -> Result<KnowledgeBatch, BusError> {
        self.local.poll(budget)
    }
    fn metrics(&self) -> BusMetrics {
        let mut m = self.local.metrics();
        // Fold export drops into backpressure so the caller sees the full
        // picture of clauses that did not reach the network.
        m.backpressure += self.export_dropped.load(Ordering::Relaxed);
        m
    }
}
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
    /// Run as a cluster node: load a DIMACS file, start local workers, and
    /// exchange learned clauses with peer nodes over TCP (AKX NetBus).
    ///
    /// All nodes load the same problem file and race to solve it. Learned
    /// clauses propagate across the network, accelerating the whole fleet.
    /// This is the entry point for multi-machine parallel SAT.
    Serve {
        /// Path to the DIMACS CNF file to solve.
        file: PathBuf,
        /// TCP port to listen on for peer connections.
        #[arg(long, default_value_t = 9000u16)]
        port: u16,
        /// Number of CDCL worker threads on this node.
        #[arg(long, default_value_t = 4u32)]
        workers: u32,
        /// Base random seed (workers get seed, seed+1, seed+2, …).
        /// Use different seeds on each node for portfolio diversification.
        #[arg(long, default_value_t = 1u64)]
        seed: u64,
        /// Peer node addresses in "host:port" form. May be repeated.
        #[arg(long = "peer")]
        peers: Vec<String>,
        /// Wall-clock timeout in seconds before this node reports UNKNOWN.
        #[arg(long, default_value_t = 300u64)]
        timeout_secs: u64,
        /// Cross-node bridge polling interval in milliseconds.
        #[arg(long, default_value_t = 50u64)]
        bridge_ms: u64,
    },
    /// Replay a captured trace for debugging.
    Replay { trace: PathBuf },
    /// Verify an UNSAT proof/certificate.
    CheckProof { proof: PathBuf },
    /// Run a benchmark manifest.
    Benchmark { manifest: PathBuf },
}

/// Multi-node cluster solve: load DIMACS, start a WorkerPool, bind a NetBus
/// listener, connect to peers, run a bridge thread forwarding learned clauses
/// across the network, then report the verdict.
///
/// The "bridge" polls the local InprocBus and forwards clauses to all peers
/// via the NetBus, and vice versa — implementing cross-node AKX sharing
/// without modifying the WorkerPool internals. Each clause crosses the network
/// once per bridge interval (50ms default), filtered by the global export
/// utility gate (LBD≤3 by default).
fn run_serve(
    file: &std::path::Path,
    port: u16,
    num_workers: usize,
    seed: u64,
    peers: &[String],
    timeout_secs: u64,
    bridge_ms: u64,
) -> i32 {
    use rm_bus::net::{NetBus, NetConfig};
    use rm_worker::{Problem, WorkerConfig, WorkerPool, WorkerOutcome};

    // Parse DIMACS.
    let input = match std::fs::read_to_string(file) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: cannot read {}: {e}", file.display());
            return EXIT_INTERNAL_ERROR;
        }
    };
    let cnf = match parse_dimacs(&input) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("error: invalid DIMACS in {}: {e}", file.display());
            return EXIT_INTERNAL_ERROR;
        }
    };

    let clauses: Vec<Vec<Literal>> = cnf.clauses.iter().map(|clause| {
        clause.iter().map(|&l| {
            if l > 0 { Literal::positive(l as u32) } else { Literal::negative((-l) as u32) }
        }).collect()
    }).collect();
    let problem = Problem::new(cnf.num_vars, clauses);

    // BroadcastBus: workers publish to both local (for peer workers) and export
    // (drained exclusively by the bridge thread). Workers import from local
    // only. This cleanly separates local sharing from cross-node forwarding.
    let bcast = Arc::new(BroadcastBus::new(&BusConfig::default()));
    let export_bus = bcast.export_bus();
    let local_bus = bcast.local_bus();

    let pool_cfg = WorkerConfig {
        num_workers,
        seed,
        ..WorkerConfig::default()
    };
    let pool = WorkerPool::with_bus(
        problem,
        pool_cfg,
        Arc::clone(&bcast) as Arc<dyn KnowledgeBus>,
    );

    // Bind the NetBus listener (accept_loop runs in a background thread).
    let bind_addr: std::net::SocketAddr = format!("0.0.0.0:{port}").parse().unwrap();
    let net_bus = match NetBus::bind(bind_addr, NetConfig::default()) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("error: cannot bind :{port}: {e}");
            return EXIT_INTERNAL_ERROR;
        }
    };
    eprintln!("info: listening on 0.0.0.0:{port}");

    // Connect to each peer with up to 30s of retry so all nodes can start
    // concurrently without a fixed leader.
    for peer_str in peers {
        eprintln!("info: connecting to {peer_str} ...");
        match net_bus.connect_peer_retry(peer_str, Duration::from_secs(30)) {
            Ok(()) => eprintln!("info: connected to {peer_str}"),
            Err(e) => {
                eprintln!("error: cannot connect to {peer_str}: {e}");
                return EXIT_INTERNAL_ERROR;
            }
        }
    }

    // Bridge thread:
    //   export_bus → NetBus: forward locally learned clauses to all TCP peers
    //   NetBus → local_bus: inject peer clauses so local workers can import them
    //
    // The loop is event-driven: it only sleeps when both directions are idle,
    // so clause bursts are drained at full speed without a fixed 50 ms lag
    // between the export-forward and net-inject phases.
    let bridge_shutdown = Arc::new(AtomicBool::new(false));
    let bridge_handle = {
        let net = Arc::clone(&net_bus);
        let shutdown = Arc::clone(&bridge_shutdown);
        let idle_interval = Duration::from_millis(bridge_ms);
        std::thread::Builder::new()
            .name("rm-bridge".into())
            .spawn(move || {
                loop {
                    if shutdown.load(Ordering::Acquire) {
                        break;
                    }
                    let mut active = false;
                    if let Ok(batch) = export_bus.poll(PollBudget { max_items: 64 }) {
                        if !batch.is_empty() {
                            let _ = net.publish(Scope::Global, batch);
                            active = true;
                        }
                    }
                    if let Ok(batch) = net.poll(PollBudget { max_items: 64 }) {
                        if !batch.is_empty() {
                            let _ = local_bus.publish(Scope::Process, batch);
                            active = true;
                        }
                    }
                    // Sleep only when both directions were idle. Under load the
                    // bridge runs at full CPU speed; at rest it yields the core.
                    if !active {
                        std::thread::sleep(idle_interval);
                    }
                }
            })
            .expect("spawn bridge thread")
    };

    eprintln!("info: starting {num_workers} workers, timeout={timeout_secs}s");
    let outcomes = pool.run(&[], Some(Duration::from_secs(timeout_secs)));
    bridge_shutdown.store(true, Ordering::Release);
    // Join the bridge so its panic (if any) surfaces here rather than being
    // silently swallowed, and so TCP sockets are cleanly drained before exit.
    bridge_handle.join().expect("bridge thread panicked");

    let nm = net_bus.metrics();
    eprintln!(
        "info: net_bus published={} bytes_out={} bytes_in={} incoming_evicted={}",
        nm.published_total, nm.bytes_serialized, nm.bytes_received, nm.evicted
    );
    let export_dropped = bcast.export_dropped_total();
    if export_dropped > 0 {
        eprintln!(
            "warn: export_bus dropped {export_dropped} clause(s) — bridge could not keep up; \
             consider reducing --workers or increasing --bridge-ms"
        );
    }

    let sat = outcomes.iter().any(|o| matches!(o, WorkerOutcome::Sat { .. }));
    let unsat = outcomes.iter().any(|o| matches!(o, WorkerOutcome::Unsat { .. }));
    if sat {
        println!("s SATISFIABLE");
        EXIT_SAT
    } else if unsat {
        println!("s UNSATISFIABLE");
        EXIT_UNSAT
    } else {
        println!("s UNKNOWN");
        EXIT_UNKNOWN
    }
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
        Command::Serve {
            file,
            port,
            workers,
            seed,
            peers,
            timeout_secs,
            bridge_ms,
        } => {
            std::process::exit(run_serve(
                &file,
                port,
                workers as usize,
                seed,
                &peers,
                timeout_secs,
                bridge_ms,
            ));
        }
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
