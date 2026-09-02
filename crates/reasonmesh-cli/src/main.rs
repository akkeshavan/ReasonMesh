use clap::{Parser, Subcommand};
use rm_akx::literal::Literal;
use rm_bench::{run_manifest, Manifest};
use rm_proof::model::check_dimacs_model;
use rm_proof::proof_file::ProofFile as RmProofFile;
use rm_proof::{ProofError, ProofFile, ProofStatus};
use rm_sat::{parse_dimacs, CdclSolver, DimacsCnf, SolveResult};
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
///
/// The export bus uses per-object publishing so the queue's utility-based
/// eviction considers each clause independently — a batch-level publish would
/// abort on the first full-queue failure and silently discard all remaining
/// objects even if they are high enough utility to evict something.
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
        let mut dropped = 0u64;
        for obj in &batch {
            if self.export.publish(scope, vec![obj.clone()]).is_err() {
                dropped += 1;
            }
        }
        if dropped > 0 {
            self.export_dropped.fetch_add(dropped, Ordering::Relaxed);
        }
        self.local.publish(scope, batch)
    }
    fn poll(&self, budget: PollBudget) -> Result<KnowledgeBatch, BusError> {
        self.local.poll(budget)
    }
    fn metrics(&self) -> BusMetrics {
        let mut m = self.local.metrics();
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
        /// Maximum LBD of learned clauses forwarded to remote peers.
        /// Only clauses with LBD ≤ this value enter the cross-node export queue.
        /// Corresponds to the HIGH_UTILITY filter in the TLA+ specification
        /// (spec axiom: KEY_CLAUSES ⊆ HIGH_UTILITY). Set to 0 to forward all clauses.
        #[arg(long, default_value_t = 6u32)]
        export_lbd: u32,
    },
    /// Replay a captured trace for debugging.
    Replay { trace: PathBuf },
    /// Verify an UNSAT proof/certificate.
    CheckProof { proof: PathBuf },
    /// Run a benchmark manifest.
    Benchmark { manifest: PathBuf },
}

/// Parse a DIMACS file and convert it into a `Problem` ready for the worker pool.
fn load_cnf_problem(file: &std::path::Path) -> Result<rm_worker::Problem, i32> {
    use rm_worker::Problem;
    let input = std::fs::read_to_string(file).map_err(|e| {
        eprintln!("error: cannot read {}: {e}", file.display());
        EXIT_INTERNAL_ERROR
    })?;
    let cnf = parse_dimacs(&input).map_err(|e| {
        eprintln!("error: invalid DIMACS in {}: {e}", file.display());
        EXIT_INTERNAL_ERROR
    })?;
    let clauses: Vec<Vec<Literal>> = cnf.clauses.iter().map(|clause| {
        clause.iter().map(|&l| {
            if l > 0 { Literal::positive(l as u32) } else { Literal::negative((-l) as u32) }
        }).collect()
    }).collect();
    Ok(Problem::new(cnf.num_vars, clauses))
}

/// Connect to each peer address, retrying for up to 30 s so all nodes can
/// start concurrently without a fixed leader.
fn connect_peers(net: &Arc<rm_bus::net::NetBus>, peers: &[String]) -> Result<(), i32> {
    for peer_str in peers {
        eprintln!("info: connecting to {peer_str} ...");
        match net.connect_peer_retry(peer_str, Duration::from_secs(30)) {
            Ok(()) => eprintln!("info: connected to {peer_str}"),
            Err(e) => {
                eprintln!("error: cannot connect to {peer_str}: {e}");
                return Err(EXIT_INTERNAL_ERROR);
            }
        }
    }
    Ok(())
}

/// Spawn the bridge thread that forwards clauses in both directions:
///   export_bus → net: locally learned clauses go to all TCP peers.
///   net → local_bus: peer clauses are injected for local workers to import.
///
/// The loop is event-driven; it only sleeps when both directions are idle so
/// clause bursts drain at full speed without a fixed polling delay.
fn spawn_bridge_thread(
    export_bus: Arc<InprocBus>,
    local_bus: Arc<InprocBus>,
    net: Arc<rm_bus::net::NetBus>,
    shutdown: Arc<AtomicBool>,
    idle_ms: u64,
) -> std::thread::JoinHandle<()> {
    let idle_interval = Duration::from_millis(idle_ms);
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
                if !active {
                    std::thread::sleep(idle_interval);
                }
            }
        })
        .expect("spawn bridge thread")
}

/// Print the serve verdict based on the worker outcomes, returning an exit code.
fn serve_verdict(outcomes: &[rm_worker::WorkerOutcome]) -> i32 {
    use rm_worker::WorkerOutcome;
    if outcomes.iter().any(|o| matches!(o, WorkerOutcome::Sat { .. })) {
        println!("s SATISFIABLE");
        EXIT_SAT
    } else if outcomes.iter().any(|o| matches!(o, WorkerOutcome::Unsat { .. })) {
        println!("s UNSATISFIABLE");
        EXIT_UNSAT
    } else {
        println!("s UNKNOWN");
        EXIT_UNKNOWN
    }
}

/// Multi-node cluster solve: load DIMACS, start a WorkerPool, bind a NetBus
/// listener, connect to peers, run a bridge thread forwarding learned clauses
/// across the network, then report the verdict.
///
/// The "bridge" is event-driven: it drains the export queue and the incoming
/// network queue at full speed whenever either is non-empty, sleeping only
/// when both are idle. Only clauses with LBD ≤ `export_lbd` enter the
/// cross-node export queue (HIGH_UTILITY filter from the TLA+ spec).
fn run_serve(
    file: &std::path::Path,
    port: u16,
    num_workers: usize,
    seed: u64,
    peers: &[String],
    timeout_secs: u64,
    bridge_ms: u64,
    export_lbd: u32,
) -> i32 {
    use rm_bus::net::{NetBus, NetConfig};
    use rm_akx::ExportPolicy;
    use rm_worker::{WorkerConfig, WorkerPool};

    let problem = match load_cnf_problem(file) {
        Ok(p) => p,
        Err(code) => return code,
    };

    let bcast = Arc::new(BroadcastBus::new(&BusConfig::default()));
    let export_min_utility = if export_lbd == 0 {
        0.0_f32
    } else {
        1.0_f32 / (1.0 + export_lbd as f32)
    };
    let pool = WorkerPool::with_bus(
        problem,
        WorkerConfig {
            num_workers,
            seed,
            export_policy: ExportPolicy {
                min_utility: export_min_utility,
                ..ExportPolicy::default()
            },
            ..WorkerConfig::default()
        },
        Arc::clone(&bcast) as Arc<dyn KnowledgeBus>,
    );

    let bind_addr: std::net::SocketAddr = format!("0.0.0.0:{port}").parse().unwrap();
    let net_bus = match NetBus::bind(bind_addr, NetConfig::default()) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("error: cannot bind :{port}: {e}");
            return EXIT_INTERNAL_ERROR;
        }
    };
    eprintln!("info: listening on 0.0.0.0:{port}");

    if let Err(code) = connect_peers(&net_bus, peers) {
        return code;
    }

    let bridge_shutdown = Arc::new(AtomicBool::new(false));
    let bridge_handle = spawn_bridge_thread(
        bcast.export_bus(),
        bcast.local_bus(),
        Arc::clone(&net_bus),
        Arc::clone(&bridge_shutdown),
        bridge_ms,
    );

    eprintln!("info: starting {num_workers} workers, timeout={timeout_secs}s");
    let outcomes = pool.run(&[], Some(Duration::from_secs(timeout_secs)));
    bridge_shutdown.store(true, Ordering::Release);
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

    serve_verdict(&outcomes)
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

/// Build a `CdclSolver` loaded with all clauses from `cnf`.
fn build_dimacs_solver(cnf: &DimacsCnf, with_proof: bool) -> CdclSolver {
    let mut solver = CdclSolver::new(cnf.num_vars);
    if with_proof {
        solver.enable_proof_logging();
    }
    for clause in &cnf.clauses {
        let lits: Vec<Literal> = clause
            .iter()
            .map(|&l| {
                if l > 0 { Literal::positive(l as u32) } else { Literal::negative((-l) as u32) }
            })
            .collect();
        solver.add_clause(&lits);
    }
    solver
}

/// Validate a SAT model against the original clauses (using code that shares
/// nothing with the solver internals), print the result, and write any
/// requested proof file. Returns the outcome on success, or an exit code on
/// internal error.
fn handle_sat_model(
    m: rm_sat::Model,
    cnf: &DimacsCnf,
    proof_out: Option<&std::path::Path>,
) -> Result<Outcome, i32> {
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
            if let Some(path) = proof_out {
                emit_proof_file(path, |w| {
                    RmProofFile::write_sat(cnf.num_vars, &cnf.clauses, &raw, w)
                });
            }
            Ok(Outcome::Sat)
        }
        Ok(false) => {
            eprintln!("error: solver returned a model that FAILS independent validation; this is a bug");
            Err(EXIT_INTERNAL_ERROR)
        }
        Err(e) => {
            eprintln!("error: cannot validate solver model ({e}); this is a bug");
            Err(EXIT_INTERNAL_ERROR)
        }
    }
}

/// Append solve-phase telemetry events (phase start, search counters, outcome).
fn record_solve_events(solver: &CdclSolver, outcome: Outcome, events: &mut Vec<Event>) {
    let mut seq = events.len() as u64;
    let mut push = |events: &mut Vec<Event>, kind: EventKind| {
        seq += 1;
        events.push(Event { seq, worker: 0, at_nanos: now_nanos(), kind });
    };
    push(events, EventKind::Phase { name: "root".into() });
    push(events, EventKind::SearchSummary {
        decisions: solver.decisions,
        propagations: solver.propagations,
        conflicts: solver.conflicts,
        restarts: solver.restarts,
    });
    push(events, EventKind::RunFinished { outcome });
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

    if file.extension().is_some_and(|e| e == "smt2" || e == "smt") {
        return run_smt_solve(&input, max_conflicts, events);
    }

    let cnf = match parse_dimacs(&input) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("error: invalid DIMACS in {}: {e}", file.display());
            return (EXIT_INTERNAL_ERROR, events);
        }
    };

    let mut solver = build_dimacs_solver(&cnf, proof_out.is_some());
    let budget = max_conflicts.unwrap_or(u64::MAX);
    let result = solver.solve(&[], budget);
    let proof_log = solver.take_proof_log();

    let outcome = match result {
        SolveResult::Sat(m) => match handle_sat_model(m, &cnf, proof_out) {
            Ok(o) => o,
            Err(code) => return (code, events),
        },
        SolveResult::Unsat => {
            println!("s UNSATISFIABLE");
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

    record_solve_events(&solver, outcome, &mut events);
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

    let mut seq = events.len() as u64;
    let mut push = |events: &mut Vec<Event>, kind: EventKind| {
        seq += 1;
        events.push(Event { seq, worker: 0, at_nanos: now_nanos(), kind });
    };
    push(&mut events, EventKind::Phase { name: "root".into() });

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
            export_lbd,
        } => {
            std::process::exit(run_serve(
                &file,
                port,
                workers as usize,
                seed,
                &peers,
                timeout_secs,
                bridge_ms,
                export_lbd,
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
            log::info!("solve: {} workers={} seed={}", file.display(), workers, seed);
            let _ = no_gpu;

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
