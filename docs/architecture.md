# ReasonMesh Architecture

This document covers how ReasonMesh is structured: what each crate does, how the pieces connect, and where the interesting design decisions live. It is written for someone who wants to contribute or who needs to understand what is actually happening rather than what the system aspires to be.

The system has three operating modes that share a large chunk of code:

- **Single-process solve** — one `reasonmesh solve` invocation, one problem, one or more worker threads sharing an in-memory bus.
- **Multi-node cluster** — multiple `reasonmesh serve` invocations on different machines, each running its own workers and exchanging learned clauses over TCP.
- **Distributed coordinator** — a long-running `rm-coordinator` server accepting jobs over HTTP, with `rm-node` worker processes polling for tasks. This mode handles both independent proof farms and cube-and-conquer decompositions.

---

## 1. Crate layout

```
reasonmesh-cli     -- the "reasonmesh" binary
rm-api             -- programmatic API (Rust embedding, C FFI, Lean 4 bridge)
rm-smt             -- SMT-LIB 2 facade: dispatches to theory solvers
rm-sat             -- CDCL engine
rm-theory-bv       -- bit-vector theory (Tseitin blasting)
rm-theory-euf      -- equality + uninterpreted functions (e-graph + CC)
rm-theory-arith    -- difference-logic arithmetic
rm-ir              -- bitvector IR and circuit builder
rm-syntax          -- SMT-LIB 2 lexer and S-expression parser
rm-akx             -- AKX protocol types and import gate
rm-bus             -- knowledge bus implementations (in-process, TCP)
rm-worker          -- multi-thread CDCL worker pool
rm-scheduler       -- cube partition tree and lease management
rm-orchestrator    -- local orchestrator (single-node parallel solving)
rm-coordinator     -- distributed HTTP coordinator
rm-node            -- distributed solver worker binary
rm-proof           -- proof certificate format (.rmproof) and verification
rm-telemetry       -- structured trace files (.rmtrace)
rm-bench           -- benchmark manifest runner
rm-gpu             -- GPU worker stub (future milestone)
rm-gpu-cuda        -- CUDA backend stub (future milestone)
```

The dependency graph runs roughly bottom-up: `rm-syntax` has no internal dependencies; `rm-sat` depends on `rm-akx` for literal representation; `rm-smt` depends on the theory crates; `rm-worker` depends on `rm-sat`, `rm-akx`, and `rm-bus`. The CLI and API sit at the top.

---

## 2. The CDCL engine (rm-sat)

`CdclSolver` in `crates/rm-sat/src/cdcl.rs` is the core search engine. It implements:

- **Two-watched-literal BCP.** Each clause watches two of its literals. When a watched literal becomes false, the watch is moved to another unassigned or true literal, or unit propagation fires. This is the MiniSAT convention.
- **1-UIP conflict analysis.** On conflict, the solver resolves the conflict clause backwards through the implication graph until only one variable from the current decision level remains (the unique implication point). The resulting clause is learned and added to the database.
- **Non-chronological backjumping.** After learning a clause, the solver jumps back to the second-highest decision level in the learned clause, not necessarily the previous level.
- **VSIDS branching.** Variable activity scores are bumped on each conflict for all variables in the conflict clause. The score of every variable decays by a configurable factor each conflict, so recent activity dominates. The variable with the highest score that is currently unassigned is selected next.
- **Luby restarts.** The solver restarts its search (undoing all decisions and keeping only learned clauses) on a Luby sequence schedule. This helps escape pathological decision sequences.
- **LBD-based clause deletion.** Learned clauses are tagged with their Literal Block Distance — roughly, how many decision levels appear in the clause. Clauses with high LBD are deleted during periodic reduction rounds.
- **DRUP proof logging.** When `enable_proof_logging()` is called before solving, the solver records every learned clause and deletion in DRUP format. The log is extracted after solving with `take_proof_log()`.

The solver exposes a `solve(&assumptions, max_conflicts)` method. Assumptions are hypothesized literals that hold for this call only; the solver never backtracks below the assumption decision level, so assumptions survive restarts. `max_conflicts = u64::MAX` means unlimited.

For multi-worker operation, the solver is wrapped in `CdclReasoner` (in `rm-sat/src/reasoner.rs`), which adds an import/export interface. Between each `step()` call, the reasoner exports newly learned clauses to the bus and polls for incoming knowledge from other workers.

---

## 3. Theory solvers

### QF_BV — bit-vector theory (rm-theory-bv)

The entry point is `BvSolver`. It takes a parsed SMT-LIB `Script`, extracts all `declare-const` statements and `assert` expressions, and converts the formula to SAT via Tseitin transformation (in `crates/rm-theory-bv/src/tseitin.rs`).

The conversion walks the expression tree. Boolean connectives become CNF clauses directly. Bit-vector operations are expanded into circuits of 1-bit gates (AND, OR, XOR, etc.). Each gate output gets a fresh Boolean variable. The Tseitin encoding adds clauses that enforce `gate_output ⟺ gate_function(inputs)`, which preserves equisatisfiability with linear clause count.

Once the formula is in CNF, `CdclSolver` handles the search. On SAT, the model assigns values to each gate output; the BV model extracts per-constant values by reading the assignments of the bit variables that correspond to each declared constant.

There is also a differential encoding (`crates/rm-theory-bv/src/differential.rs`) that is used when incremental solving is needed — it avoids re-encoding unchanged parts of the formula.

### QF_IDL / QF_RDL — difference logic (rm-theory-arith)

Difference-logic formulas constrain integer or rational variables only through inequalities of the form `x - y ≤ k`. The solver in `crates/rm-theory-arith/src/diff.rs` handles these without going through SAT: it builds a constraint graph where each variable is a node and each assertion `x - y ≤ k` is a directed edge from `y` to `x` with weight `k`. Satisfiability is decided by checking for negative cycles using a Bellman-Ford variant. When a negative cycle is found, the formula is UNSAT.

The SMT facade (`rm-smt/src/dl.rs`) parses the SMT-LIB script, extracts difference-logic assertions, and calls the diff-logic solver. No CDCL is involved for pure QF_IDL/QF_RDL.

### QF_UF — uninterpreted functions (rm-theory-euf)

The e-graph (`EGraph` in `crates/rm-theory-euf/src/egraph.rs`) stores ground terms as DAG nodes. Each term is identified by an `ENodeId`. Congruence closure (`CongruenceClosure` in `crates/rm-theory-euf/src/cc.rs`) maintains equivalence classes: when two terms are asserted equal, their classes are merged, and all function applications of the form `f(a)` and `f(b)` where `a` and `b` are in the same class are also merged (the congruence rule). If two terms are ever asserted both equal and distinct, the formula is UNSAT.

The SMT facade (`rm-smt/src/uf.rs`) builds the e-graph from the script's declarations, interns all sub-terms from assertions into the graph, then processes `(assert (= a b))` and `(assert (not (= a b)))` constraints through the CC. The model maps each constant to its e-class representative.

### QF_UFIDL — combined (rm-smt/cdclt.rs)

For formulas mixing equality, uninterpreted functions, and difference-logic arithmetic, the facade uses a simplified CDCL(T) approach: the CDCL engine handles the Boolean structure, and theory lemmas from the EUF and DL modules are fed back to the engine as learned clauses when the theory detects inconsistency. This is the most complex of the four theory paths.

---

## 4. The SMT facade (rm-smt)

`SmtSolver::parse(text)` stores the raw SMT-LIB 2 text without doing any parsing. `SmtSolver::solve(max_conflicts)` then:

1. Scans the text for a `(set-logic ...)` declaration to decide which theory path to take.
2. Dispatches to `BvSolver` for QF_BV, `solve_qf_idl` for QF_IDL/QF_RDL, `solve_qf_uf` for QF_UF, or `solve_qf_ufidl` for QF_UFIDL.
3. Returns `SmtResult { status, model, values }` where `values` is a `Vec<(name, value_string)>` ready for `get-model` output.

Unsupported logics return `SmtError::UnsupportedLogic`. An empty problem (no assertions and no declarations) returns `SmtError::EmptyProblem`.

The `max_conflicts` parameter passes through to the CDCL engine for QF_BV and QF_UFIDL. For QF_IDL and QF_UF, which don't use CDCL, the parameter is accepted but has no effect.

---

## 5. The AKX protocol (rm-akx)

AKX — Asynchronous Knowledge Exchange — is the protocol that lets multiple reasoning threads share what they have learned. The core types are in `crates/rm-akx/`.

A `KnowledgeObject` is a tagged piece of knowledge. The important kinds are:

- `ClauseKnowledge`: a learned CNF clause, with its LBD and a `Scope` indicating how broadly it can be shared.
- `TheoryLemma`: a theory-derived fact (e.g., a congruence from EUF or a derived bound from DL).
- `CubeKnowledge`: a cube assertion for cube-and-conquer workflows.
- `HeuristicHint`: a variable polarity or branching suggestion.

`Scope` controls routing: `Scope::Process` stays on the local bus; `Scope::Global` is eligible for export to remote nodes.

`TrustLevel` distinguishes axioms (certain consequences of the original formula), derived facts (learned during search, sound by proof), and heuristic hints (plausible but not guaranteed).

The `ImportGate` enforces the assumption-scoped import predicate: a worker operating under assumptions `A` may only apply a learned clause if all literals in that clause are either present in the original formula or are consequences of assumptions consistent with `A`. This prevents unsound cross-contamination when workers are solving different cubes.

`ExportPolicy` and `ImportPolicy` carry utility thresholds. A worker will not export clauses whose estimated utility (computed as `1 / (1 + LBD)`) falls below `export_min_utility`, and will discard imported clauses below `import_min_utility`. The G1 gate experiments in `experiments/` measure how these thresholds affect parallel speedup.

---

## 6. The knowledge bus (rm-bus)

`KnowledgeBus` is a trait with three methods: `publish(scope, batch)`, `poll(budget)`, and `metrics()`.

**InprocBus** (`crates/rm-bus/src/inproc.rs`) is the in-memory implementation. It maintains a bounded queue per scope. When the queue is full and a new item arrives with higher utility than the lowest-utility item in the queue, the lowest-utility item is evicted to make room. If the new item has lower utility than everything in the queue, `BusError::BufferFull` is returned instead. Items are deduplicated by `canonical_key` before insertion.

**NetBus** (`crates/rm-bus/src/net.rs`) is the TCP implementation used in cluster mode. It listens on a local port and accepts connections from peer nodes. Serialization uses `postcard` (a compact binary format). The NetBus has its own bounded buffers and tracks bytes sent and received for diagnostics.

**BroadcastBus** (in `crates/reasonmesh-cli/src/main.rs`) is a dual-queue adapter used when a node operates in both local and cluster mode simultaneously. It maintains two `InprocBus` instances: one for local workers and one for export. Every `publish` call writes to the export bus and the local bus independently, using per-object publishing so each clause is evaluated for eviction on its own merits. The bridge thread drains the export bus to the network and writes incoming network clauses to the local bus. Keeping them separate prevents the bridge from consuming clauses that local workers need.

---

## 7. The worker pool (rm-worker)

`WorkerPool` manages N threads, each running a `CdclReasoner`. The pool is constructed with a `Problem` (num_vars + clause list), a `WorkerConfig`, and a `KnowledgeBus`. Calling `pool.run(cubes, deadline)` starts all threads and blocks until one reports a conclusive result or the deadline expires.

Worker `i` is seeded with `config.seed + i`. With four workers and seeds 1, 2, 3, 4, each worker has a different initial VSIDS state, so they explore different parts of the search space (portfolio diversification).

Inside each worker thread, the loop is:

1. Call `reasoner.step(step_budget)`. This runs `step_budget` conflicts worth of CDCL search.
2. Export newly learned clauses to the bus (filtered by `ExportPolicy`).
3. Poll the bus for clauses learned by other workers.
4. Filter incoming clauses through the `ImportGate` and apply the ones that pass.
5. If the step returned `SatCandidate` or `UnsatLocal`, report the outcome and stop.

When a worker finds SAT, it independently validates the model against the original formula before reporting. This is a deliberate cross-check that shares nothing with solver internals — a model that fails validation is a bug, reported as `EXIT_INTERNAL_ERROR`. When a worker finds UNSAT, it stops. The shared `Arc<AtomicBool> shutdown` flag is set when any worker reports SAT, so the others exit without waiting for their step to complete.

---

## 8. Multi-node cluster mode

The CLI's `serve` subcommand wires the local worker pool to a TCP network:

1. A `NetBus` is created and bound to a local port.
2. A `BroadcastBus` wraps a local `InprocBus` and the export side.
3. The `WorkerPool` uses the `BroadcastBus` so worker-to-worker sharing is still in-memory.
4. A bridge thread runs in the background and does two things in a tight loop:
   - Drains the export bus and publishes the batch to the `NetBus`.
   - Polls the `NetBus` for incoming clauses and injects them into the local bus.
5. The bridge only sleeps when both directions are idle (`--bridge-ms` controls the idle sleep, default 50 ms).

Peers are specified with `--peer host:port` (may be repeated). Connections are retried for up to 30 seconds, so all nodes can be started concurrently without a strict ordering requirement.

Only clauses with LBD ≤ `--export-lbd` are eligible for network export. The default is 6, meaning only relatively short and well-structured clauses cross the network. Setting it to 0 exports everything, which may flood the network on hard instances.

---

## 9. The distributed coordinator (rm-coordinator)

The coordinator is an Axum HTTP server. All mutable state lives in a `parking_lot::Mutex<CoordinatorState>`. A `tokio::sync::Semaphore` tracks the number of tasks currently in the queue; `rm-node` workers acquire a semaphore permit as part of the long-poll, which means they block cheaply without holding any lock until a task is ready.

### State machine

`CoordinatorState` contains:
- `batch_jobs: HashMap<JobId, BatchJob>` — proof-farm batches (Regime B).
- `cube_jobs: HashMap<JobId, CubeJob>` — cube-and-conquer jobs (Regime A).
- `task_queue: VecDeque<Task>` — tasks not yet claimed.
- `in_flight: HashMap<TaskId, InFlightTask>` — tasks held by a worker under a lease.
- `workers: HashMap<u32, WorkerInfo>` — registered workers and their last heartbeat.

### Regime B: proof farm (BatchJob)

When a client posts to `/v1/batch`, the coordinator creates one `Task` per script and pushes them all to `task_queue`. `BatchJob` tracks how many tasks are still pending; when that count reaches zero, the job is complete. Any worker can claim any task.

### Regime A: cube-and-conquer (CubeJob)

When a client posts to `/v1/cube`, the coordinator creates a root `CubeNode` and pushes one initial task. The `CubeJob` stores the base script (the formula without `(check-sat)`) and a tree of `CubeNode`s.

When a worker reports `code=2` (UNKNOWN) and includes a `split` array, the coordinator:
1. Marks the current node as split.
2. Creates two child `CubeNode`s, each with one of the split assertions appended to the inherited assertions.
3. Pushes two new tasks with scripts derived by concatenating the base script with the node's accumulated assertions.
4. Adds two semaphore permits.

When a worker reports `code=1` (UNSAT), the node is marked closed. The coordinator checks whether all leaves of the cube tree are closed: if so, the original formula is UNSAT. When a worker reports `code=0` (SAT), the formula is immediately SAT and the job finishes.

### Long-polling

`GET /v1/work?worker_id=N&long_poll_ms=M` acquires a semaphore permit (blocking for up to `M` ms), then pops a task from the queue. If the timeout expires before a permit is available, it returns HTTP 204 and the worker loops. This design means workers never spin-wait; the OS scheduler parks them until a task is available.

### Leases and reaping

Each in-flight task has a TTL. If a worker crashes or stops renewing, a background task running every 5 seconds reaps expired in-flight tasks by pushing them back onto the queue and adding a semaphore permit. Workers extend their leases by posting to `/v1/work/:task_id/renew`. Dead workers (no heartbeat for the configured timeout) are removed from the registry.

---

## 10. The distributed worker (rm-node)

`rm-node` runs one or more concurrent solve loops (controlled by `--concurrency`). Each loop:

1. Long-polls `GET /v1/work` with `?worker_id=N&long_poll_ms=25000`.
2. On receiving a task, spawns a lease renewal task in the background (`POST /v1/work/:id/renew` every `lease_ttl / 2`).
3. Runs `solve_with_lookahead(script, max_conflicts)` on a blocking thread (not in the async executor).
4. Cancels the lease renewal task.
5. Posts the result to `POST /v1/work/:task_id/result`.

### Look-ahead for cube splitting

When the solver returns UNKNOWN (budget exhausted without a conclusion), the worker runs the look-ahead heuristic in `crates/rm-node/src/lookahead.rs`:

1. **Parse declarations.** The script is tokenized with `rm_syntax::lex` and `parse_program`. All `declare-const` and nullary `declare-fun` statements are collected.
2. **Score by occurrence.** For each variable name, the number of whole-token occurrences in the assertion text is counted. Variables that appear more often are more central to the search.
3. **Probe top-4 candidates.** For each of the four most-occurring variables, two branches are constructed (positive assertion, negative assertion). Each branch is run with a small conflict budget (`max_conflicts / 8`, clamped to [200, 2000]). Branches score 100 for UNSAT (the branch is eliminated), 10 for SAT (the branch is feasible), and 5 for UNKNOWN (too hard to probe).
4. **Pick the winner.** The variable with the highest combined branch score is chosen for the split. A tie is broken by occurrence count.
5. **Generate assertions.** For Bool: `(assert x)` vs `(assert (not x))`. For `(_ BitVec n)`: `(assert (bvult x (_ bv{mid} {n})))` vs the negation, where `mid = 1 << (n-1)` (the midpoint). For Int: `(assert (<= x 0))` vs `(assert (> x 0))`.

The split is reported as two `(assert ...)` strings. The coordinator appends each to the base script to form the child cube tasks.

The probe budget is zero when `max_conflicts = 0` (the solver runs without a limit and should never return UNKNOWN), so probing is skipped in that case.

---

## 11. The programmatic API (rm-api)

The API is designed for Rust programs that want to use ReasonMesh as a library rather than shelling out to the CLI.

**Context** is a factory for expressions. It holds no mutable state; the same context can be shared across solver instances. Constants are created with `ctx.bool_const("x")`, `ctx.int_const("y")`, `ctx.bitvec_const("z", 32)`. Literals are `ctx.bool_val(true)`, `ctx.int_val(5)`, `ctx.bitvec_val(42, 8)`.

**Expr** wraps an `Arc<ExprNode>` so cloning is O(1) and the expression tree is naturally shared. Building an expression allocates one node per operation. `emit_smtlib` (in `crates/rm-api/src/emit.rs`) walks the expression tree and serializes it to SMT-LIB 2 text, which is then passed to `SmtSolver`. The roundtrip through text is deliberate: it keeps the API implementation straightforward and ensures the programmatic path exercises exactly the same code as the CLI path.

**Solver** is an incremental session. `assert(&expr)` appends a formula. `push()` saves the current assertion count; `pop()` restores it. `check()` emits the current assertion stack as SMT-LIB, calls the solver, and returns `SatResult`. `check_assumptions(&[expr])` is a non-persistent variant: the assumptions are added for this one call and discarded afterward.

`SolverConfig::num_workers` races N independent solver instances on each `check()` call. This is not a full portfolio with clause sharing (the API solver doesn't extract CNF and feed it to `WorkerPool`); the benefit is fault tolerance and that different seedings occasionally lead one instance to finish while the others are stuck. Full clause-sharing portfolio for the API is a future milestone.

**SolverPool** is the Regime B interface. Submit independent jobs as `Vec<Job>` (each job is a raw SMT-LIB 2 string plus an optional label), receive `Vec<JobResult>` back in submission order. This is what the Lean 4 bridge uses when verifying a batch of subgoals concurrently.

**C FFI** (`crates/rm-api/src/ffi.rs`) exposes the same functionality through C-compatible `extern "C"` functions. The entry points follow the pattern `rm_ctx_new()`, `rm_ctx_bitvec_const()`, `rm_solver_new()`, `rm_solver_assert()`, `rm_solver_check()`, etc. The FFI is what the Lean 4 `rm_api` Lake package calls at elaboration time.

---

## 12. Proof format (.rmproof)

A `.rmproof` file is UTF-8 text in a DIMACS-adjacent format:

```
c reasonmesh proof v0.2
p cnf <num_vars> <num_clauses>
<clause lines>
s SAT
v <lit1> <lit2> ... 0
```

For UNSAT:
```
s UNSAT
d <lit1> <lit2> ... 0
d ...
d 0
```

`c` lines are comments. The `p cnf` header records the problem. `v` lines follow the DIMACS SAT competition convention: positive literal means the variable is true, negative means false, and `0` terminates the line. Multiple `v` lines are concatenated.

SAT proof verification (`ProofFile::verify()`) re-checks the model against every clause in the problem independently of the solver. This is the guarantee that matters: even if the solver has a bug in its assignment tracking, an incorrect model will fail here.

UNSAT proof verification via DRUP is declared as "not yet implemented." The DRUP steps are parsed and stored, but the checker that walks the implication chain is a future milestone.

---

## 13. Telemetry (.rmtrace)

When `--trace path.rmtrace` is passed to `reasonmesh solve`, the CLI records a structured trace of the run. `TraceWriter` writes a `RunMeta` header (solver version, num_workers, deterministic flag, command line) followed by a sequence of `Event` records:

- `EventKind::Phase { name }` — marks the start of a named phase.
- `EventKind::SearchSummary { decisions, propagations, conflicts, restarts }` — solver counters at run end.
- `EventKind::RunFinished { outcome }` — final verdict.

`reasonmesh replay path.rmtrace` reads the file back and prints the summary via `TraceReader::summarize().render()`. The trace format is designed for future analysis: later milestones will record per-conflict information for portfolio comparison.

---

## 14. Benchmark manifests

A manifest is a TOML file with the following structure:

```toml
schema_version = 1
name = "g1-hard-sharing"
description = "..."

[solver]
workers = 4
seed = 1
clause_sharing = true
export_min_utility = 0.25   # share clauses with LBD ≤ 3
import_min_utility = 0.143  # apply clauses with LBD ≤ 6
max_conflicts_per_problem = 100000
timeout_secs = 300

[output]
dir = "results/g1-hard-sharing"
trace = false

[[baselines]]
name = "z3-1t"
binary = "z3"
args = ["-smt2", "-t:300000"]

[[problems]]
name = "php-5-4"
file = "benchmarks/g1/php-5-4.cnf"
expect = "unsat"
```

`run_manifest` runs each problem against ReasonMesh and any configured baselines, respects the per-problem timeout, checks the verdict against `expect` if provided, and emits a JSON result file with per-problem times and verdicts. The utility thresholds (`export_min_utility`, `import_min_utility`) correspond directly to the `ExportPolicy` and `ImportPolicy` passed to `WorkerPool` — these are the primary experimental variables in the G1 gate experiments.

---

## 15. Design decisions worth noting

**Why text roundtrip in rm-api?** The Expr tree serializes to SMT-LIB 2 text, which is then re-parsed by `SmtSolver`. This is slower than passing the expression tree directly, but it means the API and CLI exercise the same code path, and any fix to the parser benefits both. The performance cost is measurable only on very small problems, where the solver time is negligible anyway.

**Why BroadcastBus over a single shared bus?** With a single bus, the bridge thread and local workers compete to consume clauses. A clause exported to a remote peer should not be removed from the local pool before local workers have a chance to import it. The dual-queue design gives local workers exclusive access to the local bus and gives the bridge exclusive access to the export bus.

**Why semaphore-based long-polling?** The alternative — polling the task queue in a loop with a sleep — either wastes CPU or adds latency. The semaphore approach is exact: the number of permits equals the number of tasks in the queue, so a worker acquiring a permit is guaranteed to find a task. No spurious wakeups, no overshoot.

**Why utility = 1/(1+LBD)?** LBD is unbounded; utility needs to be in [0,1] for comparison. The mapping `1/(1+LBD)` gives utility 1.0 for unit clauses (LBD=0, trivially important), 0.5 for LBD=1, 0.25 for LBD=3, and so on. The eviction policy always keeps the highest-utility items, so low-LBD (high-quality) clauses are protected. The G1 experiments use `export_min_utility = 0.25` (LBD ≤ 3) and `import_min_utility = 0.143` (LBD ≤ 6) as the default thresholds.

**Why not share clause databases directly between threads?** The per-worker clause database approach (each worker has its own copy of the original clauses plus its own learned-clause database) avoids synchronization on the hot path. Synchronization only happens on the bus, which is write-seldom and read in bulk. The tradeoff is memory: N workers use N copies of the original formula. For the problems in the benchmark set this is acceptable; for very large instances it becomes a concern.
