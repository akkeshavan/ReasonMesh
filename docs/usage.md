# ReasonMesh Usage

This document covers how to use ReasonMesh from the command line and as a Rust library. It assumes you have built the project with `cargo build --workspace`.

---

## Part I: The CLI

The `reasonmesh` binary has five subcommands: `solve`, `serve`, `replay`, `check-proof`, and `benchmark`. All follow the SAT competition exit-code convention: 10 = SAT, 20 = UNSAT, 0 = UNKNOWN or timeout, 3 = internal error.

---

### `reasonmesh solve`

Solve a single problem file. Accepts DIMACS CNF (`.cnf`) or SMT-LIB 2 (`.smt2`, `.smt`).

```
reasonmesh solve <file> [options]

Options:
  --workers N          Number of CPU worker threads (default: 1)
  --seed N             Random seed for VSIDS initialization (default: 1)
  --deterministic      Force single worker, fixed seed (overrides --workers)
  --max-conflicts N    Stop after N CDCL conflicts (default: unlimited)
  --trace PATH         Write a .rmtrace replay trace to PATH
  --proof-out PATH     Write a .rmproof certificate to PATH
  --no-gpu             Disable GPU workers (currently a no-op; GPU is a future milestone)
```

**DIMACS example:**

```sh
reasonmesh solve benchmarks/g1/php-5-4.cnf
# s UNSATISFIABLE
echo $?  # 20
```

**SMT-LIB 2 example:**

```sh
reasonmesh solve problem.smt2
# s SATISFIABLE
# (model
#   (define-fun x () (_ bv7 8))
# )
echo $?  # 10
```

**With multiple workers:**

Workers use seeds `seed`, `seed+1`, ..., `seed+N-1`. Different seeds mean different initial VSIDS scores, so each worker explores a different part of the search space. The first worker to reach a conclusion wins; the others are cancelled.

```sh
reasonmesh solve hard.cnf --workers 8 --seed 42
```

**With a conflict budget:**

Useful for running many problems with a bounded time budget without relying on wall-clock timeouts.

```sh
reasonmesh solve problem.cnf --max-conflicts 500000
```

**Saving a trace:**

```sh
reasonmesh solve problem.cnf --trace run.rmtrace
reasonmesh replay run.rmtrace
# trace: run.rmtrace solver=0.1.0 workers=1 deterministic=false
# events: 3
# ...
```

**Saving a proof certificate:**

For SAT instances, the certificate is a model file. For UNSAT instances, it is a DRUP derivation. Either can be verified with `check-proof`.

```sh
reasonmesh solve problem.cnf --proof-out result.rmproof
reasonmesh check-proof result.rmproof
# VALID SAT model (10 vars, 30 clauses)
```

---

### `reasonmesh serve`

Run as a cluster node. The node loads a DIMACS file, starts its own workers, and exchanges learned clauses with peer nodes over TCP.

All nodes must load the same problem file. They race independently toward a solution; the first node to find SAT or UNSAT prints the verdict and exits. Learned clauses discovered on any node propagate to all peers, shrinking the search space for the whole fleet.

```
reasonmesh serve <file> [options]

Options:
  --port N             TCP port to listen on (default: 9000)
  --workers N          Number of CDCL worker threads on this node (default: 4)
  --seed N             Base seed; workers get seed, seed+1, ..., seed+N-1 (default: 1)
  --peer host:port     Peer address (may be repeated)
  --timeout-secs N     Wall-clock timeout before reporting UNKNOWN (default: 300)
  --bridge-ms N        Idle sleep for the clause bridge thread in ms (default: 50)
  --export-lbd N       Only forward clauses with LBD ≤ N to remote peers (default: 6)
```

**Two-node example:**

Start node 2 first, then node 1. The `--peer` flag retries the connection for up to 30 seconds, so start order does not matter as long as all nodes are up within 30 seconds of each other.

```sh
# Terminal 1
reasonmesh serve problem.cnf --port 9000 --workers 4 --seed 1 --peer host2:9001

# Terminal 2
reasonmesh serve problem.cnf --port 9001 --workers 4 --seed 100 --peer host1:9000
```

The seeds are different on each node. This means no two workers in the cluster start from the same VSIDS configuration.

**Clause export tuning:**

`--export-lbd 6` means only clauses with a Literal Block Distance of 6 or less are forwarded to remote peers. Smaller values (e.g. 3) forward only the shortest, most general learned clauses — better for congested or high-latency networks. Setting it to 0 forwards everything, which can flood the network on large instances.

The `--bridge-ms` setting controls how long the bridge thread sleeps when both the export queue and the incoming network queue are empty. The default (50 ms) is a reasonable tradeoff; lower values reduce latency at the cost of one spinning thread on each node.

**Diagnostics:**

When the run completes, the node prints network statistics to stderr:

```
info: net_bus published=1432 bytes_out=287400 bytes_in=191200 incoming_evicted=3
```

If clauses were dropped because the bridge thread could not keep up with the local workers:

```
warn: export_bus dropped 17 clause(s) — bridge could not keep up;
      consider reducing --workers or increasing --bridge-ms
```

---

### `reasonmesh replay`

Read a `.rmtrace` file and print a summary.

```sh
reasonmesh replay run.rmtrace
```

Output includes the solver version, number of workers, whether the run was deterministic, the number of recorded events, and a formatted summary of search statistics (decisions, propagations, conflicts, restarts, outcome).

This is primarily useful for comparing runs: two traces from the same problem with different worker counts or seeds show exactly how the search differed.

---

### `reasonmesh check-proof`

Verify a `.rmproof` certificate.

```sh
reasonmesh check-proof result.rmproof
```

Exit codes: 10 = valid SAT proof, 20 = valid UNSAT proof, 0 = valid but ambiguous, 1 = invalid, 3 = could not parse.

For SAT proofs, verification re-checks the model against every clause in the problem independently of the solver. An incorrect model is impossible to pass: the checker shares no code with the CDCL engine.

For UNSAT proofs, the DRUP steps are stored in the file and will be checked by an external DRAT checker when that integration is complete. For now, `check-proof` parses and reports the step count but does not verify the derivation.

---

### `reasonmesh benchmark`

Run a suite of problems described by a TOML manifest.

```sh
reasonmesh benchmark experiments/g1-hard-sharing.toml
```

Results are printed as JSON to stdout. Redirect to a file for comparison:

```sh
reasonmesh benchmark experiments/g1-hard-sharing.toml > results/g1-hard-sharing.json
reasonmesh benchmark experiments/g1-hard-isolated.toml > results/g1-hard-isolated.json
```

**Manifest format:**

```toml
schema_version = 1
name = "g1-hard-sharing"
description = "4-worker portfolio with clause sharing, G1 gate benchmark"

[solver]
workers = 4
seed = 1
clause_sharing = true       # exchange learned clauses between workers
export_min_utility = 0.25   # only export clauses with LBD ≤ 3
import_min_utility = 0.143  # only apply clauses with LBD ≤ 6
max_conflicts_per_problem = 100000
timeout_secs = 300
deterministic = false

[output]
dir = "results/g1-hard-sharing"
trace = false               # set true to write .rmtrace per problem

[[baselines]]
name = "z3-1t"
binary = "z3"
args = ["-smt2", "-t:300000"]

[[problems]]
name = "php-5-4"
file = "benchmarks/g1/php-5-4.cnf"
expect = "unsat"

[[problems]]
name = "rand-250-1065"
file = "benchmarks/g1/rand-250-1065.cnf"
```

**Fields:**

`solver.clause_sharing = false` disables the in-process knowledge bus and runs an isolated portfolio (each worker is completely independent). This is the control condition for the G1 experiments: comparing `clause_sharing = true` vs `false` on the same problems measures whether asynchronous clause exchange actually helps.

`export_min_utility` and `import_min_utility` are expressed as utility values (`1 / (1 + LBD)`). LBD 3 corresponds to utility 0.25; LBD 6 corresponds to 0.143. Setting both to 0.0 shares everything with no filtering.

`baselines` runs an external solver on every problem with the same timeout. The binary is resolved through `PATH`. Output is parsed for `s SATISFIABLE` or `s UNSATISFIABLE` in the DIMACS competition format.

Problem paths are resolved relative to the manifest file, so manifests are relocatable.

---

## Part II: The distributed solver

The distributed mode separates solving from coordination. `rm-coordinator` accepts jobs over HTTP; `rm-node` workers poll for tasks, solve them, and report back.

---

### Starting the coordinator

```sh
rm-coordinator --addr 0.0.0.0:7700 --lease-ttl-secs 120 --worker-timeout-secs 300
```

Options:
- `--addr` — bind address (default: `0.0.0.0:7700`)
- `--lease-ttl-secs` — how long a worker has to solve a task before it is reassigned (default: 120)
- `--worker-timeout-secs` — how long before an unresponsive worker is removed from the registry (default: 300)

---

### Starting worker nodes

```sh
rm-node --coordinator http://leader:7700 --concurrency 8 --worker-id 1
```

Options:
- `--coordinator` — coordinator URL (default: `http://127.0.0.1:7700`)
- `--concurrency` — number of solve slots on this node (default: 4)
- `--worker-id` — integer ID reported to coordinator (default: OS process ID)
- `--long-poll-ms` — how long each work request blocks waiting for a task (default: 25000)
- `--retry-ms` — back-off between retries when the coordinator is unreachable (default: 2000)

Worker IDs must be unique across the cluster. When running multiple workers on the same machine, either use distinct process IDs (the default) or assign explicit IDs.

---

### Submitting a proof farm (Regime B)

Post a list of independent SMT-LIB 2 scripts. The coordinator creates one task per script; any worker can claim any task.

```sh
curl -X POST http://localhost:7700/v1/batch \
  -H 'Content-Type: application/json' \
  -d '{
    "scripts": [
      "(set-logic QF_BV)(declare-const x (_ BitVec 8))(assert (bvult x (_ bv10 8)))(check-sat)",
      "(set-logic QF_BV)(declare-const x (_ BitVec 4))(assert (= x #b0000))(assert (= x #b1111))(check-sat)"
    ],
    "max_conflicts": 100000
  }'
# {"job_id": "3fa85f64-..."}
```

Poll for results:

```sh
curl http://localhost:7700/v1/batch/3fa85f64-...
# {"job_id":"...","pending":0,"results":[{"index":0,"code":0,"model":"(x (_ bv7 8))"},{"index":1,"code":1,"model":""}]}
```

Result codes: 0 = SAT, 1 = UNSAT, 2 = UNKNOWN.

---

### Submitting a cube-and-conquer job (Regime A)

Post a single SMT-LIB 2 script. The coordinator starts with one task covering the full formula. Workers that exhaust their conflict budget report a split; the coordinator fans out new tasks.

```sh
curl -X POST http://localhost:7700/v1/cube \
  -H 'Content-Type: application/json' \
  -d '{
    "script": "(set-logic QF_BV)(declare-const a (_ BitVec 32))...(check-sat)",
    "max_conflicts_per_cube": 50000
  }'
# {"job_id": "7c9e6679-..."}
```

Poll for the verdict:

```sh
curl http://localhost:7700/v1/cube/7c9e6679-...
# {"job_id":"...","done":false,"status":"open","open_nodes":4,"closed_nodes":2}
# ... later ...
# {"job_id":"...","done":true,"status":"unsat"}
```

---

### Coordinator API reference

| Method | Path | Description |
|---|---|---|
| POST | `/v1/batch` | Submit proof-farm batch |
| GET | `/v1/batch/:job_id` | Poll batch results |
| POST | `/v1/cube` | Submit cube-and-conquer job |
| GET | `/v1/cube/:job_id` | Poll cube verdict |
| GET | `/v1/work` | Worker long-poll for a task |
| POST | `/v1/work/:task_id/result` | Report SAT/UNSAT/split |
| POST | `/v1/work/:task_id/renew` | Extend task lease |
| POST | `/v1/heartbeat` | Worker liveness ping |
| GET | `/v1/status` | Coordinator statistics |

---

## Part III: The Rust library

### Adding the dependency

```toml
[dependencies]
rm-api = { path = "path/to/ReasonMesh/crates/rm-api" }
```

Or, for direct access to the lower-level SMT facade:

```toml
rm-smt = { path = "path/to/ReasonMesh/crates/rm-smt" }
```

---

### One-shot SMT-LIB 2 text interface

The simplest way to call the solver is to provide a script as a string:

```rust
use rm_api::solve_smtlib;

let result = solve_smtlib(
    "(set-logic QF_BV)
     (declare-const x (_ BitVec 8))
     (assert (bvult x #x0a))
     (check-sat)"
);

match result {
    rm_api::solver::SatResult::Sat(model) => {
        let (bits, width) = model.get_bitvec("x").unwrap();
        println!("x = {} ({}b)", bits, width);
    }
    rm_api::solver::SatResult::Unsat => println!("unsat"),
    rm_api::solver::SatResult::Unknown(reason) => println!("unknown: {reason}"),
}
```

With a conflict budget:

```rust
use rm_api::solve_smtlib_with_budget;

let result = solve_smtlib_with_budget(script, 100_000);
```

---

### Programmatic API

Build formulas using `Context` and `Expr`, then check them with `Solver`. This avoids writing SMT-LIB text by hand.

```rust
use rm_api::{Context, Solver, solver::SatResult};

let ctx = Context::new();
let mut solver = Solver::new(&ctx);

// Build expressions
let x = ctx.bitvec_const("x", 32);
let y = ctx.bitvec_const("y", 32);
let sum = x.bvadd(&y);
let target = ctx.bitvec_val(0, 32);

// Assert constraints
solver.assert(&sum.eq(&target));     // x + y = 0
solver.assert(&x.bvugt(&target));   // x > 0

match solver.check() {
    SatResult::Sat(model) => {
        let (x_val, _) = model.get_bitvec("x").unwrap();
        let (y_val, _) = model.get_bitvec("y").unwrap();
        println!("x={}, y={}", x_val, y_val);
    }
    SatResult::Unsat => println!("impossible"),
    SatResult::Unknown(r) => println!("gave up: {r}"),
}
```

**Integer constraints:**

```rust
let ctx = Context::new();
let mut solver = Solver::new(&ctx);
let x = ctx.int_const("x");
let y = ctx.int_const("y");
let five = ctx.int_val(5);

solver.assert(&x.sub(&y).le(&five));   // x - y ≤ 5
solver.assert(&y.sub(&x).le(&five));   // y - x ≤ 5
assert!(solver.check().is_sat());
```

**Boolean logic:**

```rust
let ctx = Context::new();
let mut solver = Solver::new(&ctx);
let a = ctx.bool_const("a");
let b = ctx.bool_const("b");

solver.assert(&a.or(&b));              // a ∨ b
solver.assert(&ctx.not(&a));           // ¬a
assert!(solver.check().is_sat());      // b must be true
```

---

### Push and pop

`push()` saves the current assertion stack. `pop()` restores it. This lets you explore multiple branches without rebuilding the solver.

```rust
let ctx = Context::new();
let mut solver = Solver::new(&ctx);
let x = ctx.bitvec_const("x", 8);

solver.assert(&x.bvult(&ctx.bitvec_val(100, 8)));  // x < 100

solver.push();
solver.assert(&x.bvult(&ctx.bitvec_val(0, 8)));    // additionally: x < 0
assert!(solver.check().is_unsat());                 // impossible

solver.pop();
assert!(solver.check().is_sat());                   // x < 100 alone is fine
```

---

### Parallel check with multiple workers

Race N independent solver instances. The first conclusive result wins.

```rust
use rm_api::{Context, Solver};
use rm_api::solver::SolverConfig;
use std::time::Duration;

let ctx = Context::new();
let mut solver = Solver::with_config(
    &ctx,
    SolverConfig {
        num_workers: 8,
        max_conflicts: 500_000,
        timeout: Some(Duration::from_secs(60)),
    },
);

let x = ctx.bitvec_const("x", 64);
solver.assert(&x.bvult(&ctx.bitvec_val(42, 64)));
let result = solver.check();
```

The workers do not currently share learned clauses between each other (that requires routing through `WorkerPool` with CNF extraction, which is a future API milestone). The benefit is that occasional runs escape pathological decision sequences faster when one of the N workers finds the solution first.

---

### Solving a batch of independent problems (proof farm)

When you have many independent formulas — for example, separate Lean verification conditions — solve them concurrently:

```rust
use rm_api::{Job, SolverPool};
use rm_api::solver::SolverConfig;

let pool = SolverPool::new(SolverConfig {
    num_workers: 16,  // total concurrent workers
    ..Default::default()
});

let jobs = vec![
    Job::new("(set-logic QF_BV) ... (check-sat)").with_label("vc_1"),
    Job::new("(set-logic QF_IDL) ... (check-sat)").with_label("vc_2"),
    Job::new("(set-logic QF_UF) ... (check-sat)").with_label("vc_3"),
];

let results = pool.run_all(jobs);

for r in &results {
    println!("{}: {:?}", r.label.as_deref().unwrap_or("?"), r.result);
}
```

Results are returned in submission order regardless of which job finishes first.

---

### Working with models

`Model::get_bitvec(name)` returns `Option<(u64, u32)>` — the value and the bit width. `Model::get_bool(name)` returns `Option<bool>`. `Model::get_int(name)` returns `Option<i64>`.

```rust
let (bits, width) = model.get_bitvec("x").unwrap();
println!("x = {} ({}b)", bits, width);  // e.g. x = 42 (32b)

// As hex:
println!("x = {:#0width$x}", bits, width = (width as usize / 4) + 2);
```

---

### Using rm-smt directly

`rm-smt` is slightly lower-level than `rm-api` and gives you access to the full `SmtResult` including the `BvModel` for bit-vector problems:

```rust
use rm_smt::{SmtSolver, SmtStatus, SmtError};

let solver = SmtSolver::parse(script)?;
match solver.solve(100_000) {
    Ok(result) => match result.status {
        SmtStatus::Sat => {
            for (name, value) in &result.values {
                println!("{name} = {value}");
            }
        }
        SmtStatus::Unsat => {}
        SmtStatus::Unknown => {}
    },
    Err(SmtError::UnsupportedLogic(logic)) => {
        eprintln!("logic {logic} not supported");
    }
    Err(SmtError::EmptyProblem) => {
        // Script has no assertions — trivially SAT
    }
    Err(e) => eprintln!("solver error: {e}"),
}
```

`result.values` is a `Vec<(String, String)>` where the second string is the value in SMT-LIB 2 notation (e.g. `(_ bv42 32)` for a 32-bit value of 42).

---

### Supported SMT-LIB 2 logics

| Logic | Path | Notes |
|---|---|---|
| `QF_BV` | Tseitin bit-blasting + CDCL | Full model output |
| `QF_IDL` | Bellman-Ford difference-logic | Integer model output |
| `QF_RDL` | Bellman-Ford difference-logic | Rational literals treated as integers |
| `QF_UF` | E-graph + congruence closure | Model: term → representative name |
| `QF_UFIDL` | CDCL(T): EUF + DL combined | No model output yet |
| `(none)` | Defaults to `QF_BV` | — |

All other logics return `SmtError::UnsupportedLogic`. Non-quantified linear arithmetic (`QF_LIA`, `QF_NIA`, `QF_NRA`, etc.) is not yet supported.

---

### Supported bit-vector operations (QF_BV)

The `Expr` API supports all common bit-vector operations:

**Arithmetic:** `bvadd`, `bvsub`, `bvmul`, `bvneg`

**Bitwise:** `bvand`, `bvor`, `bvxor`, `bvnot`

**Comparisons:** `bvult` (<, unsigned), `bvule` (≤, unsigned), `bvslt` (<, signed), `bvsle` (≤, signed)

**Shifts:** `bvshl`, `bvlshr` (logical right), `bvashr` (arithmetic right)

**Structural:** `concat`, `extract(hi, lo)`, `zero_extend(n)`, `sign_extend(n)`

In SMT-LIB 2 text, all standard QF_BV operations and literals (`#x...`, `#b...`, `(_ bv... ...)`) are supported.

---

## Environment and logging

Set `RUST_LOG` to control log verbosity:

```sh
RUST_LOG=info reasonmesh solve problem.cnf       # show progress
RUST_LOG=debug rm-node --coordinator http://...  # show task lifecycle
RUST_LOG=warn  rm-coordinator                    # warnings only
```

Available log levels: `error`, `warn`, `info`, `debug`, `trace`.

For `rm-node`, `debug` level shows each task being received, the solve outcome, and lease renewal events. For `rm-coordinator`, `info` shows job submissions and completions; `debug` shows each task state transition.
