# ReasonMesh

ReasonMesh is a parallel SAT/SMT solver written in Rust. It implements CDCL with a shared learned-clause database, an asynchronous inter-worker knowledge bus (AKX), cube-and-conquer decomposition, and a TCP cluster transport for distributing cubes across machines.

**Supported logics:** QF\_BV (bit-blasting), QF\_IDL/QF\_RDL (difference logic), QF\_UF (congruence closure), QF\_UFIDL (EUF + DL combined), QF\_LIA / QF\_UFLIA (Simplex for linear integer arithmetic).

**Exit codes** follow the SAT competition convention: **10 = SAT, 20 = UNSAT, 0 = UNKNOWN/timeout, 3 = error**.

---

## Goals

Modern SAT and SMT solvers are fast but largely single-threaded at the algorithmic level. ReasonMesh is a research project exploring what changes when clause learning, theory propagation, and cube decomposition are designed from the ground up to be parallel and distributed.

Three concrete goals drive the work:

**1. Asynchronous knowledge sharing (AKX protocol).**
Workers learn clauses and theory lemmas independently, then share them through a publish-subscribe bus with soundness guarantees. The import gate checks that an incoming clause is valid under the receiving worker's current assumption scope before applying it — so workers can run ahead without synchronising, and the bus can drop or reorder messages without affecting correctness.

**2. Scalable cube-and-conquer.**
Hard combinatorial problems (pigeonhole, graph colouring, chip verification) are split into sub-problems (cubes) by a lookahead splitter, then solved in parallel across local threads or remote machines over the TCP cluster transport. The scheduler tracks coverage and reassigns cubes from slow workers to fast ones.

**3. A practical SMT core for formal verification.**
The theory layer targets the logics that appear in real verification pipelines: QF_BV (bit-blasting for hardware), QF_LIA / QF_UFLIA (linear arithmetic for software), and QF_UF / QF_UFIDL (uninterpreted functions for abstract models). The long-term goal is a solver that Lean 4 and TLA+ tools can call as a drop-in SMT backend.

The project is academic research in progress. Results are compared against Z3, CaDiCaL, and Kissat on SATLIB and SMTLIB benchmarks using the experiment harness in `experiments/`.

---

## Table of contents

- [Install](#install)
- [Smoke test](#smoke-test)
- [CLI reference](#cli-reference)
- [Running the benchmarks](#running-the-benchmarks)
- [Cluster mode (coordinator + remote workers)](#cluster-mode)
- [Rust library](#rust-library)
- [Lean 4 and TLA+ integration](#lean-4-and-tla-integration)
- [Architecture](#architecture)

---

## Install

**Prerequisites**

| Tool | Version | Install |
|---|---|---|
| Rust (stable) | ≥ 1.82 | `curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs \| sh` |
| C compiler | any | macOS: `xcode-select --install`; Linux: `apt install build-essential` |
| tokio (bundled) | — | pulled by Cargo automatically |

Optional, for Lean 4 integration:

| Tool | Install |
|---|---|
| elan (Lean toolchain manager) | `curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \| sh` |

**Clone and build**

```sh
git clone https://github.com/akkeshavan/ReasonMesh
cd ReasonMesh
cargo build --release -p reasonmesh-cli
```

Add the binary to your PATH:

```sh
export PATH="$PWD/target/release:$PATH"
# or copy it permanently:
cp target/release/reasonmesh ~/.local/bin/
```

To build everything (all crates including benchmarks and tests):

```sh
cargo build --release --workspace
```

---

## Smoke test

Verify the build is working before doing anything else:

```sh
# Run the full test suite (takes ~30 s)
cargo test --workspace

# Then confirm the CLI works:

# Should print "s UNSATISFIABLE" and exit 20
reasonmesh solve benchmarks/satlib/aim/aim-100-1_6-no-1.cnf
echo "exit: $?"

# Should print "s SATISFIABLE" and exit 10
reasonmesh solve benchmarks/satlib/uf50/uf50-01.cnf
echo "exit: $?"
```

---

## CLI reference

### `reasonmesh solve` — solve a single file

```
reasonmesh solve <file> [options]
```

Accepts **DIMACS CNF** (`.cnf`) and **SMT-LIB 2** (`.smt2`, `.smt`). The strategy is selected with `--strategy`; `auto` (the default) analyses the instance and picks for you.

| Option | Default | Description |
|---|---|---|
| `--workers N` | 1 | Number of parallel CDCL threads |
| `--strategy` | auto | `auto`, `cdcl`, `portfolio`, `cnc`, `shared-db`, `cluster` |
| `--seed N` | 1 | Base random seed (workers get seed, seed+1, …) |
| `--deterministic` | off | Force 1 worker, fixed seed |
| `--max-conflicts N` | unlimited | Stop after N conflicts |
| `--timeout-secs N` | 300 | Wall-clock timeout |
| `--classify-only` | off | Print instance profile and exit without solving |
| `--trace PATH` | — | Write a `.rmtrace` replay file |
| `--proof-out PATH` | — | Write a `.rmproof` certificate |
| `--cluster-bind ADDR` | 127.0.0.1:7654 | Coordinator bind address (strategy=cluster) |
| `--cluster-cubes N` | 1 | Number of cubes to split into (strategy=cluster) |
| `--no-gpu` | off | Disable Metal GPU acceleration (macOS) |

**Single-threaded CDCL:**
```sh
reasonmesh solve benchmarks/satlib/uf100/uf100-01.cnf
```

**8-worker portfolio with clause sharing:**
```sh
reasonmesh solve benchmarks/satlib/uf100/uf100-01.cnf --workers 8 --strategy portfolio
```

**Parallel CDCL with shared in-memory clause database (best for a single 32+ core machine):**
```sh
reasonmesh solve benchmarks/satlib/uf250/uf250-01.cnf --workers 32 --strategy shared-db
```

**Cube-and-conquer (4 workers, lookahead splitting):**
```sh
reasonmesh solve benchmarks/satlib/uuf100/uuf100-01.cnf --workers 4 --strategy cnc
```

**SMT-LIB 2 input:**
```sh
reasonmesh solve problem.smt2
```

**With a proof certificate:**
```sh
reasonmesh solve benchmarks/satlib/aim/aim-100-1_6-no-1.cnf --proof-out run.rmproof
reasonmesh check-proof run.rmproof
# VALID UNSAT proof (100 vars, 160 clauses, 314 DRUP steps)
```

**Classify only (no solve):**
```sh
reasonmesh solve benchmarks/satlib/phole/hole6.cnf --classify-only
# vars=42 clauses=133 avg_clause_len=2.00 detected_class=CardinalityHeavy
```

---

### `reasonmesh serve` — multi-node clause sharing

Run the same DIMACS problem on multiple machines. Each node runs its own workers and forwards learned clauses to peers. The first node to find SAT or UNSAT wins.

```
reasonmesh serve <file> [options]
```

| Option | Default | Description |
|---|---|---|
| `--port N` | 9000 | TCP listen port |
| `--workers N` | 4 | CDCL threads on this node |
| `--seed N` | 1 | Base seed (use different seeds on each node) |
| `--peer host:port` | — | Peer address; may be repeated |
| `--timeout-secs N` | 300 | Per-node wall-clock timeout |
| `--bridge-ms N` | 50 | Clause bridge poll interval (ms) |
| `--export-lbd N` | 6 | Only forward clauses with LBD ≤ N to peers |

**Two-node example:**
```sh
# node 1
reasonmesh serve hard.cnf --port 9000 --workers 4 --seed 1  --peer host2:9001

# node 2 (different machine)
reasonmesh serve hard.cnf --port 9001 --workers 4 --seed 100 --peer host1:9000
```

Nodes retry peer connections for 30 seconds, so start order does not matter.

---

### `reasonmesh worker-node` — cluster worker

Connect to a coordinator running `solve --strategy cluster` and solve assigned cubes.

```
reasonmesh worker-node --coordinator host:port [--threads N]
```

| Option | Default | Description |
|---|---|---|
| `--coordinator` | required | Coordinator address (host:port) |
| `--threads N` | 0 | CDCL threads per cube (0 = all CPUs) |

The worker retries the connection for 60 seconds, so you can start workers before the coordinator is ready.

---

### `reasonmesh benchmark` — run a manifest

Run a TOML benchmark manifest and emit JSON results.

```sh
reasonmesh benchmark experiments/satlib-smoke.toml
# results printed as JSON to stdout

reasonmesh benchmark experiments/satlib-smoke.toml --checkpoint results/smoke.ckpt
# resumes from checkpoint if interrupted
```

---

### `reasonmesh replay` — inspect a trace

```sh
reasonmesh solve problem.cnf --trace run.rmtrace
reasonmesh replay run.rmtrace
# trace: run.rmtrace  solver=0.1.0  workers=1  deterministic=false
# events: 3
# ...
```

---

### `reasonmesh check-proof` — verify a certificate

```sh
reasonmesh check-proof run.rmproof
# VALID SAT model (50 vars, 218 clauses)    → exit 10
# VALID UNSAT proof (100 vars, 160 clauses, 314 DRUP steps) → exit 20
```

---

## Running the benchmarks

### Step 1 — Build the benchmark runner

```sh
cargo build --release -p rm-bench
cargo build --release -p reasonmesh-cli
export PATH="$PWD/target/release:$PATH"
```

### Step 2 — Quick smoke test (5 problems, ~10 s)

```sh
reasonmesh benchmark experiments/satlib-smoke.toml
```

Output is JSON. To save and compare:

```sh
reasonmesh benchmark experiments/satlib-smoke.toml > results/smoke.json
```

### Step 3 — SATLIB suite

The `benchmarks/satlib/` tree ships with several SATLIB categories. Run them all:

```sh
# 4-thread run on the full uf50/uuf50/uf100/uf250 suite
reasonmesh benchmark experiments/satlib-fair-4t.toml

# Against z3 and kissat baselines (requires those binaries on PATH)
reasonmesh benchmark experiments/satlib-full.toml
```

SATLIB directory layout:

| Directory | Content | Expect |
|---|---|---|
| `benchmarks/satlib/uf50/` | Random 3-SAT, 50 vars | sat |
| `benchmarks/satlib/uuf50/` | Random 3-SAT, 50 vars | unsat |
| `benchmarks/satlib/uf100/` | Random 3-SAT, 100 vars | sat |
| `benchmarks/satlib/uuf100/` | Random 3-SAT, 100 vars | unsat |
| `benchmarks/satlib/uf150/` – `uf250/` | Larger random 3-SAT | sat |
| `benchmarks/satlib/aim/` | AIM structured SAT/UNSAT | mixed |
| `benchmarks/satlib/phole/` | Pigeonhole `hole6.cnf`…`hole10.cnf` (hard UNSAT) | unsat |
| `benchmarks/satlib/flat50/` – `flat200/` | Graph colouring | sat |
| `benchmarks/satlib/parity/` | Parity constraints | mixed |

### Step 4 — SMT-LIB 2 benchmarks

The `benchmarks/smtlib/non-incremental/` tree contains QF\_UF, QF\_UFIDL, and QF\_UFLIA problems from the official SMTLIB suite. Run a sampled subset:

```sh
reasonmesh benchmark experiments/smtlib-uflia-run17.toml
```

### Step 5 — G-series (AKX research experiments)

The G-series experiments measure clause-sharing vs. isolated-portfolio performance:

```sh
# G1: PHP and random-SAT, sharing vs. isolated
reasonmesh benchmark experiments/g1-hard-sharing.toml > results/g1-sharing.json
reasonmesh benchmark experiments/g1-hard-isolated.toml > results/g1-isolated.json

# G2: scaling experiments (1w → 32w)
reasonmesh benchmark experiments/g2-scaling-1w.toml
reasonmesh benchmark experiments/g2-scaling-8w-selective.toml
reasonmesh benchmark experiments/g2-scaling-32w-selective.toml

# G3: against z3 and kissat
reasonmesh benchmark experiments/g3-vs-all-baselines.toml
```

To run G3 baselines you need `z3`, `kissat`, and `cadical` on your PATH.

### Step 6 — Cluster end-to-end test (Docker)

```sh
# build once (~3-5 min)
docker compose -f docker-compose-cluster.yml build

# run: 1 coordinator + 2 remote workers on aim-100-1_6-no-1.cnf
docker compose -f docker-compose-cluster.yml up
```

Expected output:
```
coordinator-1  | info: problem split into 2 cube(s)
coordinator-1  | info: cluster coordinator on 0.0.0.0:7654
worker1-1      | ...
coordinator-1  | s UNSATISFIABLE
```

### Benchmark manifest format

Write your own manifest TOML:

```toml
schema_version = 1
name = "my-experiment"
description = "Clause sharing on PHP instances"

[solver]
workers = 4
seed    = 1
timeout_secs = 300
parallel_problems = 4      # solve this many problems concurrently

[[baselines]]
name   = "z3"
binary = "z3"
args   = []

[[problems]]
name   = "php-5-4"
file   = "../benchmarks/satlib/phole/pigeon-hole5.cnf"
expect = "unsat"
```

Run it:
```sh
reasonmesh benchmark my-experiment.toml > results/my-experiment.json
```

---

## Cluster mode

The cluster transport is a TCP binary protocol. The coordinator holds the full CNF and splits it into cubes; workers connect, receive the problem, solve their cube, and report SAT/UNSAT.

**Single-machine cluster (coordinator + 4 local workers):**

```sh
reasonmesh solve benchmarks/satlib/uuf250/uuf250-01.cnf \
  --strategy cluster \
  --cluster-bind 127.0.0.1:7654 \
  --cluster-cubes 4 \
  --workers 4
```

**Multi-machine cluster:**

On the coordinator machine:
```sh
reasonmesh solve hard.cnf \
  --strategy cluster \
  --cluster-bind 0.0.0.0:7654 \
  --cluster-cubes 8 \
  --workers 0          # 0 = wait for remote workers only
```

On each worker machine:
```sh
reasonmesh worker-node --coordinator coordinator-host:7654 --threads 0
```

The coordinator waits up to 60 seconds for workers; workers retry for 60 seconds. Start order does not matter.

---

## Rust library

See [`docs/library.md`](docs/library.md) for the full reference. Quick summary:

**Add as a dependency (path-based, not yet on crates.io):**

```toml
# High-level API (SMT + SAT)
rm-api = { path = "path/to/ReasonMesh/crates/rm-api" }

# Or directly to the SMT facade (lower level)
rm-smt = { path = "path/to/ReasonMesh/crates/rm-smt" }

# Or directly to the SAT engine (lowest level)
rm-sat = { path = "path/to/ReasonMesh/crates/rm-sat" }
```

**One-line SMT call:**

```rust
use rm_api::solve_smtlib;

let result = solve_smtlib(
    "(set-logic QF_BV)
     (declare-const x (_ BitVec 8))
     (assert (bvult x #x0a))
     (check-sat)"
);
// result: SatResult::Sat(model) | SatResult::Unsat | SatResult::Unknown(reason)
```

**Parallel SAT (shared clause DB):**

```rust
use rm_sat::{parse_dimacs, ParallelCdclSolver, ParallelConfig, SolveResult};

let cnf = parse_dimacs(&std::fs::read_to_string("hard.cnf")?)?;
let solver = ParallelCdclSolver::from_dimacs(
    cnf.num_vars,
    &cnf.clauses,
    ParallelConfig { num_threads: 8, ..Default::default() },
);
match solver.solve() {
    SolveResult::Sat(model) => { /* model.value_of(var) */ }
    SolveResult::Unsat      => {}
    _                       => {}
}
```

---

## Lean 4 and TLA+ integration

See [`docs/integrations.md`](docs/integrations.md) for:
- Lean 4 tactics (`rm_decide`, `rm_decide_par`, `rm_decide_all`, `rm_smt`)
- Lean 4 programmatic API (`RmContext`, `RmSolver`, batch proof farm)
- TLA+ / TLAPS: calling ReasonMesh as an SMT backend subprocess
- C FFI header for calling from any language

---

## Architecture

The solver has three layers:

**CDCL engine (`rm-sat`)** — two-watched-literal BCP, 1-UIP conflict analysis, non-chronological backjumping, VSIDS, Luby restarts, LBD clause deletion. Closely follows MiniSAT/CaDiCaL conventions.

**Theory solvers (`rm-smt`)** — DPLL(T) loop wrapping each theory:
- `QF_BV`: Tseitin bit-blasting, compiled once to SAT
- `QF_IDL`/`QF_RDL`: incremental Bellman-Ford
- `QF_UF`: e-graph congruence closure
- `QF_UFIDL`: Nelson-Oppen EUF+DL combination
- `QF_LIA`/`QF_UFLIA`: Dutertre–de Moura incremental Simplex

**AKX bus (`rm-bus`, `rm-akx`)** — asynchronous publish/subscribe between workers. Each learned clause is tagged with a `Scope` and utility score (`1 / (1 + LBD)`). The `ImportGate` checks assumption-scoped soundness before applying any incoming clause. Low-utility clauses are evicted before consuming buffer space.

For the formal protocol, see the TLA+ specs in `tla/`. For the full design, see [`docs/architecture_spec.md`](docs/architecture_spec.md).

---

## Status

This is a research codebase in active development. The table below summarises what is working, what has been measured, and what is still to be done.

### Test coverage

| Crate | Tests | Notes |
|---|---|---|
| `rm-sat` | 74 unit | CDCL, BCP, restart, LBD, model extraction |
| `rm-smt` | 71 unit | All six logics; 2 QF_UFLIA congruence tests currently failing |
| `rm-syntax` | 32 unit | Parser, sort system, AST |
| `rm-theory-bv` | 26 unit | Bit-blasting, Tseitin encoding |
| `rm-scheduler` | 25 unit | Cube tree, lease management |
| `rm-bus` | 23 unit | In-process queue, TCP bus |
| `rm-akx` | 22 unit | Import predicate, scope soundness |
| `rm-proof` | 18 unit | DRUP recording and verification |
| `rm-theory-arith` | 17 unit | Bellman-Ford, Simplex |
| `rm-ir` | 13 unit | Term interning, circuit IR |
| `rm-theory-euf` | 10 unit | E-graph, congruence closure |
| `rm-telemetry` | 7 unit | Trace recording |
| `rm-worker` | 6 unit | Worker pool |
| `rm-cluster` | 7 integration | Differential correctness: parallel and cluster agree with 1-thread oracle |

~361 tests total. Run with `cargo test --workspace`.

### Benchmarks run

**SATLIB (807 problems, `experiments/satlib-fair-4t.toml`)**

4-thread parallel CDCL with AKX clause sharing, 300 s timeout, compared against Kissat (1 thread) and Z3 (4 threads).

| Category | Problems | Solved | Timeouts |
|---|---|---|---|
| uf50 / uuf50 | 100 | 100 | 0 |
| uf100 / uuf100 | 100 | 100 | 0 |
| uf150 / uuf150 | 100 | 100 | 0 |
| uf200 / uuf200 | 100 | 99 | 1 |
| uf250 / uuf250 | 100 | 97 | 3 |
| flat50–flat200 | 200 | 200 | 0 |
| aim | 72 | 72 | 0 |
| phole | 5 | 5 | 0 |
| parity | 30 | 24 | 6 |
| **Total** | **807** | **797 / 807** | **10** |

No wrong answers. 10 timeouts are all in parity and the harder uf/uuf250 instances.

**SMTLIB QF_UF / QF_UFIDL / QF_UFLIA (600 problems, latest run)**

600-problem sample from the official SMTLIB suite (200 per logic), 30 s timeout, single thread, compared against Z3.

| Logic | ReasonMesh | Z3 |
|---|---|---|
| QF_UF | 191 / 200 | ~200 |
| QF_UFIDL | 87 / 200 | ~199 |
| QF_UFLIA | 86 / 200 | ~159 |
| **Total** | **364 / 600** | **558 / 600** |

QF_UF is close to Z3. QF_UFIDL and QF_UFLIA are the active improvement areas.

**G-series (AKX clause sharing experiments)**

Clause sharing vs. isolated-portfolio comparisons on PHP and random-3-SAT instances. Results are in `results/` and analysed by `experiments/analyze_g2.py`. Scaling experiments cover 1–32 workers (`experiments/g2-scaling-*.toml`).

### Known issues

- **2 failing QF_UFLIA unit tests** (`uf_congruence_unsat`, `uf_constant_offset_arg_unsat`): Ackermann congruence not detected when argument equality is derivable from Simplex row equations rather than explicit bounds. Fix in progress.
- **QF_UFIDL timeout rate** (56%): Nelson-Oppen combination loop exits too early on disjunctive instances; T-propagation between EUF and DL is not yet complete.

### What needs to be done

- [ ] Fix the two failing QF_UFLIA congruence tests (`uf_congruence_unsat`, `uf_constant_offset_arg_unsat`)
- [ ] Complete QF_UFLIA T-propagation: `encode_var_eq` must reuse atoms from `arith_atom_cache` so Ackermann equality literals share SAT variables with user-asserted equalities; add model-value congruence check in `theory_final_check` for equalities derivable only from Simplex row equations
- [ ] Complete QF_UFIDL T-propagation: finish Nelson-Oppen EUF↔DL propagation so derived equalities from congruence closure are forwarded to the difference-logic solver without waiting for SAT search (currently 57% timeout rate)
- [ ] Parallel CDCL(T): wire theory solvers into the AKX bus so theory lemmas flow between workers (currently only SAT clauses are shared)
- [ ] Cube-and-conquer for SMT instances (currently only SAT)
- [ ] DRUP proof certificates for SMT logics (currently only QF_SAT has proofs)
- [ ] GPU acceleration: Metal WalkSAT kernel (stub exists, kernel not yet written); CUDA not started
- [ ] Lean 4 integration: library and tactic layer are documented in `docs/integrations.md` but not yet implemented
- [ ] CI on Linux and Windows (currently macOS-only)
- [ ] Publish to crates.io once the two test failures are fixed

---

## License

MIT — see [LICENSE](LICENSE).
