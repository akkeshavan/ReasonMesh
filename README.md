# ReasonMesh

ReasonMesh is a massively parallel SMT solver. It is designed for workloads that existing solvers handle sequentially but that have enough internal structure to exploit dozens or hundreds of cores — large bit-vector verification conditions, distributed proof farms for interactive theorem provers, and cube-and-conquer decompositions of hard industrial formulas.

The project is also a research experiment. The central hypothesis is that **Asynchronous Knowledge Exchange (AKX)** — a protocol in which heterogeneous reasoners share what they have learned without global synchronization — can serve as the organizing principle for a scalable SMT solver in the same way that clause sharing organized parallel SAT solvers in the 2010s. The `benchmarks/` and `experiments/` directories contain the artifacts needed to evaluate that hypothesis. We report negative results.

---

## Why not just use Z3, CaDiCaL, or CVC5?

The short answer is that none of them were designed for the workload we care about.

**Z3** is excellent for single-threaded reasoning across a wide range of logics. Its parallel mode (`/p:n`) runs independent portfolio strategies, but there is no shared learning between them. Two Z3 threads that independently discover the same useful lemma do not tell each other about it. On problems where clause sharing matters — large random instances, hard industrial bit-vector problems — this leaves performance on the table.

**CaDiCaL and Kissat** are state-of-the-art SAT solvers with highly tuned CDCL implementations. Parallel variants (Mallob, HordeSAT, etc.) add clause sharing via an exchange buffer and have won the parallel track of the SAT competition. But they solve SAT, not SMT. Adding theory support requires rebuilding the exchange mechanism so that theory lemmas (difference-logic bounds, congruence closure explanations) obey the same sharing rules as propositional clauses. That is a significant redesign.

**CVC5** has a genuine parallel mode and supports a wide range of logics. The architecture is a centralized controller with worker processes. ReasonMesh differs in that workers are first-class: each has its own clause database and the exchange protocol is point-to-point. There is no shared data structure that all workers contend on under load.

The deeper difference is the **ImportGate**. In a cube-and-conquer decomposition, different workers are solving different sub-problems — the cube assigned to one worker changes what learned clauses are sound to apply in another. Existing parallel solvers either avoid this entirely (portfolio only, no decomposition) or handle it by keeping workers on the same problem and accepting that some shared clauses may be redundant. AKX has an explicit assumption-scoped soundness predicate: a clause learned under assumptions `A` is only imported by a worker if the worker's current assumption set is consistent with `A`. This makes sharing sound across cube boundaries.

---

## How it works

A ReasonMesh solve has three layers:

**The CDCL engine** (`rm-sat`) implements two-watched-literal BCP, 1-UIP conflict analysis, non-chronological backjumping, VSIDS branching, Luby restarts, and LBD-based clause deletion. This is the standard modern CDCL core, closely following MiniSAT and CaDiCaL conventions.

**Theory solvers** feed lemmas back into the CDCL engine when the theory detects inconsistency:
- `QF_BV`: Tseitin bit-blasting — the formula is compiled to pure SAT once, then CDCL runs to completion.
- `QF_IDL` / `QF_RDL`: Bellman-Ford difference logic — no CDCL at all; satisfiability is a graph reachability question.
- `QF_UF`: E-graph congruence closure.
- `QF_UFIDL`: combined EUF + DL via a simplified CDCL(T) loop.

**The AKX bus** (`rm-bus`, `rm-akx`) sits between workers. When a worker learns a clause, it packages it as a `KnowledgeObject` tagged with a `Scope` and a `TrustLevel`, and publishes it. Workers poll the bus between CDCL steps. The `ImportGate` checks the assumption-scoped soundness predicate before applying any incoming knowledge. The bus applies utility-based eviction (`utility = 1 / (1 + LBD)`) so low-quality clauses are dropped before they consume buffer space.

For the full architecture, see [`docs/architecture.md`](docs/architecture.md). For API and CLI usage, see [`docs/usage.md`](docs/usage.md).

---

## Install

ReasonMesh is not yet published to crates.io. Build from source:

**Prerequisites:**
- Rust stable, version 1.82 or later. Install via [rustup](https://rustup.rs):
  ```sh
  curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
  ```
- A C compiler (needed by a few transitive dependencies). On macOS, `xcode-select --install` covers this.
- For Lean integration: [elan](https://github.com/leanprover/elan) (the Lean toolchain manager).

**Clone and build:**

```sh
git clone https://github.com/your-org/ReasonMesh
cd ReasonMesh
cargo build --release --workspace
```

The release build enables LTO and full optimization. Debug builds (`cargo build --workspace`) are faster to compile and include debug symbols.

**Put the binaries on your PATH:**

```sh
export PATH="$PWD/target/release:$PATH"
```

Or copy the three binaries to wherever you keep local tools:

```sh
cp target/release/reasonmesh target/release/rm-coordinator target/release/rm-node ~/.local/bin/
```

---

## Smoke test

Verify the build is working before doing anything else:

```sh
# Run the test suite
cargo test --workspace

# Check for warnings that would break CI
cargo clippy --workspace --all-targets -- -D warnings
```

Then confirm the solver can actually solve something:

```sh
# Should print "s UNSATISFIABLE" and exit with code 20
reasonmesh solve benchmarks/g3/tseitin-600-1.cnf
echo "exit: $?"

# Should print "s SATISFIABLE" with a model
reasonmesh solve benchmarks/g3/r3sat-500-001.cnf
echo "exit: $?"
```

If both run and return the expected exit codes (20 and 10 respectively), you're good.

---

## Running standalone with the CLI

The `reasonmesh` binary has five subcommands. The two you will use most are `solve` and `serve`.

**Solve a single file:**

```sh
# DIMACS CNF
reasonmesh solve problem.cnf

# SMT-LIB 2
reasonmesh solve problem.smt2

# Multiple workers (portfolio: different seeds, first result wins)
reasonmesh solve hard.cnf --workers 8

# Bounded run: stop after N conflicts and report UNKNOWN
reasonmesh solve hard.cnf --workers 4 --max-conflicts 1000000

# Save a proof certificate
reasonmesh solve problem.cnf --proof-out result.rmproof
reasonmesh check-proof result.rmproof
```

Exit codes follow the SAT competition convention: **10 = SAT**, **20 = UNSAT**, **0 = UNKNOWN or timeout**, **3 = internal error**.

**Cluster mode — share learned clauses over TCP:**

Start one process per machine. All must load the same file. Each runs its own workers and exchanges learned clauses with peers. Connections retry for 30 seconds, so start order does not matter.

```sh
# Machine 1
reasonmesh serve problem.cnf --port 9000 --workers 4 --peer machine2:9001

# Machine 2
reasonmesh serve problem.cnf --port 9001 --workers 4 --peer machine1:9000
```

Only clauses with LBD ≤ 6 are forwarded between nodes by default. Adjust with `--export-lbd`. See `docs/usage.md` for the full flag reference.

---

## Lean 4 integration

ReasonMesh exposes a C FFI and a Lean 4 package (`lean/`) that wraps it with four tactics. The solver runs at elaboration time and closes goals automatically.

**Step 1 — build the shared library:**

```sh
cargo build --release -p rm-api
```

This produces `target/release/librm_api.dylib` (macOS) or `target/release/librm_api.so` (Linux).

**Step 2 — build the Lean package:**

```sh
cd lean
lake build
```

Lake links against the shared library using the path baked into `lakefile.lean`. If your build is somewhere else, set `RM_API_LIB_DIR` before running `lake build`.

**Step 3 — add `RmApi` as a Lake dependency in your project:**

```lean
-- lakefile.lean
require RmApi from "<path-to-ReasonMesh>/lean"
```

**Using the tactics:**

```lean
import RmApi

-- Close a bitvector goal automatically
example (x : UInt8) (h : x < 200) : x + 1 ≤ 200 := by
  rm_decide

-- Race N portfolio workers; useful when the goal's search space is irregular
example (a b : UInt32) : (a &&& b) ||| (a ^^^ b) = a ||| b := by
  rm_decide_par 8

-- Close all current goals in parallel (proof farm)
example (x y : UInt32) (h1 : x < 100) (h2 : y < 100) : x < 1000 ∧ y < 1000 := by
  constructor <;> rm_decide_all

-- Provide a hand-written SMT-LIB 2 script when the tactic can't infer the encoding
example : True := by
  rm_smt "(set-logic QF_BV)
          (declare-const x (_ BitVec 8))
          (assert (bvult x #x0a))
          (check-sat)"
```

**A note on soundness:** `rm_decide` closes goals via `RmApi.rm_oracle`, an axiom that trusts the solver's UNSAT verdict. This is the same trust model as `native_decide` — you are trusting the solver's output, not a verified proof. Future work includes LRAT certificate verification that would eliminate the axiom entirely.

---

## Distributed solver (coordinator + workers)

For large proof farms or long-running cube-and-conquer jobs, the distributed mode separates the coordinator from the workers. The coordinator accepts jobs over HTTP; workers poll for tasks, solve them, and report back.

```sh
# Start the coordinator
rm-coordinator --addr 0.0.0.0:7700

# Start workers on any number of machines
rm-node --coordinator http://leader:7700 --concurrency 8
```

Submit a batch of independent SMT-LIB 2 scripts:

```sh
curl -X POST http://localhost:7700/v1/batch \
  -H 'Content-Type: application/json' \
  -d '{"scripts": ["(set-logic QF_BV) (declare-const x (_ BitVec 8)) (assert (bvult x #x0a)) (check-sat)"],
       "max_conflicts": 100000}'
```

See `docs/usage.md` for the full HTTP API reference and both solving regimes (proof farm and cube-and-conquer).

---

## Research context

The architecture is described in full in [`docs/architecture.md`](docs/architecture.md), including the rationale behind each major design decision. The `experiments/` directory contains benchmark manifests that compare clause-sharing vs. isolated portfolio modes across the G-series problem sets. The core question is whether AKX utility-filtered sharing produces measurable speedup over pure portfolio, and under what conditions it helps or hurts.

The codebase is structured to be a credible research artifact: benchmark results are reproducible via manifest files, the proof format is documented, and the telemetry system records enough information to replay any run.

---

## License

MIT — see [LICENSE](LICENSE).
