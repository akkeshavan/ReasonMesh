# ReasonMesh

A massively parallel SMT solver built around **Asynchronous Knowledge Exchange (AKX)** — a protocol in which heterogeneous reasoners derive and share independently scoped logical knowledge without global coordination.

ReasonMesh is both an engineering artifact and a research experiment targeting a journal paper on whether AKX can serve as a scalable organizing principle for SMT solving.

---

## Architecture

```
               ┌──────────┐   ┌──────────┐
               │ CDCL-BV  │   │ CDCL-EUF │  …  (N workers)
               └────┬─────┘   └────┬─────┘
                    │   knowledge   │
                    └──────┬────────┘
                     AKX bus (rm-bus)
                           │
                  ┌────────┴────────┐
                  │  Orchestrator   │  (rm-orchestrator)
                  └────────┬────────┘
                           │  HTTP (SMT-LIB 2 tasks)
         ┌─────────────────┼─────────────────┐
  rm-coordinator      rm-node × N      Lean 4 tactic
```

Each worker runs a CDCL(T) loop and exports learned clauses via the bus. The bus applies utility-based eviction and assumption-scoped import filtering so workers never accept knowledge that would be unsound in their local context.

---

## Crates

| Crate | Role |
|---|---|
| `rm-syntax` | SMT-LIB 2.7 lexer and S-expression parser |
| `rm-sat` | CDCL solver with VSIDS, clause-DB reduction, and DRUP proof export |
| `rm-smt` | SMT facade: QF_BV, QF_IDL, QF_UF, QF_UFIDL; CDCL(T) via theory plugins |
| `rm-theory-bv` | Bit-vector theory (Tseitin bit-blasting + differential) |
| `rm-theory-euf` | Equality + uninterpreted functions (e-graph + congruence closure) |
| `rm-theory-arith` | Difference-logic arithmetic |
| `rm-ir` | Bitvector IR, DAG, and circuit builder |
| `rm-akx` | AKX protocol types: `KnowledgeBatch`, `TheoryLemma`, `Scope` |
| `rm-bus` | In-process bus (`InprocBus`) and TCP bridge (`NetBus`) |
| `rm-worker` | Multi-thread worker pool with portfolio diversification |
| `rm-scheduler` | Partition tree, lease management, and cube coverage |
| `rm-orchestrator` | Local orchestrator (single-node parallel solving) |
| `rm-coordinator` | HTTP coordinator for distributed cube-and-conquer + proof farms |
| `rm-node` | Distributed worker binary: polls coordinator, solves, reports back |
| `rm-proof` | Proof certificate recording and DRUP/model verification |
| `rm-telemetry` | Structured trace writer and reader for replay |
| `rm-bench` | Benchmark manifest runner |
| `rm-api` | High-level API + C FFI for embedding |
| `reasonmesh-cli` | CLI: `solve`, `serve`, `replay`, `check-proof`, `benchmark` |

---

## Build

```sh
cargo build --workspace
cargo test --workspace
cargo clippy --workspace --all-targets -- -D warnings
```

Requires stable Rust (≥ 1.82) and no external system dependencies beyond the Rust toolchain.

---

## CLI

```sh
# Solve a DIMACS or SMT-LIB 2 file
cargo run --bin reasonmesh -- solve problem.cnf
cargo run --bin reasonmesh -- solve problem.smt2 --workers 8

# Cluster mode: share learned clauses over TCP with peer nodes
cargo run --bin reasonmesh -- serve problem.cnf \
    --port 9000 --workers 4 --peer 10.0.0.2:9000

# Verify a proof certificate
cargo run --bin reasonmesh -- check-proof result.rmproof

# Run a benchmark manifest
cargo run --bin reasonmesh -- benchmark experiments/g1-hard-sharing.toml
```

Exit codes follow the SAT competition convention: 10 = SAT, 20 = UNSAT, 0 = UNKNOWN/TIMEOUT.

---

## Distributed solving

```sh
# Terminal 1 — coordinator
cargo run --bin rm-coordinator -- --addr 0.0.0.0:7700

# Terminal 2+ — solver nodes (any number of machines)
cargo run --bin rm-node -- --coordinator http://leader:7700 --concurrency 8
```

Submit a batch of SMT-LIB 2 scripts via the HTTP API:

```sh
curl -s -X POST http://localhost:7700/v1/batch \
  -H 'Content-Type: application/json' \
  -d '{"scripts": ["(set-logic QF_BV) (declare-const x (_ BitVec 8)) (assert (bvult x (_ bv10 8))) (check-sat)"], "max_conflicts": 100000}'
```

The coordinator implements two regimes:
- **Regime B (proof farm):** independent scripts solved in parallel; any node claims any task.
- **Regime A (cube-and-conquer):** a single formula partitioned recursively; nodes report `split=[pos, neg]` when their conflict budget is exhausted, and the coordinator fans out child cubes automatically.

Workers integrate a look-ahead heuristic that probes candidate split variables with a small conflict budget to guide the branching decision.

---

## Lean 4 integration

The `lean/` directory contains an `rm_api` Lake package with tactics that call the solver at elaboration time:

```lean
import RmApi

-- Close a goal by calling the SMT solver
example (x y : UInt32) (h : x + y = 0) (hx : x > 0) : False := by
  rm_smt

-- Parallel portfolio: solve under N independent configurations
example (x : UInt32) : x &&& x = x := by
  rm_decide_par
```

---

## Research context

The architecture and motivation are described in `docs/architecture_spec.md` (spec v0.2). The core hypothesis — that assumption-scoped asynchronous knowledge exchange can match or exceed globally coordinated CDCL(T) on large-scale workloads — is evaluated via the benchmark suite in `benchmarks/` and `experiments/`.

Failure to scale is measured and reported; the experiment is designed to be falsifiable.

---

## License

MIT — see [LICENSE](LICENSE).
