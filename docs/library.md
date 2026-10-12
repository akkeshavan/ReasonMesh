# ReasonMesh — Rust library reference

This document covers calling ReasonMesh from a Rust program. There are three entry points at different levels of abstraction:

| Crate | Level | Use when |
|---|---|---|
| `rm-api` | High-level | You want an ergonomic API with push/pop, parallel workers, batch solving, and model extraction by name |
| `rm-smt` | Mid-level | You have SMT-LIB 2 text and want direct access to `SmtResult`, or you need to control the logic explicitly |
| `rm-sat` | Low-level | You are solving SAT (DIMACS CNF), or you need the parallel CDCL solver with a shared clause DB |

---

## Adding the dependency

The crates are not yet published on crates.io. Use path dependencies:

```toml
# Cargo.toml

[dependencies]
rm-api = { path = "/path/to/ReasonMesh/crates/rm-api" }

# Optional — for direct SMT or SAT access:
rm-smt = { path = "/path/to/ReasonMesh/crates/rm-smt" }
rm-sat = { path = "/path/to/ReasonMesh/crates/rm-sat" }
```

---

## Part I — `rm-api`: high-level API

### One-shot SMT-LIB 2

The simplest entry point. Pass a complete SMT-LIB 2 script as a string; get back a `SatResult`.

```rust
use rm_api::{solve_smtlib, SatResult};

let result = solve_smtlib(
    "(set-logic QF_BV)
     (declare-const x (_ BitVec 8))
     (assert (bvult x #x0a))
     (check-sat)"
);

match result {
    SatResult::Sat(model) => {
        let (bits, width) = model.get_bitvec("x").unwrap();
        println!("x = {bits} ({width}b)");  // e.g. x = 7 (8b)
    }
    SatResult::Unsat => println!("unsat"),
    SatResult::Unknown(reason) => println!("unknown: {reason}"),
}
```

With a conflict budget (stops and returns `Unknown` when the budget is exhausted):

```rust
use rm_api::solve_smtlib_with_budget;

let result = solve_smtlib_with_budget(script, 500_000);
```

---

### Programmatic API: `Context` + `Solver`

Build formulas using `Expr` rather than writing SMT-LIB 2 text by hand.

```rust
use rm_api::{Context, Solver, SatResult};

let ctx = Context::new();
let mut solver = Solver::new(&ctx);

// Bit-vector constants
let x = ctx.bitvec_const("x", 32);
let y = ctx.bitvec_const("y", 32);
let zero = ctx.bitvec_val(0, 32);

solver.assert(&x.bvadd(&y).eq(&zero));  // x + y = 0
solver.assert(&x.bvugt(&zero));         // x > 0

match solver.check() {
    SatResult::Sat(model) => {
        let (x_val, _) = model.get_bitvec("x").unwrap();
        let (y_val, _) = model.get_bitvec("y").unwrap();
        println!("x={x_val}, y={y_val}");
    }
    SatResult::Unsat => println!("impossible"),
    SatResult::Unknown(r) => println!("gave up: {r}"),
}
```

**Integer arithmetic (difference logic):**

```rust
let ctx = Context::new();
let mut solver = Solver::new(&ctx);

let x = ctx.int_const("x");
let y = ctx.int_const("y");

solver.assert(&x.sub(&y).le(&ctx.int_val(5)));   // x - y ≤ 5
solver.assert(&y.sub(&x).le(&ctx.int_val(5)));   // y - x ≤ 5
assert!(solver.check().is_sat());
```

**Boolean constants:**

```rust
let ctx = Context::new();
let mut solver = Solver::new(&ctx);

let a = ctx.bool_const("a");
let b = ctx.bool_const("b");

solver.assert(&a.or(&b));       // a ∨ b
solver.assert(&ctx.not(&a));    // ¬a
assert!(solver.check().is_sat());  // b must be true
```

---

### Push / pop (incremental solving)

`push()` saves the current assertion stack; `pop()` restores it. Use this to explore multiple hypotheses without rebuilding the solver.

```rust
let ctx = Context::new();
let mut solver = Solver::new(&ctx);

let x = ctx.bitvec_const("x", 8);
solver.assert(&x.bvult(&ctx.bitvec_val(100, 8)));  // x < 100 — always present

solver.push();
solver.assert(&x.bvult(&ctx.bitvec_val(0, 8)));    // additionally: x < 0
assert!(solver.check().is_unsat());                 // impossible

solver.pop();
assert!(solver.check().is_sat());                   // x < 100 alone is fine
```

---

### Parallel workers

Race N independent solver instances. The first conclusive result wins.

```rust
use rm_api::{Context, Solver, SatResult, SolverConfig};
use std::time::Duration;

let ctx = Context::new();
let mut solver = Solver::with_config(
    &ctx,
    SolverConfig {
        num_workers: 8,
        max_conflicts: 1_000_000,
        timeout: Some(Duration::from_secs(60)),
    },
);

let x = ctx.bitvec_const("x", 64);
solver.assert(&x.bvult(&ctx.bitvec_val(42, 64)));
let result = solver.check();
```

---

### Batch solving (proof farm)

Solve many independent formulas concurrently. Useful when you have a list of verification conditions to discharge.

```rust
use rm_api::{Job, JobResult, SolverPool, SolverConfig};

let pool = SolverPool::new(SolverConfig {
    num_workers: 8,
    ..Default::default()
});

let jobs = vec![
    Job::new("(set-logic QF_BV)(declare-const x (_ BitVec 8))(assert (bvult x #x0a))(check-sat)")
        .with_label("vc_0"),
    Job::new("(set-logic QF_BV)(declare-const x (_ BitVec 4))(assert (= x #b0000))(assert (= x #b1111))(check-sat)")
        .with_label("vc_1"),
];

let results: Vec<JobResult> = pool.run_all(jobs);

for r in &results {
    let label = r.label.as_deref().unwrap_or("?");
    println!("{label}: {:?}", r.result);
    // vc_0: Sat(Model {...})
    // vc_1: Unsat
}
```

Results are returned in submission order regardless of which job finishes first.

---

### Working with `Model`

```rust
// Bit-vector variable (value, width)
let (bits, width) = model.get_bitvec("x").unwrap();
println!("x = {bits:#0width$x}", width = (width as usize / 4) + 2);

// Integer variable
let val: i64 = model.get_int("n").unwrap();

// Boolean variable
let b: bool = model.get_bool("flag").unwrap();
```

`Value` variants: `Value::BitVec(u64, u32)`, `Value::Int(i64)`, `Value::Bool(bool)`.

---

### Supported bit-vector operations

**Arithmetic:** `bvadd`, `bvsub`, `bvmul`, `bvneg`

**Bitwise:** `bvand`, `bvor`, `bvxor`, `bvnot`

**Comparisons (unsigned):** `bvult` (<), `bvule` (≤), `bvugt` (>), `bvuge` (≥)

**Comparisons (signed):** `bvslt` (<), `bvsle` (≤)

**Shifts:** `bvshl`, `bvlshr` (logical right shift), `bvashr` (arithmetic right shift)

**Structural:** `concat`, `extract(hi, lo)`, `zero_extend(n)`, `sign_extend(n)`

---

## Part II — `rm-smt`: mid-level SMT facade

Use `SmtSolver` when you want to parse and solve an SMT-LIB 2 script directly, with full access to the returned model values in SMT-LIB notation.

```rust
use rm_smt::{SmtSolver, SmtStatus, SmtError};

let script = r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (bvult x (_ bv10 8)))
(check-sat)
(get-model)
"#;

let solver = SmtSolver::parse(script)?;

match solver.solve(/* conflict budget */ u64::MAX) {
    Ok(result) => {
        match result.status {
            SmtStatus::Sat => {
                // result.values: Vec<(String, String)>
                // Each pair is (variable_name, smt_lib_value)
                for (name, value) in &result.values {
                    println!("{name} = {value}");  // e.g. x = (_ bv7 8)
                }
            }
            SmtStatus::Unsat  => println!("unsat"),
            SmtStatus::Unknown => println!("unknown"),
        }
    }
    Err(SmtError::UnsupportedLogic(logic)) => {
        eprintln!("logic {logic} not supported");
    }
    Err(SmtError::EmptyProblem) => {
        // No assertions — trivially SAT
    }
    Err(e) => eprintln!("solver error: {e}"),
}
```

### Supported logics

| Logic | Solver | Notes |
|---|---|---|
| `QF_BV` | Tseitin + CDCL | Full model output |
| `QF_IDL` / `QF_RDL` | Bellman-Ford | Integer/rational difference logic |
| `QF_UF` | Congruence closure | Model: term → representative name |
| `QF_UFIDL` | Nelson-Oppen (EUF+DL) | Combined |
| `QF_LIA` / `QF_UFLIA` | Simplex (DPLL(T)) | Linear integer arithmetic |
| *(none)* | Defaults to `QF_BV` | — |

All other logics return `SmtError::UnsupportedLogic`.

---

## Part III — `rm-sat`: low-level SAT engine

### Single-threaded CDCL

```rust
use rm_sat::{CdclSolver, SolveResult};
use rm_akx::literal::Literal;

let mut solver = CdclSolver::new(/* num_vars */ 3);

// Add clauses as slices of Literal
solver.add_clause(&[Literal::positive(1), Literal::positive(2)]);  //  x1 ∨  x2
solver.add_clause(&[Literal::negative(1), Literal::positive(3)]);  // ¬x1 ∨  x3

match solver.solve(/* assumptions */ &[], /* conflict budget */ u64::MAX) {
    SolveResult::Sat(model)  => println!("sat: x1={}", model.value_of(1)),
    SolveResult::Unsat       => println!("unsat"),
    SolveResult::BudgetExceeded | SolveResult::Unknown => println!("unknown"),
}
```

`Literal::positive(v)` means variable `v` is true. Variables are 1-indexed (`1..=num_vars`).

### Parsing DIMACS

```rust
use rm_sat::{parse_dimacs, DimacsCnf, DimacsError};

let text = std::fs::read_to_string("problem.cnf")?;
let cnf: DimacsCnf = parse_dimacs(&text)?;
// cnf.num_vars: u32
// cnf.clauses: Vec<Vec<i32>>  (DIMACS literals: positive = true, negative = false)
```

### Parallel CDCL with shared clause database

Multiple threads share a single `SharedClauseDb`. Workers export learned clauses with LBD ≤ 6 and import what others have discovered. The first thread to reach SAT or UNSAT wins.

```rust
use rm_sat::{parse_dimacs, ParallelCdclSolver, ParallelConfig, SolveResult};

let cnf = parse_dimacs(&std::fs::read_to_string("hard.cnf")?)?;
let solver = ParallelCdclSolver::from_dimacs(
    cnf.num_vars,
    &cnf.clauses,
    ParallelConfig {
        num_threads: 8,  // 0 = auto-detect logical CPUs
        ..Default::default()
    },
);

match solver.solve() {
    SolveResult::Sat(model)  => { /* model.value_of(var) */ }
    SolveResult::Unsat       => {}
    _                        => {}
}
```

`ParallelConfig` fields:

| Field | Default | Description |
|---|---|---|
| `num_threads` | 0 (auto) | Worker count; 0 uses `num_cpus` |
| `lbd_threshold` | 6 | Only export clauses with LBD ≤ this |
| `max_clauses` | 50000 | Clause DB capacity before eviction |
| `conflicts_per_slice` | 100 | Conflicts per work slice before clause exchange |

### Extern-cancel: stopping a parallel solve from outside

If you want to cancel a parallel solve from another thread or from an async context:

```rust
use std::sync::{Arc, atomic::{AtomicBool, Ordering}};
use rm_sat::{parse_dimacs, ParallelCdclSolver, ParallelConfig};

let cnf = parse_dimacs(&text)?;
let cancel = Arc::new(AtomicBool::new(false));

// Solver respects the flag within ~100 ms (one conflict slice)
let cancel_clone = Arc::clone(&cancel);
std::thread::spawn(move || {
    std::thread::sleep(std::time::Duration::from_secs(5));
    cancel_clone.store(true, Ordering::SeqCst);
});

let config = ParallelConfig { num_threads: 4, ..Default::default() };
let solver = ParallelCdclSolver::from_dimacs(cnf.num_vars, &cnf.clauses, config);
let result = solver.solve_with_cancel(cancel);
```

This is the same mechanism the TCP cluster uses to cancel workers when another worker finds SAT.

---

## Part IV — cluster transport (`rm-cluster`)

Programmatic access to the TCP cluster protocol. The coordinator distributes cubes; workers connect and solve.

```rust
use std::net::SocketAddr;
use rm_cluster::{ClusterCoordinator, ClusterResult, ClusterWorkerNode};

#[tokio::main]
async fn main() {
    let coord = ClusterCoordinator;
    let bound = coord.bind("127.0.0.1:0".parse::<SocketAddr>().unwrap()).await.unwrap();
    let addr = bound.addr;  // port assigned by OS

    // Spawn local workers
    for _ in 0..4 {
        tokio::spawn(async move {
            ClusterWorkerNode::new(/* threads */ 2).run(addr).await.ok();
        });
    }

    // Run: 2 cubes splitting on x1=true/false
    let cubes = vec![vec![1i32], vec![-1i32]];
    let result = bound.run(num_vars, clauses, cubes).await;

    match result {
        ClusterResult::Sat   => println!("sat"),
        ClusterResult::Unsat => println!("unsat"),
        ClusterResult::Failed(e) => eprintln!("error: {e}"),
    }
}
```

`BoundCoordinator::run` is cancel-safe: if a worker finds SAT, in-flight cubes in other workers are cancelled within one conflict slice.

---

## Environment variables

| Variable | Effect |
|---|---|
| `RUST_LOG=info` | Progress messages |
| `RUST_LOG=debug` | Per-task lifecycle and clause exchange statistics |
| `RUST_LOG=trace` | Very verbose — every BCP step |

Use the `env_logger` crate or call `env_logger::init()` in your application's `main` to honour `RUST_LOG`.
