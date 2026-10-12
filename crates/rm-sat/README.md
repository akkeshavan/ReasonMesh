# rm-sat

Production CDCL SAT engine from the [ReasonMesh](https://github.com/akkeshavan/ReasonMesh) solver. Two-watched-literal BCP, 1-UIP conflict analysis, non-chronological backjumping, VSIDS, Luby restarts, LBD clause deletion, and AKX-based parallel clause sharing.

## Usage

Add to your `Cargo.toml`:

```toml
rm-sat = { path = "path/to/ReasonMesh/crates/rm-sat" }
```

### Single-threaded solver

```rust
use rm_sat::{CdclSolver, SolveResult};
use rm_akx::literal::Literal;

let mut solver = CdclSolver::new(3); // 3 variables
solver.add_clause(&[Literal::positive(1), Literal::positive(2)]);
solver.add_clause(&[Literal::negative(1), Literal::positive(3)]);
match solver.solve(&[], u64::MAX) {
    SolveResult::Sat(model) => println!("SAT: x1={}", model.value_of(1)),
    SolveResult::Unsat      => println!("UNSAT"),
    _                       => {}
}
```

### Parallel solver from DIMACS

```rust
use rm_sat::{parse_dimacs, ParallelCdclSolver, ParallelConfig, SolveResult};

let cnf = parse_dimacs(&std::fs::read_to_string("problem.cnf")?)?;
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

### Cancellable solve (for timeouts)

```rust
use rm_sat::ParallelCdclSolver;
use std::sync::{Arc, atomic::AtomicBool};

let cancel = Arc::new(AtomicBool::new(false));
// pass cancel.clone() to a timer thread that sets it to true
let result = solver.solve_with_cancel(cancel);
```

See the [repository README](https://github.com/akkeshavan/ReasonMesh) for benchmarking and cluster usage.
