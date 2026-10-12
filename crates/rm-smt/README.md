# rm-smt

SMT-LIB 2 facade for the [ReasonMesh](https://github.com/akkeshavan/ReasonMesh) solver. Implements a DPLL(T) loop over theory solvers for QF_BV, QF_IDL, QF_RDL, QF_UF, QF_UFIDL, QF_LIA, and QF_UFLIA.

## Usage

Add to your `Cargo.toml`:

```toml
rm-smt = { path = "path/to/ReasonMesh/crates/rm-smt" }
```

### Parse and solve an SMT-LIB 2 script

```rust
use rm_smt::{SmtSolver, SmtStatus};
use std::sync::{Arc, atomic::AtomicBool};

let script = "
    (set-logic QF_LIA)
    (declare-const x Int)
    (declare-const y Int)
    (assert (>= x 0))
    (assert (<= (+ x y) 10))
    (assert (> y 7))
    (check-sat)
";

let cancel = Arc::new(AtomicBool::new(false));
let result = rm_smt::solve_qf_lia(script, cancel);
// LiaResult { status: LiaSat | LiaUnsat | LiaUnknown, model: Vec<(String, i64)> }
```

### Supported logics

| Logic | Theory |
|---|---|
| `QF_BV` | Tseitin bit-blasting |
| `QF_IDL` / `QF_RDL` | Bellman-Ford difference logic |
| `QF_UF` | E-graph congruence closure |
| `QF_UFIDL` | Nelson-Oppen EUF + DL |
| `QF_LIA` / `QF_UFLIA` | Dutertre-de Moura Simplex + Ackermann encoding |

For a higher-level interface with C FFI and batch solving, use [`rm-api`](https://crates.io/crates/rm-api).

See the [repository README](https://github.com/akkeshavan/ReasonMesh) for the full reference.
