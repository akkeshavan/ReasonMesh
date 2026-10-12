# rm-api

High-level Rust API and C FFI for the [ReasonMesh](https://github.com/akkeshavan/ReasonMesh) parallel SAT/SMT solver.

**Supported logics:** QF_BV, QF_IDL, QF_RDL, QF_UF, QF_UFIDL, QF_LIA, QF_UFLIA

## Usage

Add to your `Cargo.toml`:

```toml
rm-api = { path = "path/to/ReasonMesh/crates/rm-api" }
```

### One-line SMT query

```rust
use rm_api::solve_smtlib;

let result = solve_smtlib(
    "(set-logic QF_BV)
     (declare-const x (_ BitVec 8))
     (assert (bvult x #x0a))
     (check-sat)"
);
// SatResult::Sat(model) | SatResult::Unsat | SatResult::Unknown(reason)
```

### Incremental solver

```rust
use rm_api::{Context, Solver, SolverConfig};

let ctx = Context::new();
let mut s = Solver::new(&ctx, SolverConfig { num_workers: 4, ..Default::default() });

s.push();
s.assert("(declare-const x Int) (assert (> x 5))");
let r = s.check();
s.pop();
```

### Batch / proof farm

```rust
use rm_api::SolverPool;

let pool = SolverPool::new(64);
let results = pool.solve_all(&obligations);
```

## C FFI

`rm-api` also builds as a `cdylib`. Link against `librm_api.dylib` (macOS) or `librm_api.so` (Linux) using the header at `include/rm_api.h`.

```c
#include "rm_api.h"
rm_model_t *model = NULL;
int32_t code = rm_solve_smtlib("(set-logic QF_BV)...(check-sat)", 500000, &model);
// RM_SAT=0, RM_UNSAT=1, RM_UNKNOWN=2
```

See the [full documentation](https://github.com/akkeshavan/ReasonMesh/blob/main/docs/library.md) for the complete API reference and the [integrations guide](https://github.com/akkeshavan/ReasonMesh/blob/main/docs/integrations.md) for Lean 4 and TLA+ usage.
