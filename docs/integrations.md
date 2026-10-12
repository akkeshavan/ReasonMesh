# ReasonMesh — Lean 4 and TLA+ integration

This document covers calling ReasonMesh from Lean 4 (as a tactic and as a programmatic API) and from TLA+ / TLAPS (as an SMT subprocess backend).

---

## Lean 4

### Prerequisites

| Tool | Install |
|---|---|
| elan | `curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \| sh` |
| Lean 4 toolchain | installed automatically by elan when you run `lake build` |
| Rust stable ≥ 1.82 | `rustup update stable` |

### Step 1 — build the shared library

The Lean package links against `librm_api`, the C FFI wrapper around the Rust solver.

```sh
# from the ReasonMesh repository root
cargo build --release -p rm-api
```

This produces:
- macOS: `target/release/librm_api.dylib`
- Linux: `target/release/librm_api.so`

The `lean/lakefile.lean` embeds an rpath pointing at this exact directory, so `LD_LIBRARY_PATH` is not needed at runtime.

To install the library to a non-default location (e.g. for a system-wide install), set:

```sh
export RM_API_LIB_DIR=/usr/local/lib
cp target/release/librm_api.{dylib,so} /usr/local/lib/
```

### Step 2 — build the Lean package

```sh
cd lean
lake build
```

Lake compiles `ffi/rm_lean_ffi.c` as an `extern_lib` and links it against `librm_api`. The result is the `RmApi` Lean library.

Run the integration tests to verify everything works:

```sh
lake exe RmApiTest
```

Expected output:
```
=== Programmatic API ===
  (empty assertion set) → SAT: ok (expected)
=== SMT-LIB 2 text interface ===
  SAT query → SAT/UNKNOWN (expected)
  UNSAT query → UNSAT (expected)
=== Batch solver (proof farm) ===
  job 0 → SAT
  job 1 → UNSAT
  job 2 → UNSAT
  checkAllUnsat on 2 UNSAT jobs → true
  openObligations on mixed jobs → indices #[0]
=== RmPool ===
  pool result[0] → SAT
  pool result[1] → UNSAT
All tests completed.
```

### Step 3 — add RmApi to your project

In your `lakefile.lean`:

```lean
require RmApi from "../path/to/ReasonMesh/lean"
```

Then in any Lean file:

```lean
import RmApi
```

This imports all four modules: `RmApi.Basic`, `RmApi.Emit`, `RmApi.Tactic`, and `RmApi.Pool`.

---

### Tactics

#### `rm_decide`

Automatically translates the current goal and all local hypotheses to SMT-LIB 2, calls the solver, and closes the goal if the negated query is UNSAT.

```lean
example (x : UInt32) (h : x < 1000) : x + 1 ≤ 1000 := by
  rm_decide

example (x y : UInt8) (h1 : x < 10) (h2 : y < 10) : x + y < 20 := by
  rm_decide
```

On SAT, the tactic fails and prints a counter-example. On an unsupported fragment, it suggests `decide` or `omega` as fallbacks.

#### `rm_decide_par (n)`

Like `rm_decide` but races `n` independent solver threads (portfolio parallelism). Use on goals that benefit from heuristic diversity.

```lean
example (x : BitVec 64) (h : x.toNat < 2^32) :
    (x &&& 0xFFFFFFFF#64) = x := by
  rm_decide_par (4)
```

#### `rm_decide_all`

Closes **all current goals** in parallel in one batch call. Goals outside the supported fragment remain open.

```lean
example : (0 : UInt8) < 255 ∧ (1 : UInt8) < 255 ∧ (2 : UInt8) < 255 := by
  constructor <;> constructor
  all_goals rm_decide_all
```

#### `rm_smt "..."`

Low-level escape hatch. Pass a hand-written SMT-LIB 2 script; the goal is closed with `rm_oracle` if the script returns UNSAT.

```lean
example : True := by
  rm_smt "(set-logic QF_BV)
          (declare-const x (_ BitVec 8))
          (assert (bvult x (_ bv0 8)))
          (check-sat)"
```

The current goal type is ignored for translation. The script must contain `(check-sat)`.

---

### Supported Lean fragment

The `RmApi.Emit` layer translates a subset of Lean 4 expressions to SMT-LIB 2.

**Types**

| Lean type | SMT sort | Logic |
|---|---|---|
| `Bool` | uninterpreted constant | QF\_UF |
| `UInt8`, `UInt16`, `UInt32`, `UInt64` | `(_ BitVec 8/16/32/64)` | QF\_BV |
| `BitVec n` | `(_ BitVec n)` | QF\_BV |
| `Int` | `Int` (linear arithmetic only) | QF\_IDL |
| `Prop` connectives | SMT-LIB 2 core | (any) |

**Operators**

| Lean | SMT-LIB 2 |
|---|---|
| `∧` / `∨` / `¬` | `and` / `or` / `not` |
| `=` / `≠` | `=` / `(not (= ...))` |
| `+` / `-` | `bvadd` / `bvsub` (bitvec); `+` / `-` on `Int` → linear arithmetic |
| `&&&` / `\|\|\|` / `^^^` | `bvand` / `bvor` / `bvxor` |
| `<<<` / `>>>` | `bvshl` / `bvlshr` |
| `<` / `≤` / `>` / `≥` | unsigned bitvec comparisons; `<` on `Int` → integer `<` |

**Not supported** (tactic falls back or skips the hypothesis):

- `Nat` — use `UInt32`/`UInt64` or `omega` instead
- `Float` / `Real` / non-linear arithmetic (`x * y` where both are variables)
- Quantifiers (`∀`, `∃`)
- Inductive types, recursive types, type-class hypotheses
- `String`, `List`, `Array`
- Coercions between numeric types

---

### Programmatic Lean API

For incremental solving or use outside a tactic proof:

```lean
import RmApi.Basic
open RmApi

def checkConstraint : IO Unit := do
  let ctx ← RmContext.new
  let s   ← RmSolver.new ctx (numWorkers := 4) (maxConflicts := 500000)

  s.push

  -- Use solveSmtlib for direct SMT-LIB 2 text queries
  let (result, modelStr) ← solveSmtlib
    "(set-logic QF_BV)
     (declare-const x (_ BitVec 8))
     (assert (bvult x #x0a))
     (check-sat)" 0

  match result with
  | .sat _    => IO.println s!"SAT: {modelStr}"
  | .unsat    => IO.println "UNSAT"
  | .unknown r => IO.println s!"unknown: {r}"

  s.pop
```

**Key types**

| Type | Description |
|---|---|
| `RmContext` | Solver context — manages variable lifetime |
| `RmSolver` | Incremental solver — push/pop scope stack |
| `RmModel` | Counter-example model — query by variable name |
| `SatResult` | `.sat (model : RmModel)` \| `.unsat` \| `.unknown (reason : String)` |

All handles are wrapped in Lean's `ExternalObject` GC and freed automatically.

**Key functions**

```lean
-- Single-shot text interface
solveSmtlib (script : String) (maxConflicts : UInt64) : IO (SatResult × String)

-- Model queries
RmModel.getBitvec (m : RmModel) (name : String) : IO (Option (UInt64 × UInt32))
RmModel.getInt    (m : RmModel) (name : String) : IO (Option Int)
RmModel.toString  (m : RmModel) : IO String
```

---

### Batch / proof farm

Discharge thousands of independent proof obligations concurrently:

```lean
import RmApi
open RmApi

def verifyAll (obligations : Array String) : IO Bool :=
  checkAllUnsat obligations (numWorkers := 64)

-- Get structured results (index + result code):
def verifyWithDiag (obligations : Array String) : IO (Array PoolResult) :=
  RmPool.solveAll obligations (numWorkers := 64)

-- Get indices of unprovable obligations:
def whichFailed (obligations : Array String) : IO (Array Nat) :=
  openObligations obligations (numWorkers := 64)
```

`solveBatch` result codes: `0` = SAT, `1` = UNSAT, `2` = UNKNOWN.

---

### Soundness and `rm_oracle`

All tactics that close goals via the solver apply the axiom:

```lean
axiom rm_oracle : ∀ (p : Prop), p
```

This trusts the solver's UNSAT verdict. To audit which theorems in your project depend on it:

```lean
#print axioms myTheorem
-- RmApi.rm_oracle  (if rm_decide was used)
```

Or at the shell:

```sh
grep -r "rm_oracle" .lake/build/
```

ReasonMesh writes DRUP proof certificates to `.rmproof` files. These can be externally verified with `lrat-check`. Kernel-level certificate checking that would eliminate `rm_oracle` entirely is planned for a future release.

---

## TLA+ / TLAPS

TLA+ has two distinct proof contexts where an external SMT solver is useful:

1. **TLAPS (TLA+ Proof System)** — discharge proof obligations generated from a TLA+ proof
2. **TLC (TLC model checker)** — TLAPS uses Z3 and Isabelle/HOL as backends; you can substitute ReasonMesh for Z3

### Calling ReasonMesh as a subprocess (recommended)

TLAPS drives backend solvers as child processes reading SMT-LIB 2 from stdin. Any SMT-LIB 2-capable solver can be wired in.

**Step 1 — wrap ReasonMesh as a SMTLIB-compliant subprocess:**

Create a shell wrapper that accepts SMT-LIB 2 on stdin and prints `sat` or `unsat` to stdout:

```sh
#!/usr/bin/env sh
# reasonmesh-smt-backend.sh
exec reasonmesh solve /dev/stdin --strategy auto "$@"
```

Mark it executable:
```sh
chmod +x reasonmesh-smt-backend.sh
```

**Step 2 — configure TLAPS to use it:**

In your TLAPS configuration (typically `~/.config/tlapm/config`):

```
backend.smt = reasonmesh-smt-backend.sh
```

TLAPS will call the binary with an SMT-LIB 2 file and read the result.

**Step 3 — verify with TLAPS:**

```tla
---- MODULE MySpec ----
THEOREM MyProperty
  BY Z3  \* replace Z3 with your configured backend
```

Or force the backend explicitly:

```tla
THEOREM MyProperty
  BY Backend "reasonmesh-smt-backend.sh"
```

### Calling the C FFI directly from a TLA+ tool

If you are building a TLA+ tool in C or C++, link against `librm_api` directly. The header is at `crates/rm-api/include/rm_api.h`.

```c
#include "rm_api.h"

// Single-shot SMT-LIB 2 query
rm_model_t *model = NULL;
int32_t code = rm_solve_smtlib(
    "(set-logic QF_BV)"
    "(declare-const x (_ BitVec 8))"
    "(assert (bvult x #x0a))"
    "(check-sat)",
    /* conflict budget */ 500000,
    &model
);
// code: RM_SAT (0), RM_UNSAT (1), RM_UNKNOWN (2)

if (code == RM_SAT && model) {
    uint64_t bits;  uint32_t width;
    rm_model_get_bitvec(model, "x", &bits, &width);
    printf("x = %" PRIu64 " (%ub)\n", bits, width);
    rm_model_free(model);
}
```

**Full C FFI reference**

| Function | Description |
|---|---|
| `rm_context_new() → rm_context_t*` | Create solver context |
| `rm_context_free(ctx)` | Free context and all resources |
| `rm_solver_new(ctx, workers, max_conflicts) → rm_solver_t*` | Create incremental solver |
| `rm_solver_assert(s, expr)` | Add constraint |
| `rm_solver_push(s)` / `rm_solver_pop(s)` | Scope stack |
| `rm_solver_check(s, &model) → int32_t` | Check satisfiability |
| `rm_solve_smtlib(script, budget, &model) → int32_t` | Single-shot text interface |
| `rm_solve_batch(scripts, n, workers, budget, results)` | Batch: one result code per script |
| `rm_model_get_bitvec(m, name, &bits, &width) → int` | Query bit-vector variable |
| `rm_model_get_int(m, name, &val) → int` | Query integer variable |
| `rm_model_iter(m, callback, userdata)` | Iterate all assignments |
| `rm_model_free(m)` | Free model |

Return codes: `RM_SAT = 0`, `RM_UNSAT = 1`, `RM_UNKNOWN = 2`.

Link flags on Linux:
```sh
gcc myapp.c -I crates/rm-api/include -L target/release -lrm_api -Wl,-rpath,target/release -o myapp
```

Link flags on macOS:
```sh
clang myapp.c -I crates/rm-api/include -L target/release -lrm_api \
  -Wl,-rpath,@loader_path/../target/release -o myapp
```

### Calling from any language with subprocess I/O

For Python, Go, or any other language, the simplest integration is to call the `reasonmesh` binary as a subprocess:

**Python example:**

```python
import subprocess

def check_sat(smt_script: str, timeout: int = 10) -> str:
    """Returns 'sat', 'unsat', or 'unknown'."""
    result = subprocess.run(
        ["reasonmesh", "solve", "/dev/stdin"],
        input=smt_script.encode(),
        capture_output=True,
        timeout=timeout,
    )
    for line in result.stdout.decode().splitlines():
        if line.startswith("s "):
            return line[2:].lower()  # 'satisfiable' → 'sat'
    return "unknown"

# Example
verdict = check_sat("""
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (bvult x #x0a))
(check-sat)
""")
print(verdict)  # sat
```

**Go example:**

```go
package main

import (
    "fmt"
    "os/exec"
    "strings"
)

func checkSat(script string) string {
    cmd := exec.Command("reasonmesh", "solve", "/dev/stdin")
    cmd.Stdin = strings.NewReader(script)
    out, err := cmd.Output()
    if err != nil {
        return "unknown"
    }
    for _, line := range strings.Split(string(out), "\n") {
        if strings.HasPrefix(line, "s SATISFIABLE") {
            return "sat"
        }
        if strings.HasPrefix(line, "s UNSATISFIABLE") {
            return "unsat"
        }
    }
    return "unknown"
}
```

### Supported SMT-LIB 2 logics for TLA+ use

TLAPS generates QF\_UF and mixed-logic queries. The logics ReasonMesh handles:

| Logic | Typical TLA+ use case |
|---|---|
| `QF_BV` | Bit-level protocol properties, word arithmetic |
| `QF_IDL` | Integer difference constraints, timing properties |
| `QF_UF` | Uninterpreted functions in action formulas |
| `QF_UFIDL` | Combined EUF + difference logic |
| `QF_LIA` | Linear integer arithmetic (Presburger formulas) |
| `QF_UFLIA` | Combined EUF + linear arithmetic |

If TLAPS generates a query in an unsupported logic (e.g. `QF_NIA` with non-linear products), ReasonMesh returns exit code 0 (`UNKNOWN`) and TLAPS will fall back to Z3 or Isabelle.

---

## Troubleshooting

**`lake build` fails with "library not found for -lrm_api"**

The shared library was not built yet. Run `cargo build --release -p rm-api` from the repository root first.

**Tactic says "goal outside supported fragment"**

Common causes:
- `Nat` variables: use `UInt32`/`UInt64` or the `omega` tactic
- `x * y` where both are variables (non-linear): use `decide` for small finite types
- Inductive or recursive types: extract the scalar sub-goal manually

**Counter-example is hard to read**

The model string is in SMT-LIB 2 `get-model` format: `(x #b00001010)`. Use `RmModel.getBitvec` / `RmModel.getInt` for structured access.

**`rm_decide` is very slow**

Try `rm_decide_par (n)` with `n` = number of available cores. For very large goals, consider `rm_smt` with a hand-optimised script or the batch API.

**TLAPS backend does not find `reasonmesh`**

Either put `reasonmesh` on PATH before starting TLAPS, or use the full path in the backend configuration:

```
backend.smt = /home/user/.local/bin/reasonmesh-smt-backend.sh
```
