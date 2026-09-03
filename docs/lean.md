# Lean 4 integration

ReasonMesh ships a native Lean 4 package (`lean/RmApi`) that lets you discharge proof obligations directly from Lean tactics or from ordinary `IO` code. The integration goes all the way down: Lean expressions are translated to SMT-LIB 2, sent to the ReasonMesh solver over a C FFI, and results are returned as `SatResult` values or closed goals.

---

## Architecture

```
Lean elaborator / tactic monad
        │
        │  (Lean Expr tree)
        ▼
   RmApi.Emit.buildScript
        │  emitExpr: recursive Expr → SMT-LIB 2 string
        │  collects hypotheses from local context
        │  negates goal and assembles (check-sat) script
        ▼
   rm_lean_ffi.c   ← compiled by Lake as extern_lib
        │  rm_solve_smtlib_lean / rm_solve_batch_lean
        │  Lean 4 calling convention: world token, lean_external_class GC
        ▼
   librm_api.{dylib,so}   ← Rust crate rm-api (cdylib)
        │  rm_solve_smtlib / rm_solve_batch
        ▼
   rm-smt / rm-sat / rm-theory-bv …
        │  CDCL + theory combination
        ▼
   SatResult:  .unsat / .sat model / .unknown reason
        │
        ▼
   Tactic: close goal with rm_oracle  (if UNSAT)
        or: surface counter-example   (if SAT)
        or: suggest fallback tactic   (if outside fragment)
```

The FFI is entirely text-based at the tactic level: Lean translates to SMT-LIB 2, passes a string, and gets back a result code plus an optional model string. The programmatic API additionally exposes opaque handle types (`RmContext`, `RmSolver`, `RmExpr`, `RmModel`) for incremental solving.

---

## Prerequisites

- [elan](https://github.com/leanprover/elan) / Lean 4 toolchain (any recent stable release)
- `lake` (bundled with elan)
- Rust toolchain (stable, 1.80+) for building the shared library
- macOS 13+ or Linux with glibc 2.35+

---

## Building the shared library

The Lean package links against `librm_api`, which is built from the `rm-api` Rust crate:

```sh
# from the repository root
cargo build --release -p rm-api
```

This produces `target/release/librm_api.dylib` (macOS) or `target/release/librm_api.so` (Linux). The Lake build embeds an rpath pointing at that exact directory, so you do not need to set `LD_LIBRARY_PATH` at runtime.

To override the library directory (e.g. for a system-wide install):

```sh
export RM_API_LIB_DIR=/usr/local/lib
```

---

## Building the Lean package

```sh
cd lean
lake build
```

Lake compiles `ffi/rm_lean_ffi.c` as an `extern_lib` object and links it together with `librm_api`. The result is a Lean library `RmApi` and a test executable `RmApiTest`.

To run the integration tests:

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

---

## Adding RmApi to your project

In your `lakefile.lean`:

```lean
require RmApi from "../path/to/reasonmesh/lean"
```

Or, once the package is published:

```lean
require RmApi from git "https://github.com/reasonmesh/reasonmesh" @ "main" / "lean"
```

Then import:

```lean
import RmApi
```

This imports all four modules: `RmApi.Basic`, `RmApi.Emit`, `RmApi.Tactic`, and `RmApi.Pool`.

---

## Tactics

### `rm_decide`

Automatically translates the current goal and all local hypotheses to SMT-LIB 2 and calls the solver. If the solver returns UNSAT, the goal is closed via `rm_oracle`.

```lean
example (x : UInt32) (h : x < 1000) : x + 1 ≤ 1000 := by
  rm_decide

example (x y : UInt8) (h1 : x < 10) (h2 : y < 10) : x + y < 20 := by
  rm_decide
```

The tactic:
1. Collects all hypotheses from the local context that are expressible in the supported fragment.
2. Negates the goal and assembles an SMT-LIB 2 script via `RmApi.Emit.buildScript`.
3. Sends the script to the solver.
4. On UNSAT: closes the goal with `rm_oracle`.
5. On SAT: prints the counter-example model and fails with a message showing which assignment falsifies the goal.
6. If the goal or a hypothesis is outside the supported fragment: logs a diagnostic and suggests `decide` or `omega` as fallbacks.

### `rm_decide_par (n)`

Like `rm_decide` but launches `n` independent solver threads racing on the same query (portfolio parallelism). Use when the goal is hard enough to benefit from diversity in heuristic choices:

```lean
example (x : BitVec 64) (h : x.toNat < 2^32) : (x &&& 0xFFFFFFFF#64) = x := by
  rm_decide_par (4)
```

The syntax takes a numeric literal for the worker count. The underlying `RmConfig` is `{ numWorkers := n }`.

### `rm_decide_all`

Closes **all current goals** in parallel in a single solver batch. Useful when a tactic sequence has left multiple open goals of the same kind:

```lean
example : (0 : UInt8) < 255 ∧ (1 : UInt8) < 255 ∧ (2 : UInt8) < 255 := by
  constructor <;> constructor
  all_goals rm_decide_all
```

Internally:
1. Translates each goal to an SMT script (goals outside the fragment are left open).
2. Submits all translatable scripts in one `solveBatch` call with 16 workers.
3. Goals that return UNSAT are closed with `rm_oracle`; the rest remain open for the next tactic.

### `rm_smt "..."`

Low-level escape hatch for when automatic translation is insufficient. Pass a complete SMT-LIB 2 script as a string literal; the goal is closed with `rm_oracle` if the script returns UNSAT:

```lean
example : True := by
  rm_smt "(set-logic QF_BV)
          (declare-const x (_ BitVec 8))
          (assert (bvult x (_ bv0 8)))
          (check-sat)"
```

The script must contain `(check-sat)`. The goal type is ignored for translation — `rm_oracle` closes whatever the current goal is. This is intentionally unchecked: if the script is SAT or the logic is wrong, the tactic fails with an error.

### Debugging tactics

Set `traceScript := true` in the config (requires calling `tryCloseGoal` directly) to see the emitted SMT-LIB 2 in the Lean infoview. Alternatively, use `rm_smt` with a hand-written script to bypass the translation layer.

---

## Supported Lean fragment

The `RmApi.Emit` layer translates a subset of Lean 4 expressions. Only goals and hypotheses that live entirely within this fragment are passed to the solver; others are silently dropped from the hypothesis set (they may still be used by other tactics in the same proof).

### Types

| Lean type | SMT sort | Logic |
|---|---|---|
| `Bool` | uninterpreted function | QF_UF |
| `UInt8`, `UInt16`, `UInt32`, `UInt64` | `(_ BitVec 8/16/32/64)` | QF_BV |
| `BitVec n` | `(_ BitVec n)` | QF_BV |
| `Int` | `Int` (linear arithmetic only) | QF_IDL |
| `Prop` connectives | SMT-LIB 2 core | (any) |

### Operators

| Lean | SMT-LIB 2 | Notes |
|---|---|---|
| `∧` / `∨` / `¬` | `and` / `or` / `not` | |
| `=` / `≠` | `=` / `(not (= ...))` | any supported sort |
| `+` / `-` / `*` | `bvadd` / `bvsub` / `bvmul` | bitvec; `+` on `Int` → linear arithmetic |
| `&&&` / `\|\|\|` / `^^^` | `bvand` / `bvor` / `bvxor` | bitvec |
| `<<< ` / `>>>` | `bvshl` / `bvlshr` | bitvec (logical shift right) |
| `<` / `≤` / `>` / `≥` | `bvult` / `bvule` / `bvugt` / `bvuge` | bitvec (unsigned); `<` on `Int` → `<` |

### Limitations

The following are **not** translated and cause the tactic to fall back or skip the hypothesis:

- `Nat` (use `UInt32`/`UInt64` or `omega` instead)
- `Float` / `Real` / non-linear arithmetic (`x * y` when both are variables)
- Recursive types, inductive types, type-class hypotheses
- Quantifiers (`∀`, `∃`) — the solver targets quantifier-free logics
- `String`, `List`, `Array`, and other data structures
- `Eq.mpr`, `cast`, coercions between numeric types (translate explicitly)

---

## Programmatic API

For incremental solving or use outside a tactic proof, the `RmApi.Basic` module exposes an imperative interface backed by the same C FFI:

```lean
import RmApi.Basic
open RmApi

def example : IO Unit := do
  let ctx ← RmContext.new
  let s   ← RmSolver.new ctx (numWorkers := 4) (maxConflicts := 0)

  -- Push a scope
  s.push

  -- Assert (x < 10 ∧ x > 5 ∧ x = 3)
  let x ← ctx.bitvecConst "x" 8
  -- (assertions built via RmExpr constructors or via solveSmtlib for text)
  s.assert x

  match ← s.check with
  | .unsat     => IO.println "UNSAT"
  | .sat model => IO.println s!"SAT: {← model.toString}"
  | .unknown r => IO.println s!"unknown: {r}"

  s.pop
```

### Types

| Type | Description |
|---|---|
| `RmContext` | Solver context — allocates constants, manages lifetime |
| `RmSolver` | Incremental solver — supports push/pop scope stack |
| `RmExpr` | Opaque expression handle (bitvec, int, or bool constant) |
| `RmModel` | Counter-example model — query variable assignments |
| `SatResult` | `.sat (model : RmModel)` / `.unsat` / `.unknown (reason : String)` |

All four handle types are wrapped in Lean's `ExternalObject` GC, so they are freed automatically when they go out of scope. Do not hold a reference to a `RmSolver` after its parent `RmContext` is freed.

### Key methods

```lean
-- Context
RmContext.new : IO RmContext

-- Solver
RmSolver.new (ctx : RmContext) (numWorkers : UInt32 := 1) (maxConflicts : UInt64 := 0) : IO RmSolver
RmSolver.assert (s : RmSolver) (e : RmExpr) : IO Unit
RmSolver.push   (s : RmSolver) : IO Unit
RmSolver.pop    (s : RmSolver) : IO Unit
RmSolver.check  (s : RmSolver) : IO SatResult

-- Model
RmModel.getBitvec (m : RmModel) (name : String) : IO (Option (UInt64 × UInt32))
RmModel.getInt    (m : RmModel) (name : String) : IO (Option Int)
RmModel.toString  (m : RmModel) : IO String

-- Text interface (no handle required)
solveSmtlib (script : String) (maxConflicts : UInt64 := 0) : IO (SatResult × String)
```

`solveSmtlib` is the primary entry point used internally by `rm_decide`. It accepts a complete SMT-LIB 2 script and returns a result plus a model string (in SMT-LIB 2 `get-model` format) when the result is SAT.

---

## Batch / proof farm API

For large-scale verification — thousands of independent proof obligations — use the batch interface to avoid per-call overhead:

```lean
import RmApi
open RmApi

def verifyAll (obligations : Array String) : IO Bool := do
  checkAllUnsat obligations (numWorkers := 64)

-- Or get structured results:
def verifyWithDiag (obligations : Array String) : IO (Array PoolResult) := do
  RmPool.solveAll obligations (numWorkers := 64)
```

### `solveBatch`

```lean
solveBatch (scripts : Array String) (numWorkers : UInt32 := 16)
           (maxConflicts : UInt64 := 0) : IO (Array UInt32)
```

Submits all scripts to a thread pool of `numWorkers` workers. Returns one result code per script in input order: `0` = SAT, `1` = UNSAT, `2` = UNKNOWN. This is the lowest-level batch API, used by all higher-level wrappers.

### `RmPool.solveAll`

```lean
RmPool.solveAll (scripts : Array String)
                (numWorkers : UInt32 := 16) (maxConflicts : UInt64 := 0)
                : IO (Array PoolResult)
```

Wraps `solveBatch` and returns `PoolResult` values (each has `.code` and `.index`) for easier pattern matching.

### `checkAllUnsat`

```lean
checkAllUnsat (scripts : Array String)
              (numWorkers : UInt32 := 64) (maxConflicts : UInt64 := 0)
              : IO Bool
```

Returns `true` iff every script in the array is UNSAT. The first non-UNSAT result short-circuits the verdict. Use this for batch proof checking where you only care about the aggregate.

### `openObligations`

```lean
openObligations (scripts : Array String)
                (numWorkers : UInt32 := 64) (maxConflicts : UInt64 := 0)
                : IO (Array Nat)
```

Returns the **indices** of scripts that are not conclusively UNSAT (SAT or UNKNOWN). An empty array means all obligations are proved.

### `rm_decide_all` tactic

The batch API is also available as a tactic. `rm_decide_all` collects all open goals in the current proof state, translates each to SMT, and submits them as a single batch. Goals that are proved UNSAT are closed; the rest remain open. Worker count is fixed at 16 (configured by editing the `solveBatch 16 0` call in `RmApi/Pool.lean` if needed).

### Scaling to distributed mode

Currently, `solveBatch` dispatches across threads on one machine. The distributed coordinator (future milestone) will expose the same `rm_solve_batch` C entry point over the network: Lean's `IO (Array UInt32)` return type is unchanged regardless of whether the pool is local or a 1000-node cluster.

---

## Soundness and the `rm_oracle` axiom

All tactics that close goals via the solver — `rm_decide`, `rm_decide_par`, `rm_decide_all`, and `rm_smt` — do so by applying the axiom:

```lean
axiom rm_oracle : ∀ (p : Prop), p
```

This axiom admits any `Prop` without proof. A proof that uses `rm_oracle` is **correct only to the degree that the ReasonMesh solver is correct** for the query it was given. ReasonMesh:

- Produces DRUP/LRAT proof certificates for every UNSAT verdict.
- The certificates are written to a `.rmproof` file and can be checked externally with a LRAT verifier (e.g. `lrat-check`).
- Future work: emit certificates in a form Lean's kernel can verify directly, eliminating `rm_oracle` entirely.

To audit which theorems in your project depend on `rm_oracle`:

```sh
grep -r "rm_oracle" .lake/build/
```

Or in Lean:

```lean
#print axioms myTheorem
-- output will include `RmApi.rm_oracle` if rm_decide was used
```

---

## C FFI layer

Advanced users who need to call the solver from C or from another language can link against `librm_api` directly. The header is at `crates/rm-api/include/rm_api.h`. The Lean FFI (`lean/ffi/rm_lean_ffi.c`) is the reference implementation showing the calling convention.

Key entry points exposed by `librm_api`:

| Function | Description |
|---|---|
| `rm_context_new() → rm_context_t*` | Create a solver context |
| `rm_context_free(ctx)` | Free a context and all associated resources |
| `rm_solver_new(ctx, workers, max_conflicts) → rm_solver_t*` | Create an incremental solver |
| `rm_solver_assert(s, expr)` | Add a constraint |
| `rm_solver_push(s)` / `rm_solver_pop(s)` | Scope stack |
| `rm_solver_check(s, &model) → int32_t` | Check sat; sets `*model` on SAT |
| `rm_solve_smtlib(script, budget, &model) → int32_t` | Single-shot text interface |
| `rm_solve_batch(scripts, n, workers, budget, results)` | Batch interface |
| `rm_model_get_bitvec(m, name, &bits, &width) → int` | Query bitvec variable |
| `rm_model_get_int(m, name, &val) → int` | Query integer variable |
| `rm_model_iter(m, callback, userdata)` | Iterate all assignments |
| `rm_model_free(m)` | Free a model |

Return codes: `RM_SAT = 0`, `RM_UNSAT = 1`, `RM_UNKNOWN = 2`.

The Lean wrapper (`rm_lean_ffi.c`) follows Lean 4's `@[extern]` calling convention: IO actions receive the world token as a final `lean_obj_arg` and return `lean_io_result_mk_ok(value)`. Opaque C pointers are wrapped in `lean_external_class` with typed finalizers so Lean's GC frees them at the right time.

---

## Troubleshooting

**`lake build` fails with "library not found for -lrm_api"`**

The shared library has not been built yet. Run `cargo build --release -p rm-api` from the repository root first.

**Tactic says "goal outside supported fragment"**

The goal contains a type or operator not in the table above. Common cases:
- `Nat` variables — use `UInt32` or `UInt64` instead, or use `omega`.
- `x * y` where both are variables — use `decide` for small finite types.
- Nested data structures — extract the relevant scalar subgoal manually.

**Counter-example printed but hard to read**

The model string is in SMT-LIB 2 `get-model` format: `(x #b00001010)(y #b00000011)`. Use `RmModel.getInt` or `RmModel.getBitvec` via the programmatic API for structured access.

**`rm_decide` is slow on a large goal**

Try `rm_decide_par (n)` with `n` equal to the number of available cores. For very large goals (thousands of clauses), consider using `rm_smt` with a hand-optimized script or the batch API to parallelize across multiple sub-goals.

**Proof uses `rm_oracle` — is it trustworthy?**

Yes, with the caveat that it trusts the solver. To get an independently verifiable certificate, run the solver with proof logging enabled (the `.rmproof` file) and check it with `lrat-check`. Full kernel-level certificate checking is planned for a future release.
