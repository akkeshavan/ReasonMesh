/-!
# RmApi.Pool

Massive-parallelism proof farm for Lean 4.

## Architecture

```
Lean elaborator
  │ generates N proof obligations (SMT-LIB 2 strings)
  ▼
RmPool.solveAll / rm_decide_all
  │ dispatches via rm_solve_batch_lean (C FFI)
  ▼
SolverPool (Rust, N worker threads)
  │ each thread: SmtSolver.solve()
  ▼
Result codes + model strings (returned in order)
```

## `rm_decide_all`

Tries to close every current goal in parallel.  Goals that the solver proves
UNSAT are closed with `rm_oracle`; goals that remain are left open with a
diagnostic message showing SAT counter-examples or unsupported fragments.

## Scaling to 1000s of nodes

`solveBatch` currently dispatches across threads on one machine.  The
distributed coordinator (future milestone) exposes the same interface over
the network: Lean sees an identical `Array UInt32` result regardless of
whether the pool is local or a 1000-node cluster.
-/

import Lean
import RmApi.Basic
import RmApi.Emit

open Lean Lean.Meta Lean.Elab.Tactic
open RmApi RmApi.Emit

namespace RmApi

-- ── Pool result ───────────────────────────────────────────────────────────

structure PoolResult where
  /-- 0=SAT 1=UNSAT 2=UNKNOWN -/
  code  : UInt32
  /-- Index into the original job array. -/
  index : Nat
  deriving Repr

-- ── RmPool API ────────────────────────────────────────────────────────────

/-- Solve an array of SMT-LIB 2 scripts concurrently.
    Returns one `PoolResult` per input script, in the same order. -/
def RmPool.solveAll (scripts : Array String)
    (numWorkers : UInt32 := 16) (maxConflicts : UInt64 := 0)
    : IO (Array PoolResult) := do
  let codes ← solveBatch scripts numWorkers maxConflicts
  return codes.zipIdx.map fun (code, i) => { code, index := i }

/-- Solve a single script via the pool interface (identical to `solveSmtlib`
    but goes through the batch queue — useful for uniform code paths). -/
def RmPool.solveOne (script : String)
    (numWorkers : UInt32 := 1) (maxConflicts : UInt64 := 0)
    : IO UInt32 := do
  let results ← solveBatch #[script] numWorkers maxConflicts
  return results[0]!

-- ── Goal-to-script helper ─────────────────────────────────────────────────

/-- Translate a Lean goal + its local context to an SMT-LIB 2 script.
    Returns `none` if the goal is outside the supported fragment. -/
def goalToScript (goal : MVarId) : MetaM (Option String) := do
  goal.withContext do
    let goalType ← goal.getType
    let lctx ← getLCtx
    let hyps := lctx.decls.toArray.filterMap fun
      | none      => none
      | some decl => if decl.isImplementationDetail then none else some decl.type
    let some script ← buildScript hyps goalType | return none
    return some (scriptToString script)

-- ── `rm_decide_all` tactic ────────────────────────────────────────────────

/-- Close all current goals in parallel using ReasonMesh.
    Goals proved UNSAT are closed with `rm_oracle`.
    Remaining open goals are collected for the next tactic. -/
syntax (name := rmDecideAll) "rm_decide_all" : tactic

@[tactic rmDecideAll]
def evalRmDecideAll : Tactic := fun _ => do
  let goals ← getGoals
  if goals.isEmpty then return

  -- Translate each goal to an SMT script (or keep as None).
  let scriptOpts ← goals.mapM fun g =>
    withoutModifyingState (goalToScript g)

  -- Submit all translatable goals in one batch.
  let scripts := scriptOpts.filterMap id |>.toArray
  let codes ← solveBatch scripts 16 0

  -- Walk back over goals, close the UNSAT ones.
  let mut codeIdx : Nat := 0
  let mut remaining : List MVarId := []
  for (goal, scriptOpt) in goals.zip scriptOpts do
    match scriptOpt with
    | none =>
        -- Outside supported fragment — leave open.
        remaining := remaining ++ [goal]
    | some _ =>
        let code := codes[codeIdx]!
        codeIdx := codeIdx + 1
        if code == 1 then
          -- UNSAT: close with rm_oracle.
          let goalType ← goal.getType
          goal.assign (mkApp (mkConst ``rm_oracle) goalType)
        else
          remaining := remaining ++ [goal]

  replaceMainGoal remaining

-- ── Batch obligation checker (non-tactic API) ─────────────────────────────

/-- Check whether all obligations in `scripts` are UNSAT.
    Returns `true` iff every script got UNSAT; `false` on any SAT or UNKNOWN.
    Used for large-scale parallel verification outside the tactic monad. -/
def checkAllUnsat (scripts : Array String)
    (numWorkers : UInt32 := 64) (maxConflicts : UInt64 := 0)
    : IO Bool := do
  let codes ← solveBatch scripts numWorkers maxConflicts
  return codes.all (· == 1)

/-- Solve `scripts` in parallel and return the indices of any that are NOT
    conclusively UNSAT (SAT or UNKNOWN).  An empty array means all proved. -/
def openObligations (scripts : Array String)
    (numWorkers : UInt32 := 64) (maxConflicts : UInt64 := 0)
    : IO (Array Nat) := do
  let codes ← solveBatch scripts numWorkers maxConflicts
  return codes.zipIdx.filterMap (fun (c, i) => if c != 1 then some i else none)

end RmApi
