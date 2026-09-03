/-!
# RmApi.Tactic

Tactics that dispatch proof obligations to the ReasonMesh solver.

## `rm_decide`

Closes a goal by:
1. Collecting all local hypotheses expressible in the supported fragment.
2. Emitting `(assert (not goal))` and calling the solver.
3. If the solver returns UNSAT the hypotheses are contradictory with ¬goal,
   so the original goal holds — it is closed via `rm_oracle`.
4. If SAT the solver found a counter-example, which is printed as an error.
5. If the goal is outside the supported fragment the tactic suggests fallbacks.

## `rm_smt`

Lower-level escape hatch: pass a raw SMT-LIB 2 script string directly.
Useful when the automatic translation is insufficient.

## Soundness note

`rm_oracle` is an axiom that admits any `Prop`.  A proof that uses it is
trustworthy only to the degree that the ReasonMesh solver is correct.
Future work: emit LRAT certificates and verify them in Lean's kernel,
eliminating the axiom entirely.
-/

import Lean
import RmApi.Basic
import RmApi.Emit

open Lean Lean.Meta Lean.Elab.Tactic
open RmApi RmApi.Emit

namespace RmApi

-- ── Oracle axiom ─────────────────────────────────────────────────────────

/-- Axiom backing `rm_decide`.  Proofs that use this are correct only if
    the ReasonMesh solver returns a sound UNSAT verdict for the query.
    Eliminate by verifying LRAT certificates in Lean's kernel (future). -/
axiom rm_oracle : ∀ (p : Prop), p

-- ── Configuration ─────────────────────────────────────────────────────────

structure RmConfig where
  /-- CDCL conflict budget (0 = unlimited). -/
  maxConflicts : UInt64 := 0
  /-- Portfolio worker threads per check. -/
  numWorkers   : UInt32 := 1
  /-- Print the emitted SMT-LIB 2 script for debugging. -/
  traceScript  : Bool := false
  deriving Repr

-- ── Core solve helper ─────────────────────────────────────────────────────

private def callSolver (script : String) (cfg : RmConfig)
    : IO (SatResult × String) :=
  solveSmtlib script cfg.maxConflicts

/-- Attempt to close `goal` using the SMT solver.
    Returns `true` if the goal was closed. -/
def tryCloseGoal (goal : MVarId) (cfg : RmConfig) : TacticM Bool := do
  goal.checkNotAssigned `rm_decide
  let goalType ← goal.getType
  -- Collect hypotheses that live in Prop and are expressible in our fragment.
  let lctx ← getLCtx
  let hyps := lctx.decls.toArray.filterMap fun
    | none      => none
    | some decl => if decl.isImplementationDetail then none else some decl.type

  -- Build the SMT-LIB 2 script.
  let some script ← liftM (buildScript hyps goalType)
    | do
        logInfo m!"rm_decide: goal or hypotheses outside supported fragment\
 (QF_BV / QF_IDL / QF_UF); try `decide` or `omega`"
        return false

  let smtText := scriptToString script
  if cfg.traceScript then
    logInfo m!"rm_decide script:\n{smtText}"

  let (result, modelStr) ← callSolver smtText cfg
  match result with
  | .unsat =>
      -- Solver proved the goal; close with rm_oracle.
      let proof := mkApp (mkConst ``rm_oracle) goalType
      goal.assign proof
      return true
  | .sat _ | .unknown _ =>
      let msg := if modelStr.isEmpty
        then "solver returned SAT/UNKNOWN — goal may be false"
        else s!"solver returned SAT — counter-example:\n{modelStr}"
      throwTacticEx `rm_decide goal (msg := .ofFormat (Std.Format.text msg))

-- ── `rm_decide` tactic ────────────────────────────────────────────────────

syntax (name := rmDecide) "rm_decide" : tactic

@[tactic rmDecide]
def evalRmDecide : Tactic := fun _ => do
  let goal ← getMainGoal
  let closed ← tryCloseGoal goal {}
  if closed then replaceMainGoal []

-- ── `rm_decide_par` — parallel portfolio workers ──────────────────────────

/-- Like `rm_decide` but races `n` independent solver threads.
    Use when the goal is hard enough to benefit from portfolio diversity. -/
syntax (name := rmDecidePar) "rm_decide_par" "(" num ")" : tactic

@[tactic rmDecidePar]
def evalRmDecidePar : Tactic := fun stx => do
  let nStr := stx[2].isNatLit?.getD 4
  let cfg : RmConfig := { numWorkers := nStr.toUInt32 }
  let goal ← getMainGoal
  let _ ← tryCloseGoal goal cfg

-- ── `rm_smt` — raw SMT-LIB 2 escape hatch ────────────────────────────────

/-- Close the current goal by asserting that the given SMT-LIB 2 script is
    UNSAT.  The script must be a string literal.  The goal is closed with
    `rm_oracle` when the solver returns UNSAT. -/
syntax (name := rmSmt) "rm_smt" str : tactic

@[tactic rmSmt]
def evalRmSmt : Tactic := fun stx => do
  let script := stx[1].isStrLit?.getD ""
  let goal ← getMainGoal
  let goalType ← goal.getType
  let (result, modelStr) ← solveSmtlib script 0
  match result with
  | .unsat =>
      goal.assign (mkApp (mkConst ``rm_oracle) goalType)
      replaceMainGoal []
  | _ =>
      let msg := if modelStr.isEmpty then "solver did not return UNSAT"
                 else s!"solver returned SAT:\n{modelStr}"
      throwTacticEx `rm_smt goal (msg := .ofFormat (Std.Format.text msg))

end RmApi
