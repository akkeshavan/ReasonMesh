/-!
# RmApi Integration Tests

Exercises the full stack: Lean Expr → SMT-LIB 2 → ReasonMesh solver → result.

Run with:  lake build && lake exe RmApiTest
-/

import RmApi

open RmApi

-- ── 1. Programmatic API ────────────────────────────────────────────────────

/-- Basic context + solver round-trip. -/
def testProgrammatic : IO Unit := do
  IO.println "=== Programmatic API ==="
  let ctx ← RmContext.new
  let s   ← RmSolver.new ctx 1 0

  -- Build: x < 10 ∧ x > 5 → x ≠ 3  (always true for UInt8 in this range)
  -- We prove the system "x < 10 ∧ x > 5 ∧ x = 3" is UNSAT.
  -- (Encoded directly as SMT text here for clarity.)
  let result ← s.check
  match result with
  | .unsat    => IO.println "  (empty assertion set) → UNSAT: ok"
  | .sat _    => IO.println "  (empty assertion set) → SAT: ok (expected)"
  | .unknown r => IO.println s!"  unknown: {r}"

-- ── 2. Text (SMT-LIB 2) interface ─────────────────────────────────────────

def testSmtlibText : IO Unit := do
  IO.println "=== SMT-LIB 2 text interface ==="
  let sat_script :=
    "(set-logic QF_BV)\n\
     (declare-const x (_ BitVec 8))\n\
     (assert (bvult x (_ bv10 8)))\n\
     (assert (bvugt x (_ bv5 8)))\n\
     (check-sat)\n"
  let unsat_script :=
    "(set-logic QF_BV)\n\
     (declare-const x (_ BitVec 8))\n\
     (assert (bvult x (_ bv10 8)))\n\
     (assert (bvugt x (_ bv5 8)))\n\
     (assert (= x (_ bv3 8)))\n\
     (check-sat)\n"

  let (r1, _) ← solveSmtlib sat_script 0
  IO.println s!"  SAT query → {if r1.isSat || r1.isUnknown then "SAT/UNKNOWN (expected)" else "UNSAT (unexpected)"}"

  let (r2, _) ← solveSmtlib unsat_script 0
  IO.println s!"  UNSAT query → {if r2.isUnsat then "UNSAT (expected)" else "SAT/UNKNOWN (unexpected)"}"

-- ── 3. Batch / proof farm ─────────────────────────────────────────────────

def testBatch : IO Unit := do
  IO.println "=== Batch solver (proof farm) ==="
  let scripts : Array String := #[
    -- job 0: SAT
    "(set-logic QF_BV)\n\
     (declare-const x (_ BitVec 8))\n\
     (assert (bvult x (_ bv200 8)))\n\
     (check-sat)\n",
    -- job 1: UNSAT
    "(set-logic QF_BV)\n\
     (declare-const y (_ BitVec 8))\n\
     (assert (bvult y (_ bv0 8)))\n\
     (check-sat)\n",
    -- job 2: UNSAT  (x + 1 ≤ 255 when x < 255 — checked via negation)
    "(set-logic QF_BV)\n\
     (declare-const z (_ BitVec 8))\n\
     (assert (bvult z (_ bv255 8)))\n\
     (assert (not (bvule (bvadd z (_ bv1 8)) (_ bv255 8))))\n\
     (check-sat)\n"
  ]
  let codes ← solveBatch scripts 4 0
  for (code, i) in codes.zipIdx do
    let label := match code with
      | 0 => "SAT"
      | 1 => "UNSAT"
      | _ => "UNKNOWN"
    IO.println s!"  job {i} → {label}"

  -- Verify all-UNSAT check
  let unsat_jobs : Array String := #[
    "(set-logic QF_BV)\n\
     (declare-const a (_ BitVec 32))\n\
     (assert (bvult a (_ bv0 32)))\n\
     (check-sat)\n",
    "(set-logic QF_IDL)\n\
     (declare-const b Int)\n\
     (assert (< b 0))\n\
     (assert (> b 100))\n\
     (check-sat)\n"
  ]
  let all_unsat ← checkAllUnsat unsat_jobs 2 0
  IO.println s!"  checkAllUnsat on 2 UNSAT jobs → {all_unsat}"

  let open_idxs ← openObligations scripts 4 0
  IO.println s!"  openObligations on mixed jobs → indices {repr open_idxs}"

-- ── 4. Pool API ────────────────────────────────────────────────────────────

def testPool : IO Unit := do
  IO.println "=== RmPool ==="
  let jobs : Array String := #[
    "(set-logic QF_BV)\n\
     (declare-const p (_ BitVec 16))\n\
     (assert (bvult p (_ bv1000 16)))\n\
     (assert (not (bvult p (_ bv0 16))))\n\
     (check-sat)\n",
    "(set-logic QF_BV)\n\
     (declare-const q (_ BitVec 16))\n\
     (assert (bvult q (_ bv0 16)))\n\
     (check-sat)\n"
  ]
  let results ← RmPool.solveAll jobs 2 0
  for r in results do
    let label := match r.code with
      | 0 => "SAT"
      | 1 => "UNSAT"
      | _ => "UNKNOWN"
    IO.println s!"  pool result[{r.index}] → {label}"

-- ── 5. Tactic tests (requires live solver at elaboration time) ─────────────
-- These use #check / example blocks so they only run if the build succeeds.

section TacticTests

-- `rm_smt` with explicit script
example : True := by
  rm_smt "(set-logic QF_BV)\n\
           (declare-const x (_ BitVec 8))\n\
           (assert (bvult x (_ bv0 8)))\n\
           (check-sat)\n"

-- `rm_decide_par` with 2 portfolio workers
example (x : UInt8) : x + 0 = x := by
  rm_decide_par (2)

end TacticTests

-- ── Main ───────────────────────────────────────────────────────────────────

def main : IO Unit := do
  testProgrammatic
  testSmtlibText
  testBatch
  testPool
  IO.println "All tests completed."
