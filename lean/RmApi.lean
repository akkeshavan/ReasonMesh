/-!
# RmApi — ReasonMesh solver library for Lean 4

Provides:
- `rm_decide`         — close a QF_BV / QF_IDL / QF_UF goal using ReasonMesh
- `rm_decide_par (n)` — same but races n portfolio workers
- `rm_decide_all`     — close all current goals in parallel (proof farm)
- `rm_smt "..."`      — close a goal via a hand-written SMT-LIB 2 script
- `RmPool.solveAll`   — batch solver for non-tactic use (e.g. program verification)

## Usage

```lean
import RmApi

-- Close a bitvector goal automatically:
example (x : UInt8) (h : x < 200) : x + 1 ≤ 200 := by
  rm_decide

-- Pass a raw SMT-LIB 2 script:
example : True := by
  rm_smt "(set-logic QF_BV)
          (declare-const x (_ BitVec 8))
          (assert (not (bvult x #x00)))
          (check-sat)"

-- Close multiple goals in parallel:
example (a b : UInt32) (h1 : a < b) (h2 : b < 100) : a < 100 ∧ b < 100 := by
  constructor
  · rm_decide_all
  · rm_decide_all
```

## Soundness

`rm_decide` closes goals via `RmApi.rm_oracle`, an axiom that trusts the
solver's UNSAT verdict.  Search `#check @RmApi.rm_oracle` to audit usage.
Eliminate the axiom entirely by verifying LRAT certificates (future milestone).
-/

import RmApi.Basic
import RmApi.Emit
import RmApi.Tactic
import RmApi.Pool
