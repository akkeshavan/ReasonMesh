/-!
# RmApi.Basic

Opaque Lean types wrapping the C FFI handles, plus the low-level `@[extern]`
declarations that bind to `rm_lean_ffi.c`.

All heap-allocated C objects are managed by Lean's GC via the
`lean_external_class` finalizer registered in `rm_lean_initialize`.
-/

namespace RmApi

-- ── Initialization ────────────────────────────────────────────────────────

/-- Register C finalizers on library load. Must be called before any other
    RmApi function. Lake wires this automatically via `initialize`. -/
@[extern "rm_lean_initialize"]
private opaque initialize_ : Bool → IO Unit

initialize initialize_ true

-- ── Opaque handle types ───────────────────────────────────────────────────

private opaque RmContextPointed : NonemptyType
/-- An SMT context: factory for expressions and solver sessions.
    Managed by Lean's GC; no explicit free needed. -/
def RmContext := RmContextPointed.type
instance : Nonempty RmContext := RmContextPointed.property

private opaque RmSolverPointed : NonemptyType
/-- An incremental solver session with push/pop scopes. -/
def RmSolver := RmSolverPointed.type
instance : Nonempty RmSolver := RmSolverPointed.property

private opaque RmExprPointed : NonemptyType
/-- A solver expression (Bool, Int, or BitVec). -/
def RmExpr := RmExprPointed.type
instance : Nonempty RmExpr := RmExprPointed.property

private opaque RmModelPointed : NonemptyType
/-- A satisfying assignment returned when the solver finds SAT. -/
def RmModel := RmModelPointed.type
instance : Nonempty RmModel := RmModelPointed.property

-- ── Result type ───────────────────────────────────────────────────────────

/-- The outcome of a solver check call. -/
inductive SatResult where
  | sat     (model : RmModel)  : SatResult
  | unsat                      : SatResult
  | unknown (reason : String)  : SatResult
  deriving Repr

def SatResult.isSat     : SatResult → Bool | .sat _    => true | _ => false
def SatResult.isUnsat   : SatResult → Bool | .unsat    => true | _ => false
def SatResult.isUnknown : SatResult → Bool | .unknown _ => true | _ => false

def SatResult.model? : SatResult → Option RmModel
  | .sat m => some m
  | _      => none

-- ── Context ───────────────────────────────────────────────────────────────

@[extern "rm_context_new_lean"]
opaque RmContext.new : IO RmContext

-- ── Solver ────────────────────────────────────────────────────────────────

/-- Create a solver.  `numWorkers` independent threads race on each `check`
    call; `maxConflicts = 0` means unlimited CDCL budget. -/
@[extern "rm_solver_new_lean"]
opaque RmSolver.new (ctx : RmContext) (numWorkers : UInt32 := 1)
                    (maxConflicts : UInt64 := 0) : IO RmSolver

@[extern "rm_solver_assert_lean"]
opaque RmSolver.assert (s : RmSolver) (e : RmExpr) : IO Unit

@[extern "rm_solver_push_lean"]
opaque RmSolver.push (s : RmSolver) : IO Unit

@[extern "rm_solver_pop_lean"]
opaque RmSolver.pop (s : RmSolver) : IO Unit

/-- Internal: returns (code, Option RmModel). Use `RmSolver.check` instead. -/
@[extern "rm_solver_check_lean"]
private opaque RmSolver.checkImpl (s : RmSolver) : IO (UInt32 × Option RmModel)

def RmSolver.check (s : RmSolver) : IO SatResult := do
  let (code, mopt) ← s.checkImpl
  match code with
  | 0 => return .sat (mopt.get!)
  | 1 => return .unsat
  | _ => return .unknown "solver returned unknown"

-- ── Model ─────────────────────────────────────────────────────────────────

/-- Look up a bit-vector variable. Returns `(bits, width)` or `none`. -/
@[extern "rm_model_get_bitvec_lean"]
opaque RmModel.getBitvec (m : RmModel) (name : @& String)
    : IO (Option (UInt64 × UInt32))

/-- Look up an integer variable. -/
@[extern "rm_model_get_int_lean"]
opaque RmModel.getInt (m : RmModel) (name : @& String) : IO (Option Int)

/-- Return all assignments as an SMT-LIB `(name value)` string. -/
@[extern "rm_model_to_string_lean"]
opaque RmModel.toString (m : RmModel) : IO String

-- ── Text interface ────────────────────────────────────────────────────────

/-- Solve an SMT-LIB 2 script.  Returns `(code, modelString)` where
    `code` is 0=SAT 1=UNSAT 2=UNKNOWN and `modelString` is non-empty on SAT. -/
@[extern "rm_solve_smtlib_lean"]
opaque solveSmtlibRaw (script : @& String) (maxConflicts : UInt64 := 0)
    : IO (UInt32 × String)

def solveSmtlib (script : String) (maxConflicts : UInt64 := 0)
    : IO (SatResult × String) := do
  let (code, model) ← solveSmtlibRaw script maxConflicts
  let r := match code with
           | 0 => .unknown "SAT (use programmatic API for model access)"
           | 1 => .unsat
           | _ => .unknown "solver returned unknown"
  return (r, model)

-- ── Batch / proof farm ────────────────────────────────────────────────────

/-- Solve `scripts` concurrently using `numWorkers` threads.
    Returns result codes in submission order (0=SAT 1=UNSAT 2=UNKNOWN). -/
@[extern "rm_solve_batch_lean"]
opaque solveBatch (scripts : @& Array String) (numWorkers : UInt32 := 16)
    (maxConflicts : UInt64 := 0) : IO (Array UInt32)

end RmApi
