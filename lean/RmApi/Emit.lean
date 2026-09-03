/-!
# RmApi.Emit

Translates a fragment of Lean 4 `Expr` into an SMT-LIB 2 script.

## Supported fragment

| Lean type       | SMT logic | Notes                           |
|-----------------|-----------|---------------------------------|
| `Bool`          | QF_UF     | Bool ops → `and`/`or`/`not`    |
| `UInt8/16/32/64`| QF_BV     | Arithmetic wraps mod 2^n        |
| `BitVec n`      | QF_BV     | n must be a numeric literal     |
| `Int`           | QF_IDL    | Difference-logic constraints    |
| `Prop` connectives | same   | `And`, `Or`, `Not`, `Eq`, `Ne` |

Unsupported sub-expressions cause `emitExpr` to return `none`; the tactic
then falls through to `decide` or reports the gap.
-/

import Lean

open Lean Lean.Meta

namespace RmApi.Emit

-- ── Sort detection ────────────────────────────────────────────────────────

inductive SmtSort
  | bool
  | bitvec (width : Nat)
  | int_
  deriving Repr, BEq

def SmtSort.smtlib : SmtSort → String
  | .bool      => "Bool"
  | .bitvec w  => s!"(_ BitVec {w})"
  | .int_      => "Int"

/-- Logic name appropriate for the given set of sorts. -/
def logicOf (sorts : Array SmtSort) : String :=
  if sorts.any (· matches .bitvec _) then "QF_BV"
  else if sorts.any (· == .int_)     then "QF_IDL"
  else                                     "QF_UF"

/-- Map a Lean type expression to an SMT sort, or `none` for unsupported types. -/
def sortOfType (ty : Expr) : MetaM (Option SmtSort) := do
  let ty ← whnf ty
  match ty with
  | .const ``Bool _   => return some .bool
  | .const ``UInt8 _  => return some (.bitvec 8)
  | .const ``UInt16 _ => return some (.bitvec 16)
  | .const ``UInt32 _ => return some (.bitvec 32)
  | .const ``UInt64 _ => return some (.bitvec 64)
  | .const ``Int _    => return some .int_
  | .app (.const ``BitVec _) w => do
      let w ← whnf w
      match w with
      | .lit (.natVal n) => return some (.bitvec n)
      | _ => return none
  | _ => return none

-- ── Emission state ────────────────────────────────────────────────────────

structure EmitState where
  /-- Declared constants: `(name, sort)`. -/
  decls  : Array (String × SmtSort) := #[]
  /-- Free variable ids already declared. -/
  seen   : FVarIdSet := {}

abbrev EmitM := StateRefT EmitState MetaM

def declareVar (name : String) (sort : SmtSort) : EmitM Unit := do
  modify fun s => { s with decls := s.decls.push (name, sort) }

def declareIfNew (fid : FVarId) (name : String) (sort : SmtSort) : EmitM Unit := do
  let seen := (← get).seen
  if !seen.contains fid then do
    modify fun s => { s with seen := s.seen.insert fid }
    declareVar name sort

-- ── Expression emission ───────────────────────────────────────────────────

/-- Return the bitvec width implied by a Lean type, or 0 for non-BV types. -/
private def bvWidth (ty : Expr) : MetaM Nat := do
  match ← sortOfType ty with
  | some (.bitvec w) => return w
  | _ => return 0

/-- Emit a numeric literal of the given SMT sort. -/
private def emitLit (n : Nat) (sort : SmtSort) : String :=
  match sort with
  | .bitvec w => s!"(_ bv{n} {w})"
  | .int_     => toString n
  | .bool     => if n == 0 then "false" else "true"

private def binop (op : String) (a b : String) : String := s!"({op} {a} {b})"
private def unop  (op : String) (a : String)   : String := s!"({op} {a})"

/-- Core recursive translator.  Returns `none` for unsupported sub-expressions. -/
partial def emitExpr (e : Expr) : EmitM (Option String) := do
  let e ← liftM (whnf e)
  match e with

  -- ── Prop / Bool leaves ─────────────────────────────────────────────────
  | .const ``True  _ => return some "true"
  | .const ``False _ => return some "false"

  -- ── Bool constructors ──────────────────────────────────────────────────
  | .const ``Bool.true  _ => return some "true"
  | .const ``Bool.false _ => return some "false"

  -- ── Free variables ─────────────────────────────────────────────────────
  | .fvar fid => do
      let decl ← fid.getDecl
      let name := decl.userName.toString
      match ← liftM (sortOfType decl.type) with
      | none      => return none
      | some sort => do
          declareIfNew fid name sort
          return some name

  -- ── Prop connectives ───────────────────────────────────────────────────
  | .app (.const ``Not _) p =>
      return (← emitExpr p).map (unop "not")

  | .app (.app (.const ``And _) p) q =>
      return optBin "and" (← emitExpr p) (← emitExpr q)

  | .app (.app (.const ``Or _) p) q =>
      return optBin "or" (← emitExpr p) (← emitExpr q)

  | .app (.app (.const ``Iff _) p) q =>
      return optBin "=" (← emitExpr p) (← emitExpr q)

  -- ── Equality / Inequality ──────────────────────────────────────────────
  | .app (.app (.app (.const ``Eq _) _) a) b =>
      return optBin "=" (← emitExpr a) (← emitExpr b)

  | .app (.app (.app (.const ``Ne _) _) a) b =>
      return optBin "distinct" (← emitExpr a) (← emitExpr b)

  -- ── Bool.and / Bool.or / Bool.not ─────────────────────────────────────
  | .app (.app (.const ``Bool.and _) a) b =>
      return optBin "and" (← emitExpr a) (← emitExpr b)

  | .app (.app (.const ``Bool.or _) a) b =>
      return optBin "or" (← emitExpr a) (← emitExpr b)

  | .app (.const ``Bool.not _) a =>
      return (← emitExpr a).map (unop "not")

  -- ── Numeric literals ───────────────────────────────────────────────────
  | .lit (.natVal n) => return some (toString n)

  | .app (.app (.const ``OfNat.ofNat _) ty)
        (.app (.app (.const ``instOfNatNat _) _) (.lit (.natVal n))) => do
      match ← liftM (sortOfType ty) with
      | some sort => return some (emitLit n sort)
      | none      => return none

  -- UInt literal: UInt8.mk (Fin.mk n _) after whnf
  | .app (.const ``UInt8.mk _)
        (.app (.app (.const ``Fin.mk _) (.lit (.natVal n))) _) =>
      return some (emitLit n (.bitvec 8))
  | .app (.const ``UInt16.mk _)
        (.app (.app (.const ``Fin.mk _) (.lit (.natVal n))) _) =>
      return some (emitLit n (.bitvec 16))
  | .app (.const ``UInt32.mk _)
        (.app (.app (.const ``Fin.mk _) (.lit (.natVal n))) _) =>
      return some (emitLit n (.bitvec 32))
  | .app (.const ``UInt64.mk _)
        (.app (.app (.const ``Fin.mk _) (.lit (.natVal n))) _) =>
      return some (emitLit n (.bitvec 64))

  -- ── Arithmetic: HAdd/HSub/HMul (UInt → bv*, Int → +/-/*) ────────────
  | .app (.app (.app (.app (.app (.const ``HAdd.hAdd _) ty) _) _) _) a |>
        (fun e => match e with
         | .app prev b => some (prev, a, b)
         | _ => none) => do
      if let some (prev, a, b) := e.app? then
        let op ← bvOrArithOp ty "bvadd" "+"
        return optBin op (← emitExpr a) (← emitExpr b)
      return none

  | _ => emitBinaryArith e

where
  optBin (op : String) : Option String → Option String → Option String
    | some a, some b => some (binop op a b)
    | _, _ => none

/-- Handle HAdd/HSub/HMul/HAnd/HOr/HXor/comparison and shift ops. -/
private def emitBinaryArith (e : Expr) : EmitM (Option String) := do
  -- Pattern: f _ _ _ _ a b  where f has 6 args (typeclass-dispatched binary op)
  let some (f6, b) := e.app? | return none
  let some (f5, a) := f6.app? | return none
  let some (f4, _) := f5.app? | return none  -- inst
  let some (f3, _) := f4.app? | return none  -- out type
  let some (f2, ty) := f3.app? | return none -- rhs type / gives us the sort
  let some (f1, _) := f2.app? | return none  -- lhs type
  let .const name _ := f1 | return none
  let width ← liftM (bvWidth ty)
  let sa ← emitExpr a
  let sb ← emitExpr b
  match name with
  | ``HAdd.hAdd  => return optBin (if width > 0 then "bvadd" else "+")  sa sb
  | ``HSub.hSub  => return optBin (if width > 0 then "bvsub" else "-")  sa sb
  | ``HMul.hMul  => return optBin (if width > 0 then "bvmul" else "*")  sa sb
  | ``HAnd.hAnd  => return optBin "bvand"  sa sb
  | ``HOr.hOr    => return optBin "bvor"   sa sb
  | ``HXor.hXor  => return optBin "bvxor"  sa sb
  | ``HShiftLeft.hShiftLeft  => return optBin "bvshl"  sa sb
  | ``HShiftRight.hShiftRight => return optBin "bvlshr" sa sb
  -- Comparisons (5 args, not 6 — missing out type)
  | _ => emitComparison e

private def emitComparison (e : Expr) : EmitM (Option String) := do
  -- Pattern: f _ _ _ a b  (5-arg typeclass comparison)
  let some (f5, b) := e.app? | return none
  let some (f4, a) := f5.app? | return none
  let some (f3, _) := f4.app? | return none  -- inst
  let some (f2, ty) := f3.app? | return none
  let some (f1, _) := f2.app? | return none
  let .const name _ := f1 | return none
  let width ← liftM (bvWidth ty)
  let bv    := width > 0
  let sa ← emitExpr a
  let sb ← emitExpr b
  match name with
  | ``LT.lt => return optBin (if bv then "bvult" else "<")  sa sb
  | ``LE.le => return optBin (if bv then "bvule" else "<=") sa sb
  | ``GT.gt => return optBin (if bv then "bvugt" else ">")  sa sb
  | ``GE.ge => return optBin (if bv then "bvuge" else ">=") sa sb
  | _ => return none

private def bvOrArithOp (ty : Expr) (bvOp arithOp : String) : MetaM String := do
  match ← sortOfType ty with
  | some (.bitvec _) => return bvOp
  | _                => return arithOp

private def optBin (op : String) : Option String → Option String → Option String
  | some a, some b => some s!"({op} {a} {b})"
  | _, _ => none

-- ── Script assembly ───────────────────────────────────────────────────────

structure SmtScript where
  logic      : String
  assertions : Array String
  decls      : Array (String × SmtSort)

/-- Build an SMT-LIB 2 script from an array of Lean propositions.
    Prepends `(assert (not goal))` for the last element (the negated goal). -/
def buildScript (hyps : Array Expr) (negGoal : Expr) : MetaM (Option SmtScript) := do
  let (hyp_terms, st1) ← (hyps.mapM emitExpr).run {}
  if hyp_terms.any Option.isNone then return none
  let (goal_term, st2) ← (emitExpr negGoal).run st1
  let goal_s ← goal_term
  let all_decls := st2.decls
  let logic := logicOf (all_decls.map Prod.snd)
  let assertions := hyp_terms.filterMap id ++ #[s!"(not {goal_s})"]
  return some { logic, assertions, decls := all_decls }

def scriptToString (s : SmtScript) : String :=
  let header := s!"(set-logic {s.logic})\n"
  let decls  := s.decls.foldl (fun acc (n, sort) =>
    acc ++ s!"(declare-const {n} {sort.smtlib})\n") ""
  let asserts := s.assertions.foldl (fun acc a =>
    acc ++ s!"(assert {a})\n") ""
  header ++ decls ++ asserts ++ "(check-sat)\n"

end RmApi.Emit
