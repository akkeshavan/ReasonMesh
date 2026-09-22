#!/usr/bin/env python3
"""Generate SMT2 benchmark suite covering QF_BV, QF_UF, QF_IDL, QF_LIA."""

import os, random, textwrap
from pathlib import Path

ROOT = Path(__file__).parent.parent / "benchmarks" / "smt"
random.seed(42)

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def write(path: Path, content: str):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(textwrap.dedent(content).strip() + "\n")


def smt2(logic: str, decls: str, asserts: str, expected: str, comment: str = "") -> str:
    header = f"; expected: {expected}"
    if comment:
        header += f"  [{comment}]"
    return f"""{header}
(set-logic {logic})
{decls.strip()}
{asserts.strip()}
(check-sat)
"""

# ---------------------------------------------------------------------------
# QF_BV — bit-vector arithmetic
# ---------------------------------------------------------------------------

bv_dir = ROOT / "qf_bv"

# 1. Simple satisfiable: x + y = 10 (8-bit)
write(bv_dir / "add_eq_sat.smt2", smt2("QF_BV", """
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
""", """
(assert (= (bvadd x y) (_ bv10 8)))
(assert (bvugt x (_ bv0 8)))
(assert (bvugt y (_ bv0 8)))
""", "sat", "x+y=10 with x,y>0"))

# 2. Unsatisfiable: x + x = x (only solution is x=0) with x≠0
write(bv_dir / "add_self_unsat.smt2", smt2("QF_BV", """
(declare-fun x () (_ BitVec 8))
""", """
(assert (= (bvadd x x) x))
(assert (not (= x (_ bv0 8))))
""", "unsat", "x+x=x requires x=0"))

# 3. Bit masking: x & 0xF0 = 0xA0
write(bv_dir / "mask_sat.smt2", smt2("QF_BV", """
(declare-fun x () (_ BitVec 8))
""", """
(assert (= (bvand x (_ bv240 8)) (_ bv160 8)))
""", "sat"))

# 4. Overflow: x * 2 = x (8-bit, x must be 0 or 128)
write(bv_dir / "mul2_sat.smt2", smt2("QF_BV", """
(declare-fun x () (_ BitVec 8))
""", """
(assert (= (bvmul x (_ bv2 8)) x))
(assert (not (= x (_ bv0 8))))
""", "sat", "x=128 works"))

# 5. Shift: (x << 1) = x (requires x=0) plus x≠0 → unsat
write(bv_dir / "shift_unsat.smt2", smt2("QF_BV", """
(declare-fun x () (_ BitVec 8))
""", """
(assert (= (bvshl x (_ bv1 8)) x))
(assert (not (= x (_ bv0 8))))
""", "unsat"))

# 6. Signed comparison chain
write(bv_dir / "signed_chain_sat.smt2", smt2("QF_BV", """
(declare-fun a () (_ BitVec 16))
(declare-fun b () (_ BitVec 16))
(declare-fun c () (_ BitVec 16))
""", """
(assert (bvslt a b))
(assert (bvslt b c))
(assert (bvslt c a))
""", "unsat", "signed < cycle"))

# 7. 32-bit: x^2 - y^2 = (x-y)(x+y)
write(bv_dir / "diff_squares_sat.smt2", smt2("QF_BV", """
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
""", """
(assert (= (bvsub (bvmul x x) (bvmul y y))
           (bvmul (bvsub x y) (bvadd x y))))
(assert (not (= x (_ bv0 32))))
""", "sat", "algebraic identity always holds"))

# 8. Bit extraction: bit 3 of x is 1 and x < 16 → unsat
write(bv_dir / "bit_extract_unsat.smt2", smt2("QF_BV", """
(declare-fun x () (_ BitVec 8))
""", """
(assert (= ((_ extract 3 3) x) (_ bv1 1)))
(assert (bvult x (_ bv8 8)))
""", "unsat", "bit3=1 requires x>=8"))

# 9. XOR cancel: x XOR y XOR y = x
write(bv_dir / "xor_cancel_sat.smt2", smt2("QF_BV", """
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
""", """
(assert (not (= (bvxor (bvxor x y) y) x)))
""", "unsat", "xor cancel always holds"))

# 10. Concat + extract roundtrip
write(bv_dir / "concat_extract_sat.smt2", smt2("QF_BV", """
(declare-fun hi () (_ BitVec 8))
(declare-fun lo () (_ BitVec 8))
""", """
(declare-fun w () (_ BitVec 16))
(assert (= w (concat hi lo)))
(assert (= ((_ extract 15 8) w) hi))
(assert (= ((_ extract 7 0) w) lo))
(assert (not (= hi (_ bv0 8))))
""", "sat"))

# 11-20: Parameterized arithmetic puzzles
for n, (a, b, expected) in enumerate([
    (5, 3, "sat"),   (0, 0, "sat"),   (255, 1, "sat"),
    (127, 127, "sat"), (200, 100, "sat"), (10, 245, "sat"),
    (128, 128, "sat"), (1, 254, "sat"),  (64, 64, "sat"),
    (17, 83, "sat"),
], start=11):
    write(bv_dir / f"arith_{n:02d}.smt2", smt2("QF_BV", """
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
""", f"""
(assert (= x (_ bv{a} 8)))
(assert (= y (_ bv{b} 8)))
(assert (= (bvadd x y) (_ bv{(a+b)%256} 8)))
""", expected))

# 21-25: Unsigned division / modulo
write(bv_dir / "udiv_sat.smt2", smt2("QF_BV", """
(declare-fun x () (_ BitVec 8))
""", """
(assert (= (bvudiv x (_ bv3 8)) (_ bv5 8)))
""", "sat", "x in {15,16,17}"))

write(bv_dir / "urem_unsat.smt2", smt2("QF_BV", """
(declare-fun x () (_ BitVec 8))
""", """
(assert (= (bvurem x (_ bv4 8)) (_ bv4 8)))
""", "unsat", "remainder < divisor always"))

write(bv_dir / "bvneg_sat.smt2", smt2("QF_BV", """
(declare-fun x () (_ BitVec 8))
""", """
(assert (= (bvadd x (bvneg x)) (_ bv0 8)))
(assert (not (= x (_ bv0 8))))
""", "sat", "x + (-x) = 0 always"))

write(bv_dir / "bvnot_sat.smt2", smt2("QF_BV", """
(declare-fun x () (_ BitVec 8))
""", """
(assert (= (bvadd x (bvnot x)) (_ bv255 8)))
(assert (bvugt x (_ bv100 8)))
""", "sat"))

write(bv_dir / "zero_extend_sat.smt2", smt2("QF_BV", """
(declare-fun x () (_ BitVec 8))
""", """
(declare-fun y () (_ BitVec 16))
(assert (= y ((_ zero_extend 8) x)))
(assert (bvugt x (_ bv200 8)))
(assert (bvult y (_ bv300 16)))
""", "sat"))

# ---------------------------------------------------------------------------
# QF_UF — uninterpreted functions + congruence closure
# ---------------------------------------------------------------------------

uf_dir = ROOT / "qf_uf"

# 1. Basic transitivity
write(uf_dir / "transitivity_sat.smt2", smt2("QF_UF", """
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
""", """
(assert (= a b))
(assert (= b c))
(assert (not (= a c)))
""", "unsat", "a=b=c implies a=c"))

# 2. Congruence closure
write(uf_dir / "congruence_sat.smt2", smt2("QF_UF", """
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun a () U)
(declare-fun b () U)
""", """
(assert (= a b))
(assert (not (= (f a) (f b))))
""", "unsat", "f(a)=f(b) when a=b"))

# 3. f(f(x)) = x, f(f(f(x))) = x → f(x) = x
write(uf_dir / "ff_x_sat.smt2", smt2("QF_UF", """
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun x () U)
""", """
(assert (= (f (f x)) x))
(assert (= (f (f (f x))) x))
(assert (not (= (f x) x)))
""", "unsat", "f(f(x))=x and f(f(f(x)))=x implies f(x)=x"))

# 4. Disequality chain — satisfiable
write(uf_dir / "diseq_sat.smt2", smt2("QF_UF", """
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
""", """
(assert (not (= a b)))
(assert (not (= b c)))
(assert (not (= a c)))
""", "sat"))

# 5. Two-function congruence
write(uf_dir / "two_func_sat.smt2", smt2("QF_UF", """
(declare-sort U 0)
(declare-fun f (U U) U)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
""", """
(assert (= a b))
(assert (= b c))
(assert (not (= (f a c) (f b b))))
""", "unsat"))

# 6. Boolean UF
write(uf_dir / "bool_uf_sat.smt2", smt2("QF_UF", """
(declare-sort U 0)
(declare-fun p (U) Bool)
(declare-fun a () U)
(declare-fun b () U)
""", """
(assert (= a b))
(assert (p a))
(assert (not (p b)))
""", "unsat", "p(a) and a=b implies p(b)"))

# 7. Three-element chain — satisfiable
write(uf_dir / "three_chain_sat.smt2", smt2("QF_UF", """
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun g (U) U)
(declare-fun a () U)
""", """
(assert (= (f a) (g a)))
(assert (not (= a (f a))))
""", "sat"))

# 8. Nelson-Oppen style with multiple equalities
write(uf_dir / "multi_eq_unsat.smt2", smt2("QF_UF", """
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(declare-fun d () U)
""", """
(assert (= a b))
(assert (= c d))
(assert (= (f a) c))
(assert (= (f b) d))
(assert (not (= (f a) (f b))))
""", "unsat"))

# 9. Pigeonhole-2 for UF
write(uf_dir / "uf_pigeonhole_sat.smt2", smt2("QF_UF", """
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
""", """
(assert (not (= a b)))
(assert (not (= a c)))
(assert (not (= b c)))
(assert (= (f a) (f b)))
""", "sat", "f can map two distinct elems to same"))

# 10. f(x)=y and f(y)=x and x≠y — satisfiable (2-cycle)
write(uf_dir / "two_cycle_sat.smt2", smt2("QF_UF", """
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun x () U)
(declare-fun y () U)
""", """
(assert (= (f x) y))
(assert (= (f y) x))
(assert (not (= x y)))
""", "sat"))

# 11-20: Varied congruence problems
for i, (body, expected) in enumerate([
    ("(assert (= (f (f (f (f a)))) a))\n(assert (not (= (f a) a)))\n(assert (not (= (f (f a)) a)))", "sat"),
    ("(assert (= a (f b)))\n(assert (= b (f a)))\n(assert (not (= a b)))", "sat"),
    ("(assert (= (f a) b))\n(assert (= (f b) a))\n(assert (= a b))\n(assert (not (= (f a) a)))", "unsat"),
    ("(assert (not (= a b)))\n(assert (not (= b c)))\n(assert (= a c))", "sat"),
    ("(assert (= (f a) (f b)))\n(assert (not (= a b)))", "sat"),
    ("(assert (= a b))\n(assert (= b c))\n(assert (= c d))\n(assert (not (= a d)))", "unsat"),
    ("(assert (= (f (f a)) (f a)))\n(assert (not (= (f a) a)))", "sat"),
    ("(assert (= a b))\n(assert (= (f a) c))\n(assert (not (= (f b) c)))", "unsat"),
    ("(assert (not (= (f a) a)))\n(assert (not (= (f (f a)) a)))\n(assert (not (= (f (f (f a))) a)))", "sat"),
    ("(assert (= a b))\n(assert (= (f a) b))\n(assert (not (= (f b) a)))", "unsat"),
], start=11):
    write(uf_dir / f"cong_{i:02d}.smt2", f"""; expected: {expected}
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun c () U)
(declare-fun d () U)
{body}
(check-sat)
""")

# ---------------------------------------------------------------------------
# QF_IDL — integer difference logic
# ---------------------------------------------------------------------------

idl_dir = ROOT / "qf_idl"

# 1. Simple chain: x ≤ y, y ≤ z, z ≤ x+5 — sat
write(idl_dir / "chain_sat.smt2", smt2("QF_IDL", """
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
""", """
(assert (<= (- x y) 0))
(assert (<= (- y z) 0))
(assert (<= (- z x) 5))
""", "sat"))

# 2. Negative cycle → unsat
write(idl_dir / "neg_cycle_unsat.smt2", smt2("QF_IDL", """
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
""", """
(assert (<= (- x y) 3))
(assert (<= (- y z) 2))
(assert (<= (- z x) -10))
""", "unsat", "3+2-10 = -5 < 0 → negative cycle"))

# 3. Equality encoding x=y as x-y≤0 and y-x≤0
write(idl_dir / "eq_sat.smt2", smt2("QF_IDL", """
(declare-fun x () Int)
(declare-fun y () Int)
""", """
(assert (<= (- x y) 0))
(assert (<= (- y x) 0))
(assert (<= (- x y) (- 1)))
""", "unsat", "x=y contradicts x<y"))

# 4. Long chain of differences
write(idl_dir / "long_chain_sat.smt2", """
; expected: sat  [chain of 10 vars]
(set-logic QF_IDL)
""" + "\n".join(f"(declare-fun x{i} () Int)" for i in range(10)) + """
(assert (<= (- x0 x1) 1))
(assert (<= (- x1 x2) 1))
(assert (<= (- x2 x3) 1))
(assert (<= (- x3 x4) 1))
(assert (<= (- x4 x5) 1))
(assert (<= (- x5 x6) 1))
(assert (<= (- x6 x7) 1))
(assert (<= (- x7 x8) 1))
(assert (<= (- x8 x9) 1))
(assert (<= (- x9 x0) -1))
(check-sat)
""")

# 5. Multiple negative cycles — only one active at a time (sat via choice)
write(idl_dir / "choice_sat.smt2", smt2("QF_IDL", """
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
""", """
(assert (or (<= (- a b) -5) (<= (- b a) -5)))
""", "sat"))

# 6. Tight cycle: x-y≤1, y-x≤1, x-y≤-1 → unsat
write(idl_dir / "tight_cycle_unsat.smt2", smt2("QF_IDL", """
(declare-fun x () Int)
(declare-fun y () Int)
""", """
(assert (<= (- x y) 1))
(assert (<= (- y x) 1))
(assert (<= (- x y) (- 1)))
(assert (<= (- y x) (- 1)))
""", "unsat", "x-y≤-1 and y-x≤-1 sum to -2≤0 contradiction"))

# 7-20: Varied IDL puzzles
idl_cases = [
    # (vars, constraints, expected)
    (["p","q"], ["(<= (- p q) 3)", "(<= (- q p) 3)", "(>= p 0)", "(<= p 10)"], "sat"),
    (["a","b","c","d"], ["(<= (- a b) 2)", "(<= (- b c) 2)", "(<= (- c d) 2)", "(<= (- d a) -7)"], "unsat"),
    (["x","y"], ["(= x y)", "(not (= x y))"], "unsat"),
    (["x","y","z"], ["(<= (- x y) 0)", "(<= (- y z) 0)", "(<= (- z x) 0)"], "sat"),
    (["a","b"], ["(<= (- a b) 100)", "(<= (- b a) (- 101))"], "unsat"),
    (["a","b","c"], ["(<= (- a b) 5)", "(<= (- b c) 5)", "(>= a 0)", "(<= c 9)"], "sat"),
    (["x","y"], ["(= (- x y) 3)", "(= (- y x) (- 3))"], "sat"),
    (["x","y"], ["(<= (- x y) (- 1))", "(<= (- y x) (- 1))"], "unsat"),
    (["a","b","c"], ["(<= (- a b) 1)", "(<= (- b c) 1)", "(<= (- c a) 1)", "(<= (- a b) (- 1))", "(<= (- b c) (- 1))"], "unsat"),
    (["x","y","z","w"], ["(<= (- x y) 3)", "(<= (- y z) 3)", "(<= (- z w) 3)", "(<= (- w x) -8)"], "unsat"),
    (["x","y","z","w"], ["(<= (- x y) 3)", "(<= (- y z) 3)", "(<= (- z w) 3)", "(<= (- w x) (- 7))"], "sat"),
    (["a","b"], ["(= a b)", "(not (= b a))"], "unsat"),
    (["a","b","c","d","e"], ["(<= (- a b) 1)", "(<= (- b c) 1)", "(<= (- c d) 1)", "(<= (- d e) 1)", "(<= (- e a) -3)"], "sat"),
    (["a","b","c","d","e"], ["(<= (- a b) 1)", "(<= (- b c) 1)", "(<= (- c d) 1)", "(<= (- d e) 1)", "(<= (- e a) -5)"], "unsat"),
]
for i, (vars_, constrs, expected) in enumerate(idl_cases, start=7):
    decls = "\n".join(f"(declare-fun {v} () Int)" for v in vars_)
    asserts = "\n".join(f"(assert {c})" for c in constrs)
    write(idl_dir / f"idl_{i:02d}.smt2", f"""; expected: {expected}
(set-logic QF_IDL)
{decls}
{asserts}
(check-sat)
""")

# ---------------------------------------------------------------------------
# QF_LIA — linear integer arithmetic (Simplex + branch-and-bound)
# ---------------------------------------------------------------------------

lia_dir = ROOT / "qf_lia"

# 1. Simple: 2x + 3y = 12, x≥0, y≥0
write(lia_dir / "simple_sat.smt2", smt2("QF_LIA", """
(declare-fun x () Int)
(declare-fun y () Int)
""", """
(assert (= (+ (* 2 x) (* 3 y)) 12))
(assert (>= x 0))
(assert (>= y 0))
""", "sat", "e.g. x=0,y=4"))

# 2. Infeasible over integers: 3x + 6y = 1 → unsat (gcd=3 doesn't divide 1)
write(lia_dir / "gcd_unsat.smt2", smt2("QF_LIA", """
(declare-fun x () Int)
(declare-fun y () Int)
""", """
(assert (= (+ (* 3 x) (* 6 y)) 1))
""", "unsat", "gcd(3,6)=3 does not divide 1"))

# 3. Feasible: x > 0, y > 0, x + y < 5, x + y > 2
write(lia_dir / "range_sat.smt2", smt2("QF_LIA", """
(declare-fun x () Int)
(declare-fun y () Int)
""", """
(assert (> x 0))
(assert (> y 0))
(assert (< (+ x y) 5))
(assert (> (+ x y) 2))
""", "sat"))

# 4. Tight: x ≥ 1, x ≤ 0 → unsat
write(lia_dir / "tight_unsat.smt2", smt2("QF_LIA", """
(declare-fun x () Int)
""", """
(assert (>= x 1))
(assert (<= x 0))
""", "unsat"))

# 5. Pigeonhole integers: 3 items into 2 boxes, each box ≤ 1
write(lia_dir / "pigeonhole_unsat.smt2", smt2("QF_LIA", """
(declare-fun b1 () Int)
(declare-fun b2 () Int)
""", """
(assert (>= b1 0))
(assert (>= b2 0))
(assert (= (+ b1 b2) 3))
(assert (<= b1 1))
(assert (<= b2 1))
""", "unsat", "can't fit 3 items in 2 unit boxes"))

# 6. Modular: x mod-like: 7 | (x-3), x ≥ 0, x < 20
write(lia_dir / "divisibility_sat.smt2", smt2("QF_LIA", """
(declare-fun x () Int)
(declare-fun k () Int)
""", """
(assert (= x (+ (* 7 k) 3)))
(assert (>= x 0))
(assert (< x 20))
(assert (>= k 0))
""", "sat", "x=3,10,17 all work"))

# 7. Linear system: 2x - y = 3, x + 2y = 9
write(lia_dir / "system_sat.smt2", smt2("QF_LIA", """
(declare-fun x () Int)
(declare-fun y () Int)
""", """
(assert (= (- (* 2 x) y) 3))
(assert (= (+ x (* 2 y)) 9))
""", "sat", "x=3, y=3"))

# 8. Conflicting: x > y, y > z, z > x
write(lia_dir / "order_cycle_unsat.smt2", smt2("QF_LIA", """
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
""", """
(assert (> x y))
(assert (> y z))
(assert (> z x))
""", "unsat"))

# 9. Bounds only
write(lia_dir / "bounds_sat.smt2", smt2("QF_LIA", """
(declare-fun x () Int)
""", """
(assert (>= x 5))
(assert (<= x 10))
""", "sat"))

# 10. 4-variable feasibility
write(lia_dir / "four_vars_sat.smt2", smt2("QF_LIA", """
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(declare-fun d () Int)
""", """
(assert (>= a 1))
(assert (>= b 1))
(assert (>= c 1))
(assert (>= d 1))
(assert (<= (+ a b c d) 10))
""", "sat"))

# 11-25: Varied LIA cases
lia_cases = [
    ("(assert (= (* 5 x) 17))", "unsat", "5 doesn't divide 17"),
    ("(assert (>= x 0))\n(assert (<= x 0))\n(assert (not (= x 0)))", "unsat"),
    ("(assert (>= (* 2 x) 3))\n(assert (<= x 1))", "unsat", "2x>=3 requires x>=2"),
    ("(assert (>= (* 2 x) 4))\n(assert (<= x 2))", "sat"),
    ("(assert (> x (* 2 y)))\n(assert (> y (* 2 x)))\n(assert (>= x 0))\n(assert (>= y 0))", "unsat"),
    ("(assert (>= x 0))\n(assert (>= y 0))\n(assert (<= (+ x y) 100))\n(assert (>= (* 3 x) (* 2 y)))", "sat"),
    ("(assert (= (+ x y) 10))\n(assert (= (+ x (* 2 y)) 15))", "sat", "x=5,y=5"),
    ("(assert (= (+ x y) 10))\n(assert (= (+ x (* 2 y)) 9))", "sat", "x=11,y=-1"),
    ("(assert (> x 0))\n(assert (> y 0))\n(assert (< (+ (* 3 x) (* 5 y)) 8))", "sat"),
    ("(assert (> x 0))\n(assert (> y 0))\n(assert (< (+ (* 3 x) (* 5 y)) 8))\n(assert (> (+ (* 3 x) (* 5 y)) 9))", "unsat"),
    ("(assert (= x 7))\n(assert (= y 3))\n(assert (not (= (+ x y) 10)))", "unsat"),
    ("(assert (>= x (- 100)))\n(assert (<= x 100))\n(assert (= (* 13 x) 0))\n(assert (not (= x 0)))", "unsat"),
    ("(assert (>= x 1))\n(assert (<= x 1000000))\n(assert (= (* x x) (* x x)))", "sat"),
    ("(assert (= (+ a b c) 10))\n(assert (>= a 0))\n(assert (>= b 0))\n(assert (>= c 0))\n(assert (<= a 3))\n(assert (<= b 3))\n(assert (<= c 3))", "unsat", "max sum=9"),
    ("(assert (= (+ a b c) 9))\n(assert (>= a 0))\n(assert (>= b 0))\n(assert (>= c 0))\n(assert (<= a 3))\n(assert (<= b 3))\n(assert (<= c 3))", "sat"),
]

for i, item in enumerate(lia_cases, start=11):
    body, expected = item[0], item[1]
    comment = item[2] if len(item) > 2 else ""
    # detect which vars are used
    used = []
    for v in ["x","y","a","b","c"]:
        if v in body:
            used.append(v)
    decls = "\n".join(f"(declare-fun {v} () Int)" for v in used)
    write(lia_dir / f"lia_{i:02d}.smt2", f"""; expected: {expected}{f"  [{comment}]" if comment else ""}
(set-logic QF_LIA)
{decls}
{body}
(check-sat)
""")


# ---------------------------------------------------------------------------
# Summary
# ---------------------------------------------------------------------------
total = sum(len(list(d.glob("*.smt2"))) for d in [bv_dir, uf_dir, idl_dir, lia_dir])
print(f"Generated {total} SMT2 benchmarks:")
for d in [bv_dir, uf_dir, idl_dir, lia_dir]:
    files = list(d.glob("*.smt2"))
    print(f"  {d.name}: {len(files)} problems")
