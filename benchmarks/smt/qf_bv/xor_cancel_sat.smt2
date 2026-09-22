; expected: unsat  [xor cancel always holds]
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(assert (not (= (bvxor (bvxor x y) y) x)))
(check-sat)
