; expected: unsat  [bit3=1 requires x>=8]
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(assert (= ((_ extract 3 3) x) (_ bv1 1)))
(assert (bvult x (_ bv8 8)))
(check-sat)
