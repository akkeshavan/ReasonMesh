; expected: unsat
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(assert (= (bvshl x (_ bv1 8)) x))
(assert (not (= x (_ bv0 8))))
(check-sat)
