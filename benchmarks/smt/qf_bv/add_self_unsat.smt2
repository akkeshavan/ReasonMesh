; expected: unsat  [x+x=x requires x=0]
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(assert (= (bvadd x x) x))
(assert (not (= x (_ bv0 8))))
(check-sat)
