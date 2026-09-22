; expected: unsat  [remainder < divisor always]
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(assert (= (bvurem x (_ bv4 8)) (_ bv4 8)))
(check-sat)
