; expected: unsat  [2x>=3 requires x>=2]
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun a () Int)
(assert (>= (* 2 x) 3))
(assert (<= x 1))
(check-sat)
