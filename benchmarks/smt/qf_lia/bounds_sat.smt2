; expected: sat
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (>= x 5))
(assert (<= x 10))
(check-sat)
