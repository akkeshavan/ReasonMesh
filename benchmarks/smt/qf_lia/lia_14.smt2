; expected: sat
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun a () Int)
(assert (>= (* 2 x) 4))
(assert (<= x 2))
(check-sat)
