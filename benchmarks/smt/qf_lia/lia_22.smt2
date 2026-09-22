; expected: unsat
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun a () Int)
(assert (>= x (- 100)))
(assert (<= x 100))
(assert (= (* 13 x) 0))
(assert (not (= x 0)))
(check-sat)
