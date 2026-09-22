; expected: unsat
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun a () Int)
(assert (>= x 0))
(assert (<= x 0))
(assert (not (= x 0)))
(check-sat)
