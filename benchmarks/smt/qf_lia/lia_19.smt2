; expected: unsat
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun a () Int)
(assert (> x 0))
(assert (> y 0))
(assert (< (+ (* 3 x) (* 5 y)) 8))
(check-sat)
