; expected: sat
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (> x 0))
(assert (> y 0))
(assert (< (+ x y) 5))
(assert (> (+ x y) 2))
(check-sat)
