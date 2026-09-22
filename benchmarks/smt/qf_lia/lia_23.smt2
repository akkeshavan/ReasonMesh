; expected: sat
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (>= x 1))
(assert (<= x 1000000))
(assert (= (+ x y) 1000001))
(assert (>= y 1))
(check-sat)
