; expected: sat  [e.g. x=0,y=4]
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (+ (* 2 x) (* 3 y)) 12))
(assert (>= x 0))
(assert (>= y 0))
(check-sat)
