; expected: sat  [x=3, y=3]
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (- (* 2 x) y) 3))
(assert (= (+ x (* 2 y)) 9))
(check-sat)
