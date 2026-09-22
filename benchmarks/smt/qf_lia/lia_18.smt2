; expected: sat  [x=11,y=-1]
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun a () Int)
(assert (= (+ x y) 10))
(assert (= (+ x (* 2 y)) 9))
(check-sat)
