; expected: sat  [x=5,y=5]
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun a () Int)
(assert (= (+ x y) 10))
(assert (= (+ x (* 2 y)) 15))
(check-sat)
