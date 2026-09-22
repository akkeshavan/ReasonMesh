; expected: unsat
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun a () Int)
(assert (= x 7))
(assert (= y 3))
(assert (not (= (+ x y) 10)))
(check-sat)
