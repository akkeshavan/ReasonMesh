; expected: sat
(set-logic QF_IDL)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (- x y) 3))
(assert (= (- y x) (- 3)))
(check-sat)
