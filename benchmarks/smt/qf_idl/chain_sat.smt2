; expected: sat
(set-logic QF_IDL)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (<= (- x y) 0))
(assert (<= (- y z) 0))
(assert (<= (- z x) 5))
(check-sat)
