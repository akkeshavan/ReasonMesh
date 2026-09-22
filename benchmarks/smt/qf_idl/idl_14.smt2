; expected: unsat
(set-logic QF_IDL)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (<= (- x y) (- 1)))
(assert (<= (- y x) (- 1)))
(check-sat)
