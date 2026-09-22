; expected: unsat  [x=y contradicts x<y]
(set-logic QF_IDL)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (<= (- x y) 0))
(assert (<= (- y x) 0))
(assert (<= (- x y) (- 1)))
(check-sat)
