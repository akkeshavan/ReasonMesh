; expected: unsat  [x-y≤-1 and y-x≤-1 sum to -2≤0 contradiction]
(set-logic QF_IDL)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (<= (- x y) 1))
(assert (<= (- y x) 1))
(assert (<= (- x y) (- 1)))
(assert (<= (- y x) (- 1)))
(check-sat)
