; expected: unsat  [3+2-10 = -5 < 0 → negative cycle]
(set-logic QF_IDL)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (<= (- x y) 3))
(assert (<= (- y z) 2))
(assert (<= (- z x) -10))
(check-sat)
