; expected: unsat
(set-logic QF_IDL)
(declare-fun a () Int)
(declare-fun b () Int)
(assert (<= (- a b) 100))
(assert (<= (- b a) (- 101)))
(check-sat)
