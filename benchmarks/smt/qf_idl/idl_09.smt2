; expected: unsat
(set-logic QF_IDL)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= x y))
(assert (not (= x y)))
(check-sat)
