; expected: unsat
(set-logic QF_IDL)
(declare-fun a () Int)
(declare-fun b () Int)
(assert (= a b))
(assert (not (= b a)))
(check-sat)
