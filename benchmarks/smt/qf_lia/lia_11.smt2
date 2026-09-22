; expected: unsat  [5 doesn't divide 17]
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun a () Int)
(assert (= (* 5 x) 17))
(check-sat)
