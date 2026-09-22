; expected: unsat
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (> x y))
(assert (> y z))
(assert (> z x))
(check-sat)
