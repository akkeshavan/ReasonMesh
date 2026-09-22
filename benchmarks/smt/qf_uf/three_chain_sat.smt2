; expected: sat
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun g (U) U)
(declare-fun a () U)
(assert (= (f a) (g a)))
(assert (not (= a (f a))))
(check-sat)
