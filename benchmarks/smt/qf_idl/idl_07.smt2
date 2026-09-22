; expected: sat
(set-logic QF_IDL)
(declare-fun p () Int)
(declare-fun q () Int)
(assert (<= (- p q) 3))
(assert (<= (- q p) 3))
(assert (>= p 0))
(assert (<= p 10))
(check-sat)
