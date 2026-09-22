; expected: sat
(set-logic QF_IDL)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(assert (or (<= (- a b) -5) (<= (- b a) -5)))
(check-sat)
