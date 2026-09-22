; expected: sat
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(assert (= (bvadd x (bvnot x)) (_ bv255 8)))
(assert (bvugt x (_ bv100 8)))
(check-sat)
