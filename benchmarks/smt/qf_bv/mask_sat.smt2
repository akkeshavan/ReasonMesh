; expected: sat
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(assert (= (bvand x (_ bv240 8)) (_ bv160 8)))
(check-sat)
