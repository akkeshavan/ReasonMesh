; expected: sat
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 16))
(assert (= y ((_ zero_extend 8) x)))
(assert (bvugt x (_ bv200 8)))
(assert (bvult y (_ bv300 16)))
(check-sat)
