; expected: sat
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(assert (= x (_ bv64 8)))
(assert (= y (_ bv64 8)))
(assert (= (bvadd x y) (_ bv128 8)))
(check-sat)
