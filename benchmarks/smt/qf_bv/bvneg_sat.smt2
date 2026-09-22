; expected: sat  [x + (-x) = 0 always]
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(assert (= (bvadd x (bvneg x)) (_ bv0 8)))
(assert (not (= x (_ bv0 8))))
(check-sat)
