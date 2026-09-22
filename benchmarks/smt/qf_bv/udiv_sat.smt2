; expected: sat  [x in {15,16,17}]
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(assert (= (bvudiv x (_ bv3 8)) (_ bv5 8)))
(check-sat)
