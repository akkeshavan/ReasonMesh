; expected: sat  [x+y=10 with x,y>0]
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(assert (= (bvadd x y) (_ bv10 8)))
(assert (bvugt x (_ bv0 8)))
(assert (bvugt y (_ bv0 8)))
(check-sat)
