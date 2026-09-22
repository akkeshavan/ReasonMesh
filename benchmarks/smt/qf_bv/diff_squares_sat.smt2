; expected: sat  [algebraic identity always holds]
(set-logic QF_BV)
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(assert (= (bvsub (bvmul x x) (bvmul y y))
           (bvmul (bvsub x y) (bvadd x y))))
(assert (not (= x (_ bv0 32))))
(check-sat)
