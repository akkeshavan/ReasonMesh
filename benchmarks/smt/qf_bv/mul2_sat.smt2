; expected: sat  [x=32768 in 16-bit: 32768*2=65536 wraps to 0... let's use bvmul by 0]
(set-logic QF_BV)
(declare-fun x () (_ BitVec 16))
(assert (bvugt x (_ bv0 16)))
(assert (bvult x (_ bv256 16)))
(assert (bvugt (bvmul x (_ bv2 16)) x))
(check-sat)
