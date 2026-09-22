; expected: unsat  [f(f(x))=x and f(f(f(x)))=x implies f(x)=x]
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun x () U)
(assert (= (f (f x)) x))
(assert (= (f (f (f x))) x))
(assert (not (= (f x) x)))
(check-sat)
