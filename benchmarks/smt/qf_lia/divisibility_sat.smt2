; expected: sat  [x=3,10,17 all work]
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun k () Int)
(assert (= x (+ (* 7 k) 3)))
(assert (>= x 0))
(assert (< x 20))
(assert (>= k 0))
(check-sat)
