(set-logic QF_LIA)
(declare-fun x () Int)
(assert-soft (> x 0))
(check-sat)
