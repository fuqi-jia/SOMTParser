; Non-nullary facts and heads use quantified variables in CHC-COMP normal form.
(set-logic HORN)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (P x))))
(assert (forall ((x Int) (y Int)) (=> (and (P x) (= y (+ x 1))) (P y))))
(assert (forall ((x Int)) (=> (and (P x) (< x 0)) false)))
(check-sat)
