; A predicate under a negation in the body. Also legal SMT-LIB and also not
; Horn -- the body must be a conjunction of constraints and applications.
(set-logic HORN)
(declare-fun P (Int) Bool)
(assert (forall ((x Int) (y Int))
  (=> (and (not (P x)) (= y (+ x 1))) (P y))))
(assert (forall ((x Int)) (=> (P x) false)))
(check-sat)
