; Rules with no query. Interpreting P as universally true satisfies every
; assertion, so the answer would say nothing about the program.
(set-logic HORN)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (P x))))
(assert (forall ((x Int) (y Int)) (=> (and (P x) (= y (+ x 1))) (P y))))
(check-sat)
