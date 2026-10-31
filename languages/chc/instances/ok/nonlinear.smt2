; "Non-linear" in the CHC sense: TWO predicate applications in one body, which
; is unrelated to non-linear arithmetic. docs/languages/chc-comp.md §1 warns
; that conflating the two is hard to spot.
(set-logic HORN)
(declare-fun A (Int) Bool)
(declare-fun B (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (A x))))
(assert (forall ((x Int)) (=> (= x 1) (B x))))
(assert (forall ((x Int) (y Int)) (=> (and (A x) (B y) (= x y)) false)))
(check-sat)
