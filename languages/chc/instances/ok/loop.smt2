; The running example of docs/languages/chc-comp.md §2.1: an invariant Inv, two
; rules that say it holds initially and is preserved, and one query that says it
; implies the property. A solution for Inv is the program's inductive invariant.
(set-logic HORN)
(declare-fun Inv (Int Int) Bool)
(assert (forall ((x Int) (y Int))
  (=> (and (= x 0) (= y 0)) (Inv x y))))
(assert (forall ((x Int) (y Int) (x1 Int))
  (=> (and (Inv x y) (= x1 (+ x 1))) (Inv x1 y))))
(assert (forall ((x Int) (y Int))
  (=> (and (Inv x y) (> y x)) false)))
(check-sat)
