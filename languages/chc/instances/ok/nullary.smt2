; A zero-argument Boolean function is a nullary uninterpreted predicate in the
; official grammar. The query deliberately carries a dummy quantified variable
; because chc_query requires a non-empty binder list.
(set-logic HORN)
(declare-fun Ready () Bool)
(assert Ready)
(assert (forall ((x Int)) (=> (and Ready (< x 0)) false)))
(check-sat)
