; A disjunction in the head. Legal SMT-LIB, not Horn: a CHC solver would not
; accept it, so translating it would put an incomparable row in a CHC table.
(set-logic HORN)
(declare-fun A (Int) Bool)
(declare-fun B (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (or (A x) (B x)))))
(assert (forall ((x Int)) (=> (A x) false)))
(check-sat)
