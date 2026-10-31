; With fond_policy=strong-cyclic, policy_size=2: SAT under outcome fairness.
; With fond_policy=strong, policy_size=2: UNSAT (the retry may last forever).
(define (domain fond-retry)
  (:requirements :strips :non-deterministic)
  (:predicates (done))
  (:action try :parameters () :effect (oneof (and) (done))))
