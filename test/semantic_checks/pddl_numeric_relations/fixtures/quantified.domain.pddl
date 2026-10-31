(define (domain numeric) (:requirements :adl :numeric-fluents)
        (:types item) (:constants a b - item) (:predicates (done)) (:functions (fuel ?i - item))
        (:action transfer :parameters () :effect (and (done)
            (forall (?i - item) (when (> (fuel ?i) 0) (decrease (fuel ?i) 0.5))))))