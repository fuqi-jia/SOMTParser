(define (domain d) (:requirements :durative-actions :preferences)
(:predicates (p)) (:durative-action a :parameters () :duration (= ?duration 1)
:condition (and) :effect (at end (p))))
