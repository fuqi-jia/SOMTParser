(define (domain repeated-pulse)
 (:requirements :strips :fluents :durative-actions)
 (:predicates (dummy)) (:functions (x))
 (:action pulse :parameters () :precondition () :effect (increase (x) 1)))
