(define (domain grounded-pulse)
 (:requirements :strips :typing :fluents :durative-actions)
 (:types item) (:predicates (dummy)) (:functions (x))
 (:action pulse :parameters (?v - item) :precondition () :effect (increase (x) 1)))
