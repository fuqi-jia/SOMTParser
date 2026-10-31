(define (domain d) (:requirements :adl :fluents :durative-actions :continuous-effects :derived-predicates :constraints :preferences)
(:predicates (q) (d)) (:functions (x) (y)) (:derived (d) (< (x) 1))
(:durative-action a :parameters () :duration (= ?duration 1) :condition (and)
 :effect (and (increase (y) #t) (increase (x) (* #t (- 4 (* 8 (y))))) (at end (q)))))
