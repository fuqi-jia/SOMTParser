(define (problem task) (:domain d)  (:init ) (:goal (preference pref (forall (?x - item) (marked ?x))))  (:metric minimize (is-violated pref)))
