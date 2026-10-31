(define (problem task) (:domain d)  (:init ) (:goal (forall (?x - item) (forall (?x - item) (preference pref (marked ?x)))))  (:metric minimize (is-violated pref)))
