(define (problem t) (:domain d) (:init) (:goal (and (q) (forall (?x - empty) (preference pref (p)))))  (:metric minimize (is-violated pref)))
