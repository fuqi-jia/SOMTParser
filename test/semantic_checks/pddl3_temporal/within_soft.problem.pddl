(define (problem t) (:domain d) (:init) (:goal (q)) (:constraints (preference pref (within 2 (q)))) (:metric minimize (is-violated pref)))
