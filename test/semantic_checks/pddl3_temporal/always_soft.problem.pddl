(define (problem t) (:domain d) (:init) (:goal (q)) (:constraints (preference pref (always (p)))) (:metric minimize (is-violated pref)))
