(define (problem t) (:domain d) (:init) (:goal (q)) (:constraints (preference pref (at-most-once (p)))) (:metric minimize (is-violated pref)))
