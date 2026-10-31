(define (problem t) (:domain d) (:init) (:goal (q)) (:constraints (preference pref (at end (p)))) (:metric minimize (is-violated pref)))
