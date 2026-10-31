(define (problem t) (:domain d) (:init) (:goal (q)) (:constraints (preference pref (always-within 1 (p) (q)))) (:metric minimize (is-violated pref)))
