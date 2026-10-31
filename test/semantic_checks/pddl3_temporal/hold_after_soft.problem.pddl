(define (problem t) (:domain d) (:init) (:goal (q)) (:constraints (preference pref (hold-after 2 (p)))) (:metric minimize (is-violated pref)))
