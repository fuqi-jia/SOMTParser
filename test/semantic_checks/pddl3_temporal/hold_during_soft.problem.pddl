(define (problem t) (:domain d) (:init) (:goal (q)) (:constraints (preference pref (hold-during 1 3 (p)))) (:metric minimize (is-violated pref)))
