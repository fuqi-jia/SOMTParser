(define (problem task) (:domain d)  (:init (p)) (:goal (and)) (:constraints (preference pref (hold-during 0.5 2.5 (p)))) (:metric minimize (is-violated pref)))
