(define (problem task) (:domain d)  (:init (p)) (:goal (and)) (:constraints (preference pref (hold-during 10 20 (p)))) (:metric minimize (is-violated pref)))
