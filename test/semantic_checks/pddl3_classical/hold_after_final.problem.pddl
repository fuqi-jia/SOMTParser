(define (problem task) (:domain d)  (:init (p)) (:goal (and)) (:constraints (preference pref (hold-after 10 (p)))) (:metric minimize (is-violated pref)))
