(define (problem task) (:domain d)  (:init (p)) (:goal (and)) (:constraints (preference pref (at-most-once (p)))) (:metric minimize (is-violated pref)))
