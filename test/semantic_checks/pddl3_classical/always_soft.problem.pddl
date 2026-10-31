(define (problem task) (:domain d)  (:init (p)) (:goal (and)) (:constraints (preference pref (always (p)))) (:metric minimize (is-violated pref)))
