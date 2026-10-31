(define (problem task) (:domain d)  (:init (p)) (:goal (and)) (:constraints (preference pref (always-within 1 (p) (q)))) (:metric minimize (is-violated pref)))
