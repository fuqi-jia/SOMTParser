(define (problem task) (:domain d)  (:init (p)) (:goal (and)) (:constraints (preference pref (within 1 (q)))) (:metric minimize (is-violated pref)))
