(define (problem task) (:domain d)  (:init (p)) (:goal (and)) (:constraints (preference pref (within 0 (q)))) (:metric minimize (is-violated pref)))
