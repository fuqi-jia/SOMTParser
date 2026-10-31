(define (problem task) (:domain d)  (:init (p)) (:goal (and)) (:constraints (preference pref (at end (p)))) (:metric minimize (is-violated pref)))
