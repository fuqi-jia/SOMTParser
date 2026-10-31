(define (problem task) (:domain d)  (:init (p)) (:goal (and)) (:constraints (preference pref (sometime (q)))) (:metric minimize (is-violated pref)))
