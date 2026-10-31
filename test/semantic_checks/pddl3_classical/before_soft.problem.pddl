(define (problem task) (:domain d)  (:init (p)) (:goal (and)) (:constraints (preference pref (sometime-before (p) (q)))) (:metric minimize (is-violated pref)))
