(define (problem task) (:domain d)  (:init (p)) (:goal (and)) (:constraints (preference pref (sometime-before (p) (p)))) (:metric minimize (is-violated pref)))
