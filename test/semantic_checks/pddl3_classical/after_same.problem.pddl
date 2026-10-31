(define (problem task) (:domain d)  (:init (p)) (:goal (and)) (:constraints (preference pref (sometime-after (p) (p)))) (:metric minimize (is-violated pref)))
