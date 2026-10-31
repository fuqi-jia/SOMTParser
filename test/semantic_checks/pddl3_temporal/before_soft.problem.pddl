(define (problem t) (:domain d) (:init) (:goal (q)) (:constraints (preference pref (sometime-before (p) (q)))) (:metric minimize (is-violated pref)))
