(define (problem t) (:domain d) (:init) (:goal (q)) (:constraints (preference pref (sometime-after (p) (q)))) (:metric minimize (is-violated pref)))
