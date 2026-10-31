(define (problem t) (:domain d) (:init) (:goal (q)) (:constraints (preference pref (sometime (q)))) (:metric minimize (is-violated pref)))
