(define (problem t) (:domain d) (:init (= (x) 0) (= (y) 0)) (:goal (q)) (:constraints (preference pref (always (d)))) (:metric minimize (is-violated pref)))
