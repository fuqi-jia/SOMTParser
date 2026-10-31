(define (problem t) (:domain d) (:init) (:goal (and (q) (preference pref (> (x) 0))))  (:metric minimize (is-violated pref)))
