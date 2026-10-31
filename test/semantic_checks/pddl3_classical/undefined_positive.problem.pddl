(define (problem task) (:domain d)  (:init ) (:goal (preference pref (> (x) 0)))  (:metric minimize (is-violated pref)))
