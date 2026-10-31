(define (problem t) (:domain d) (:init (= (x) 0) (= (y) 0)) (:goal (q))  (:metric minimize (is-violated pref)))
