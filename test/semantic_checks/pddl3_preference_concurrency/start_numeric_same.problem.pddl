(define (problem t) (:domain d) (:init (p) (= (x) 0)) (:goal (and (done-a) (done-b))) (:metric minimize (is-violated pref)))
