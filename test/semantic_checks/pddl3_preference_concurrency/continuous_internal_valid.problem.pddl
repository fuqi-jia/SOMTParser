(define (problem t) (:domain d) (:init (= (x) -1)) (:goal (and (done-a) (done-b))) (:metric minimize (is-violated pref)))
