(define (problem same_owner_initializes_undefined) (:domain object-soft)
  (:init (= (pick) a) (= (other) a) (= (slot b) a) (= (clock) 0))
  (:goal (done-reader)) (:metric minimize (+ total-time (* 7 (is-violated pref)))))
