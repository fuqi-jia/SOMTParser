(define (problem same_owner_changes_selector) (:domain object-soft)
  (:init (= (pick) a) (= (other) a) (= (slot a) a) (= (slot b) b) (= (clock) 0))
  (:goal (done-reader)) (:metric minimize (+ total-time (* 7 (is-violated pref)))))
