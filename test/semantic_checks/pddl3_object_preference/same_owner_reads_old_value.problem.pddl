(define (problem same_owner_reads_old_value) (:domain object-soft)
  (:init (= (pick) a) (= (other) a) (= (slot a) b) (= (slot b) a) (= (clock) 0))
  (:goal (done-reader)) (:metric minimize (+ total-time (* 7 (is-violated pref)))))
