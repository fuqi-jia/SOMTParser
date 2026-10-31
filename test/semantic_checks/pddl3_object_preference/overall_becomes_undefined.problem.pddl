(define (problem overall_becomes_undefined) (:domain object-soft)
  (:init (= (pick) a) (= (other) a) (= (slot a) a) (= (slot b) a) (= (clock) 0))
  (:goal (and (done-reader) (done-writer))) (:metric minimize (+ total-time (* 7 (is-violated pref)))))
