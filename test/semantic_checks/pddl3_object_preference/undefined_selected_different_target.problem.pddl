(define (problem undefined_selected_different_target) (:domain object-soft)
  (:init (= (pick) a) (= (other) b) (= (slot b) a) (= (clock) 0))
  (:goal (and (done-reader) (done-writer))) (:metric minimize (+ total-time (* 7 (is-violated pref)))))
