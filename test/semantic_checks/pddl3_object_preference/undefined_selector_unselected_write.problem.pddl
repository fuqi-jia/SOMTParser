(define (problem undefined_selector_unselected_write) (:domain object-soft)
  (:init (= (other) a) (= (slot a) a) (= (slot b) a) (= (clock) 0))
  (:goal (and (done-reader) (done-writer))) (:metric minimize (+ total-time (* 7 (is-violated pref)))))
