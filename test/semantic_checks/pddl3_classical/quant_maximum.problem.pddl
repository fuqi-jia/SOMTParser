(define (problem task) (:domain d)  (:init ) (:goal (and (preference (marked a)) (preference named (marked b))))  (:metric maximize (- 10 (* 3 (is-violated named)))))
