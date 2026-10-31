(define (problem task) (:domain d)  (:init ) (:goal (and (preference pa (marked a)) (preference pb (marked b))))  (:metric minimize (+ (* 1.5 (is-violated pa)) (* 0.25 (is-violated pb)))))
