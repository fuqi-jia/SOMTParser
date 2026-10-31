(define (problem task) (:domain d)  (:init ) (:goal (and (preference pa (marked a)) (preference pb (marked b))))  (:metric minimize (+ 7 (* 2 3 (is-violated pa)) (is-violated pb))))
