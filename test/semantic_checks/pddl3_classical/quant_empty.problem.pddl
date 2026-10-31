(define (problem task) (:domain d)  (:init ) (:goal (forall (?x - vacant) (preference vacant-ok (and))))  (:metric minimize (is-violated vacant-ok)))
