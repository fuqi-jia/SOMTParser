(define (problem stable-goal-problem) (:domain stable-goal)
 (:init (p) (at 2 (not (p))) (at 3 (p)) (at 10 (q)))
 (:goal (p)) (:metric minimize total-time))
