(define (domain adl-core)
  (:requirements :adl)
  (:types item - object marked - item)
  (:constants c - marked)
  (:predicates (p ?x - item) (q ?x - item) (done))
  (:action update
    :parameters (?x - item)
    :precondition
      (and (p ?x)
           (forall (?y - item) (or (q ?y) (= ?y ?x))))
    :effect
      (and
        (forall (?y - item) (when (q ?y) (p ?y)))
        (when (q ?x) (not (p ?x)))
        (when (q ?x) (p ?x))
        (done))))
