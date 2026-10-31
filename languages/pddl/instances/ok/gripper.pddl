(define (domain gripper)
  (:predicates (at ?b) (holding ?b))
  (:action pick
    :parameters (?b)
    :precondition (at ?b)
    :effect (and (holding ?b) (not (at ?b))))
  (:action drop
    :parameters (?b)
    :precondition (holding ?b)
    :effect (and (at ?b) (not (holding ?b)))))
