{"empty", R"PDDL((define (domain d) (:requirements :adl :object-fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (f ?x - node) (g ?x - node) - node (pick) - node)  ))PDDL", R"PDDL((define (problem p) (:domain d) (:init ) (:goal (and)) ))PDDL", 0, true},
{"initial", R"PDDL((define (domain d) (:requirements :adl :object-fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (f ?x - node) (g ?x - node) - node (pick) - node)  ))PDDL", R"PDDL((define (problem p) (:domain d) (:init (= (f a) b) (= (pick) a)) (:goal (= (f (pick)) b)) ))PDDL", 0, true},
{"nested", R"PDDL((define (domain d) (:requirements :adl :object-fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (f ?x - node) (g ?x - node) - node (pick) - node)  ))PDDL", R"PDDL((define (problem p) (:domain d) (:init (= (f a) b) (= (f b) a) (= (pick) a)) (:goal (= (f (f (pick))) a)) ))PDDL", 0, true},
{"predicate_dynamic", R"PDDL((define (domain d) (:requirements :adl :object-fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (f ?x - node) (g ?x - node) - node (pick) - node)  ))PDDL", R"PDDL((define (problem p) (:domain d) (:init (= (pick) b) (p b)) (:goal (p (pick))) ))PDDL", 0, true},
{"predicate_dynamic_false", R"PDDL((define (domain d) (:requirements :adl :object-fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (f ?x - node) (g ?x - node) - node (pick) - node)  ))PDDL", R"PDDL((define (problem p) (:domain d) (:init (= (pick) a) (p b)) (:goal (p (pick))) ))PDDL", 0, true},
{"undefined_not", R"PDDL((define (domain d) (:requirements :adl :object-fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (f ?x - node) (g ?x - node) - node (pick) - node)  ))PDDL", R"PDDL((define (problem p) (:domain d) (:init (done) (= (f a) a)) (:goal (not (= (pick) a))) ))PDDL", 0, true},
{"undefined_or", R"PDDL((define (domain d) (:requirements :adl :object-fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (f ?x - node) (g ?x - node) - node (pick) - node)  ))PDDL", R"PDDL((define (problem p) (:domain d) (:init (done) (= (f a) a)) (:goal (or (done) (= (pick) a))) ))PDDL", 0, true},
{"undefined_imply", R"PDDL((define (domain d) (:requirements :adl :object-fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (f ?x - node) (g ?x - node) - node (pick) - node)  ))PDDL", R"PDDL((define (problem p) (:domain d) (:init (done) (= (f a) a)) (:goal (imply (not (done)) (= (pick) a))) ))PDDL", 0, true},
{"undefined_predicate", R"PDDL((define (domain d) (:requirements :adl :object-fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (f ?x - node) (g ?x - node) - node (pick) - node)  ))PDDL", R"PDDL((define (problem p) (:domain d) (:init (done) (= (f a) a)) (:goal (not (p (pick)))) ))PDDL", 0, true},
{"undefined_exists", R"PDDL((define (domain d) (:requirements :adl :object-fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (f ?x - node) (g ?x - node) - node (pick) - node)  ))PDDL", R"PDDL((define (problem p) (:domain d) (:init (done) (= (f a) a)) (:goal (exists (?n - node) (= (f ?n) a))) ))PDDL", 0, true},
{"assign", R"PDDL((define (domain d) (:requirements :adl :object-fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (f ?x - node) (g ?x - node) - node (pick) - node)  (:action run :parameters (?x - node) :precondition (and) :effect (assign (pick) ?x))))PDDL", R"PDDL((define (problem p) (:domain d) (:init ) (:goal (and)) ))PDDL", 1, true},
{"reset", R"PDDL((define (domain d) (:requirements :adl :object-fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (f ?x - node) (g ?x - node) - node (pick) - node)  (:action run :parameters () :precondition (and) :effect (assign (pick) undefined))))PDDL", R"PDDL((define (problem p) (:domain d) (:init (= (pick) b)) (:goal (and)) ))PDDL", 1, true},
{"rhs_undefined", R"PDDL((define (domain d) (:requirements :adl :object-fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (f ?x - node) (g ?x - node) - node (pick) - node)  (:action run :parameters () :precondition (and) :effect (assign (pick) (f a)))))PDDL", R"PDDL((define (problem p) (:domain d) (:init ) (:goal (and)) ))PDDL", 1, true},
{"swap", R"PDDL((define (domain d) (:requirements :adl :object-fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (f ?x - node) (g ?x - node) - node (pick) - node)  (:action run :parameters () :precondition (and) :effect (and (assign (f a) (f b)) (assign (f b) (f a))))))PDDL", R"PDDL((define (problem p) (:domain d) (:init (= (f a) b) (= (f b) a)) (:goal (and)) ))PDDL", 1, true},
{"old_address", R"PDDL((define (domain d) (:requirements :adl :object-fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (f ?x - node) (g ?x - node) - node (pick) - node)  (:action run :parameters () :precondition (and) :effect (and (assign (pick) b) (assign (f (pick)) b)))))PDDL", R"PDDL((define (problem p) (:domain d) (:init (= (pick) a) (= (f a) a)) (:goal (and)) ))PDDL", 1, true},
{"undefined_address", R"PDDL((define (domain d) (:requirements :adl :object-fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (f ?x - node) (g ?x - node) - node (pick) - node)  (:action run :parameters () :precondition (and) :effect (assign (f (pick)) a))))PDDL", R"PDDL((define (problem p) (:domain d) (:init ) (:goal (and)) ))PDDL", 1, true},
{"alias_conflict", R"PDDL((define (domain d) (:requirements :adl :object-fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (f ?x - node) (g ?x - node) - node (pick) - node)  (:action run :parameters () :precondition (and) :effect (and (assign (f (pick)) a) (assign (f a) a)))))PDDL", R"PDDL((define (problem p) (:domain d) (:init (= (pick) a)) (:goal (and)) ))PDDL", 1, true},
{"disjoint_writes", R"PDDL((define (domain d) (:requirements :adl :object-fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (f ?x - node) (g ?x - node) - node (pick) - node)  (:action run :parameters () :precondition (and) :effect (and (assign (f a) b) (assign (f b) a)))))PDDL", R"PDDL((define (problem p) (:domain d) (:init ) (:goal (and)) ))PDDL", 1, true},
{"predicate_address", R"PDDL((define (domain d) (:requirements :adl :object-fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (f ?x - node) (g ?x - node) - node (pick) - node)  (:action run :parameters () :precondition (and) :effect (and (assign (pick) b) (p (pick)) (not (p b))))))PDDL", R"PDDL((define (problem p) (:domain d) (:init (= (pick) a) (p b)) (:goal (and)) ))PDDL", 1, true},
{"predicate_undefined_address", R"PDDL((define (domain d) (:requirements :adl :object-fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (f ?x - node) (g ?x - node) - node (pick) - node)  (:action run :parameters () :precondition (and) :effect (p (pick)))))PDDL", R"PDDL((define (problem p) (:domain d) (:init ) (:goal (and)) ))PDDL", 1, true},
{"guard_false", R"PDDL((define (domain d) (:requirements :adl :object-fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (f ?x - node) (g ?x - node) - node (pick) - node)  (:action run :parameters () :precondition (and) :effect (when (done) (assign (f (pick)) (g b))))))PDDL", R"PDDL((define (problem p) (:domain d) (:init ) (:goal (and)) ))PDDL", 1, true},
{"guard_undefined", R"PDDL((define (domain d) (:requirements :adl :object-fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (f ?x - node) (g ?x - node) - node (pick) - node)  (:action run :parameters () :precondition (and) :effect (when (= (pick) a) (assign (f a) b)))))PDDL", R"PDDL((define (problem p) (:domain d) (:init ) (:goal (and)) ))PDDL", 1, true},
{"guard_old", R"PDDL((define (domain d) (:requirements :adl :object-fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (f ?x - node) (g ?x - node) - node (pick) - node)  (:action run :parameters () :precondition (and) :effect (and (assign (pick) b) (when (= (pick) a) (assign (f a) b))))))PDDL", R"PDDL((define (problem p) (:domain d) (:init (= (pick) a)) (:goal (and)) ))PDDL", 1, true},
{"forall_assign", R"PDDL((define (domain d) (:requirements :adl :object-fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (f ?x - node) (g ?x - node) - node (pick) - node)  (:action run :parameters () :precondition (and) :effect (forall (?x - node) (assign (f ?x) ?x)))))PDDL", R"PDDL((define (problem p) (:domain d) (:init ) (:goal (and)) ))PDDL", 1, true},
{"forall_alias_conflict", R"PDDL((define (domain d) (:requirements :adl :object-fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (f ?x - node) (g ?x - node) - node (pick) - node)  (:action run :parameters () :precondition (and) :effect (forall (?x - node) (assign (pick) ?x)))))PDDL", R"PDDL((define (problem p) (:domain d) (:init ) (:goal (and)) ))PDDL", 1, true},
{"two_steps", R"PDDL((define (domain d) (:requirements :adl :object-fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (f ?x - node) (g ?x - node) - node (pick) - node)  (:action run :parameters (?x - node) :precondition (and) :effect (assign (pick) ?x))))PDDL", R"PDDL((define (problem p) (:domain d) (:init ) (:goal (and)) ))PDDL", 2, true},
{"goal_after", R"PDDL((define (domain d) (:requirements :adl :object-fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (f ?x - node) (g ?x - node) - node (pick) - node)  (:action run :parameters () :precondition (and) :effect (assign (pick) b))))PDDL", R"PDDL((define (problem p) (:domain d) (:init ) (:goal (= (pick) b)) ))PDDL", 2, true},
{"derived_dynamic", R"PDDL((define (domain d) (:requirements :adl :object-fluents :derived-predicates) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (d)) (:functions (f ?x - node) (g ?x - node) - node (pick) - node) (:derived (d) (p (pick))) (:action run :parameters () :precondition (and) :effect (assign (pick) b))))PDDL", R"PDDL((define (problem p) (:domain d) (:init (= (pick) a) (p b)) (:goal (and)) ))PDDL", 1, true},
{"derived_nested_recursion", R"PDDL((define (domain d) (:requirements :adl :object-fluents :derived-predicates) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (d ?x - node)) (:functions (f ?x - node) (g ?x - node) - node (pick) - node) (:derived (d ?x) (or (p ?x) (d (f ?x)))) (:action run :parameters () :precondition (and) :effect (assign (f b) a))))PDDL", R"PDDL((define (problem p) (:domain d) (:init (= (f a) b) (= (f b) b) (p a)) (:goal (and)) ))PDDL", 1, true},
{"empty_argument", R"PDDL((define (domain d) (:requirements :adl :object-fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (f ?x - empty) - empty (pick) - node)  (:action run :parameters () :precondition (and) :effect (forall (?x - empty) (assign (f ?x) ?x)))))PDDL", R"PDDL((define (problem p) (:domain d) (:init ) (:goal (forall (?x - empty) (= (f ?x) ?x))) ))PDDL", 1, true},
{"empty_result", R"PDDL((define (domain d) (:requirements :adl :object-fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (f ?x - node) - empty)  ))PDDL", R"PDDL((define (problem p) (:domain d) (:init ) (:goal (and)) ))PDDL", 0, true},
{"union_return", R"PDDL((define (domain d) (:requirements :adl :object-fluents) (:types node place) (:constants a b - node c - place) (:predicates (p ?x - node) (done)) (:functions (pick) - (either place node))  (:action run :parameters (?x - (either node place)) :precondition (and) :effect (assign (pick) ?x))))PDDL", R"PDDL((define (problem p) (:domain d) (:init ) (:goal (and)) ))PDDL", 1, true},
{"grouped_return", R"PDDL((define (domain d) (:requirements :adl :fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (pick) (other) - node (n) - number)  ))PDDL", R"PDDL((define (problem p) (:domain d) (:init (= (pick) a) (= (other) b) (= (n) 2)) (:goal (and)) ))PDDL", 0, true},
{"numeric_dynamic", R"PDDL((define (domain d) (:requirements :adl :fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (pick) - node (n ?x - node) - number)  ))PDDL", R"PDDL((define (problem p) (:domain d) (:init (= (pick) b) (= (n a) 3) (= (n b) 7)) (:goal (= (n (pick)) 7)) ))PDDL", 0, true},
{"numeric_selected_undefined", R"PDDL((define (domain d) (:requirements :adl :fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (pick) - node (n ?x - node) - number)  ))PDDL", R"PDDL((define (problem p) (:domain d) (:init (= (pick) b) (= (n a) 3)) (:goal (= (n (pick)) 7)) ))PDDL", 0, true},
{"numeric_address_undefined", R"PDDL((define (domain d) (:requirements :adl :fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (pick) - node (n ?x - node) - number)  ))PDDL", R"PDDL((define (problem p) (:domain d) (:init (= (n a) 3) (= (n b) 7)) (:goal (= (n (pick)) 7)) ))PDDL", 0, true},
{"numeric_old_address", R"PDDL((define (domain d) (:requirements :adl :fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (pick) - node (n ?x - node) - number)  (:action run :parameters () :precondition (and) :effect (and (assign (pick) b) (increase (n (pick)) (n b))))))PDDL", R"PDDL((define (problem p) (:domain d) (:init (= (pick) a) (= (n a) 3) (= (n b) 7)) (:goal (and)) ))PDDL", 1, true},
{"numeric_guard_false", R"PDDL((define (domain d) (:requirements :adl :fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (pick) - node (n ?x - node) - number)  (:action run :parameters () :precondition (and) :effect (when (done) (increase (n (pick)) (n b))))))PDDL", R"PDDL((define (problem p) (:domain d) (:init ) (:goal (and)) ))PDDL", 1, true},
{"numeric_initialize_undefined", R"PDDL((define (domain d) (:requirements :adl :fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (pick) - node (n ?x - node) - number)  (:action run :parameters () :precondition (and) :effect (assign (n (pick)) 5))))PDDL", R"PDDL((define (problem p) (:domain d) (:init (= (pick) a)) (:goal (and)) ))PDDL", 1, true},
{"metric_minimize", R"PDDL((define (domain d) (:requirements :adl :fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (pick) - node (n ?x - node) - number)  (:action run :parameters (?x - node) :precondition (and) :effect (assign (pick) ?x))))PDDL", R"PDDL((define (problem p) (:domain d) (:init (= (pick) a) (= (n a) -3) (= (n b) 7)) (:goal (and)) (:metric minimize (+ (n (pick)) 2))))PDDL", 1, true},
{"metric_maximize", R"PDDL((define (domain d) (:requirements :adl :fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (pick) - node (n ?x - node) - number)  (:action run :parameters (?x - node) :precondition (and) :effect (assign (pick) ?x))))PDDL", R"PDDL((define (problem p) (:domain d) (:init (= (pick) a) (= (n a) -3) (= (n b) 7)) (:goal (and)) (:metric maximize (+ (n (pick)) 2))))PDDL", 1, true},
{"nullary_numeric", R"PDDL((define (domain d) (:requirements :adl :fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (pick) - node (n) - number)  (:action run :parameters () :precondition (and) :effect (increase (n) 2))))PDDL", R"PDDL((define (problem p) (:domain d) (:init (= n 3)) (:goal (and)) (:metric minimize n)))PDDL", 1, true},
{"same_predicate_function", R"PDDL((define (domain d) (:requirements :adl :object-fluents) (:types node empty) (:constants a b - node) (:predicates (pick) (p ?x - node)) (:functions (f ?x - node) (g ?x - node) - node (pick) - node)  (:action run :parameters () :precondition (and) :effect (and (p (pick)) (assign (pick) b)))))PDDL", R"PDDL((define (problem p) (:domain d) (:init (= (pick) a) (pick)) (:goal (and)) ))PDDL", 1, true},
{"bad_requirement", R"PDDL((define (domain d) (:requirements :adl) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (f ?x - node) (g ?x - node) - node (pick) - node)  ))PDDL", R"PDDL((define (problem p) (:domain d) (:init ) (:goal (and)) ))PDDL", 0, false},
{"bad_return", R"PDDL((define (domain d) (:requirements :adl :object-fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (pick) - missing)  ))PDDL", R"PDDL((define (problem p) (:domain d) (:init ) (:goal (and)) ))PDDL", 0, false},
{"bad_numeric_object_mixed", R"PDDL((define (domain d) (:requirements :adl :object-fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (pick) - node (n) - number)  ))PDDL", R"PDDL((define (problem p) (:domain d) (:init ) (:goal (and)) ))PDDL", 0, false},
{"bad_term_undefined", R"PDDL((define (domain d) (:requirements :adl :object-fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (f ?x - node) (g ?x - node) - node (pick) - node)  ))PDDL", R"PDDL((define (problem p) (:domain d) (:init ) (:goal (= (pick) undefined)) ))PDDL", 0, false},
{"bad_object_operator", R"PDDL((define (domain d) (:requirements :adl :object-fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (f ?x - node) (g ?x - node) - node (pick) - node)  (:action run :parameters () :precondition (and) :effect (increase (pick) a))))PDDL", R"PDDL((define (problem p) (:domain d) (:init ) (:goal (and)) ))PDDL", 0, false},
{"bad_rhs_type", R"PDDL((define (domain d) (:requirements :adl :object-fluents) (:types node place) (:constants a b - node c - place) (:predicates (p ?x - node) (done)) (:functions (f ?x - node) (g ?x - node) - node (pick) - node)  (:action run :parameters () :precondition (and) :effect (assign (pick) c))))PDDL", R"PDDL((define (problem p) (:domain d) (:init ) (:goal (and)) ))PDDL", 0, false},
{"bad_dynamic_argument", R"PDDL((define (domain d) (:requirements :adl :object-fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (pick) - object)  ))PDDL", R"PDDL((define (problem p) (:domain d) (:init ) (:goal (p (pick))) ))PDDL", 0, false},
{"bad_nested_arity", R"PDDL((define (domain d) (:requirements :adl :object-fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (f ?x - node) (g ?x - node) - node (pick) - node)  ))PDDL", R"PDDL((define (problem p) (:domain d) (:init ) (:goal (= (f a b) a)) ))PDDL", 0, false},
{"bad_init_nested", R"PDDL((define (domain d) (:requirements :adl :object-fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (f ?x - node) (g ?x - node) - node (pick) - node)  ))PDDL", R"PDDL((define (problem p) (:domain d) (:init (= (f (pick)) a) (= (pick) b)) (:goal (and)) ))PDDL", 0, false},
{"bad_init_undefined", R"PDDL((define (domain d) (:requirements :adl :object-fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (f ?x - node) (g ?x - node) - node (pick) - node)  ))PDDL", R"PDDL((define (problem p) (:domain d) (:init (= (pick) undefined)) (:goal (and)) ))PDDL", 0, false},
{"bad_init_duplicate", R"PDDL((define (domain d) (:requirements :adl :object-fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (f ?x - node) (g ?x - node) - node (pick) - node)  ))PDDL", R"PDDL((define (problem p) (:domain d) (:init (= (pick) a) (= (pick) a)) (:goal (and)) ))PDDL", 0, false},
{"bad_free_variable", R"PDDL((define (domain d) (:requirements :adl :object-fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (f ?x - node) (g ?x - node) - node (pick) - node)  (:action run :parameters () :precondition (and) :effect (assign (pick) ?x))))PDDL", R"PDDL((define (problem p) (:domain d) (:init ) (:goal (and)) ))PDDL", 0, false},
{"bad_derived_effect", R"PDDL((define (domain d) (:requirements :adl :object-fluents :derived-predicates) (:types node empty) (:constants a b - node) (:predicates (d ?x - node)) (:functions (f ?x - node) (g ?x - node) - node (pick) - node) (:derived (d ?x) (= ?x a)) (:action run :parameters () :precondition (and) :effect (d (pick)))))PDDL", R"PDDL((define (problem p) (:domain d) (:init ) (:goal (and)) ))PDDL", 0, false},
{"bad_temporal", R"PDDL((define (domain d) (:requirements :adl :object-fluents :durative-actions) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (f ?x - node) (g ?x - node) - node (pick) - node)  ))PDDL", R"PDDL((define (problem p) (:domain d) (:init ) (:goal (and)) ))PDDL", 0, true},
{"bad_boolean_return", R"PDDL((define (domain d) (:requirements :adl :object-fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (pick) - boolean)  ))PDDL", R"PDDL((define (problem p) (:domain d) (:init ) (:goal (and)) ))PDDL", 0, false},
{"bad_function_duplicate", R"PDDL((define (domain d) (:requirements :adl :fluents) (:types node empty) (:constants a b - node) (:predicates (p ?x - node) (done)) (:functions (pick) - node (pick) - number)  ))PDDL", R"PDDL((define (problem p) (:domain d) (:init ) (:goal (and)) ))PDDL", 0, false},
{"official_blocks", R"PDDL(;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; 4 Op-blocks world
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (domain BLOCKS-object-fluents)
  (:requirements :typing :equality :object-fluents)
  (:types block)

  (:constants no-block - block)

  (:predicates (on-table ?x - block))

  (:functions	(in-hand) - block
		(on-block ?x - block) - block) ;;what is in top of block ?x

  (:action pick-up
	     :parameters (?x - block)
	     :precondition (and (= (on-block ?x) no-block) (on-table ?x) (= (in-hand) no-block))
	     :effect
	     (and (not (on-table ?x))
		   (assign (in-hand) ?x)))

  (:action put-down
	     :parameters (?x - block)
	     :precondition (= (in-hand) ?x)
	     :effect
	     (and (assign (in-hand) no-block)
		   (on-table ?x)))

  (:action stack
	     :parameters (?x - block ?y - block)
	     :precondition (and (= (in-hand) ?x) (= (on-block ?y) no-block))
	     :effect
	     (and (assign (in-hand) no-block)
	   	  (assign (on-block ?y) ?x)))

  (:action unstack
	     :parameters (?x - block ?y - block)
	     :precondition (and (= (on-block ?y) ?x) (= (on-block ?x) no-block) (= (in-hand) no-block))
	     :effect
	     (and (assign (in-hand) ?x)
		  (assign (on-block ?y) no-block)))))PDDL", R"PDDL((define (problem BLOCKS-4-0)

(:domain BLOCKS-object-fluents)

(:objects D B A C - block)

(:INIT 	(= (on-block C) no-block) 
	(= (on-block A) no-block) 
	(= (on-block B) no-block) 
	(= (on-block D) no-block)
	(on-table C) 
	(on-table A)
	(on-table B) 
	(on-table D)
	(= (in-hand) no-block))

(:goal (AND (= (on-block C) D) (= (on-block B) C) (= (on-block A) B))))
)PDDL", 1, true},
{"official_logistics", R"PDDL(;; Logistics domain, PDDL 3.1 version.

(define (domain logistics-object-fluents)

(:requirements :typing :equality :object-fluents)

(:types package place city - object
        vehicle location - place
        airport - location
        truck airplane - vehicle)

(:functions (city-of ?l - location) - city
            (vehicle-location ?v - vehicle) - location
            (package-location ?p - package) - place)

(:action drive
         :parameters    (?t - truck ?l - location)
         :precondition  (= (city-of (vehicle-location ?t)) (city-of ?l))
         :effect        (assign (vehicle-location ?t) ?l))

(:action fly
         :parameters    (?a - airplane ?l - airport)
         :effect        (assign (vehicle-location ?a) ?l))

(:action load
         :parameters    (?p - package ?v - vehicle)
         :precondition  (= (package-location ?p) (vehicle-location ?v))
         :effect        (assign (package-location ?p) ?v))

(:action unload
         :parameters    (?p - package ?v - vehicle)
         :precondition  (= (package-location ?p) ?v)
         :effect        (assign (package-location ?p) (vehicle-location ?v)))

)
)PDDL", R"PDDL((define (problem logistics-4-0)

(:domain logistics-object-fluents)

(:objects  apn1 - airplane
           tru1 tru2 - truck
           obj11 obj12 obj13 obj21 obj22 obj23 - package
           apt1 apt2 - airport
           pos1 pos2 - location
           cit1 cit2 - city)

(:init  (= (vehicle-location apn1) apt2)
        (= (vehicle-location tru1) pos1)
        (= (vehicle-location tru2) pos2)
        (= (package-location obj11) pos1)
        (= (package-location obj12) pos1)
        (= (package-location obj13) pos1)
        (= (package-location obj21) pos2)
        (= (package-location obj22) pos2)
        (= (package-location obj23) pos2)
        (= (city-of apt1) cit1)
        (= (city-of apt2) cit2)
        (= (city-of pos1) cit1)
        (= (city-of pos2) cit2))

(:goal  (and (= (package-location obj11) apt1)
             (= (package-location obj13) apt1)
             (= (package-location obj21) pos1)
             (= (package-location obj23) pos1)))

)
)PDDL", 1, true},
{"official_depots", R"PDDL((define (domain Depot-object-fluents)
  (:requirements :typing :equality :fluents)
  (:types place locatable - object
	  depot distributor - place
	  truck hoist surface - locatable
	  pallet crate - surface)

  (:constants no-crate - crate)

  (:predicates
   (clear ?s - surface))

  (:functions
   (load-limit ?t - truck)
   (current-load ?t - truck)
   (weight ?c - crate)
   (fuel-cost) - number
   (position-of ?l - locatable) - place
   (crate-held ?h - hoist) - crate
   (thing-below ?c - crate) - (either surface truck))


  (:action drive
   :parameters (?t - truck ?p - place)
   :effect (and (assign (position-of ?t) ?p)
		(increase (fuel-cost) 10)))

  (:action lift
   :parameters (?h - hoist ?c - crate)
   :precondition (and (= (position-of ?h) (position-of ?c))
		      (= (crate-held ?h) no-crate)
		      (clear ?c))
   :effect (and (assign (crate-held ?h) ?c)
                (assign (position-of ?c) undefined)
		(assign (thing-below ?c) undefined)
		(clear (thing-below ?c))
		(increase (fuel-cost) 1)))

  (:action drop
   :parameters (?h - hoist ?c - crate ?s - surface)
   :precondition (and (= (position-of ?h) (position-of ?s))
                      (= (crate-held ?h) ?c)
		      (clear ?s))
   :effect (and (assign (crate-held ?h) no-crate)
                (assign (position-of ?c) (position-of ?h))
		(assign (thing-below ?c) ?s)
		(not (clear ?s))))

  (:action load
   :parameters (?h - hoist ?c - crate ?t - truck)
   :precondition (and (= (position-of ?h) (position-of ?t))
		      (= (crate-held ?h) ?c)
		      (<= (+ (current-load ?t) (weight ?c))
			  (load-limit ?t)))
   :effect (and (assign (crate-held ?h) no-crate)
		(assign (thing-below ?c) ?t)
		(increase (current-load ?t) (weight ?c))))

  (:action unload
   :parameters (?h - hoist ?c - crate ?t - truck)
   :precondition (and (= (position-of ?h) (position-of ?t))
		      (= (crate-held ?h) no-crate)
		      (= (thing-below ?c) ?t))
   :effect (and (assign (thing-below ?c) undefined)
		(assign (crate-held ?h) ?c)
		(decrease (current-load ?t) (weight ?c))))
  )
)PDDL", R"PDDL((define (problem depotprob1818)
  (:domain Depot-object-fluents)
  (:objects depot0 - Depot
	    distributor0 distributor1 - Distributor
	    truck0 truck1 - Truck
	    pallet0 pallet1 pallet2 - Pallet
	    crate0 crate1 - Crate
	    hoist0 hoist1 hoist2 - Hoist)
  (:init
   (= (position-of pallet0) depot0)
   (clear crate1)
   (= (position-of pallet1) distributor0)
   (clear crate0)
   (= (position-of pallet2) distributor1)
   (clear pallet2)
   (= (position-of truck0) distributor1)
   (= (current-load truck0) 0)
   (= (load-limit truck0) 323)
   (= (position-of truck1) depot0)
   (= (current-load truck1) 0)
   (= (load-limit truck1) 220)
   (= (position-of hoist0) depot0)
   (= (crate-held hoist0) no-crate)
   (= (position-of hoist1) distributor0)
   (= (crate-held hoist1) no-crate)
   (= (position-of hoist2) distributor1)
   (= (crate-held hoist2) no-crate)
   (= (position-of crate0) distributor0)
   (= (thing-below crate0) pallet1)
   (= (weight crate0) 11)
   (= (position-of crate1) depot0)
   (= (thing-below crate1) pallet0)
   (= (weight crate1) 86)
   (= (fuel-cost) 0))

  (:goal (and (= (thing-below crate0) pallet2)
	      (= (thing-below crate1) pallet1)))

  (:metric minimize (fuel-cost))
  )
)PDDL", 1, false}
