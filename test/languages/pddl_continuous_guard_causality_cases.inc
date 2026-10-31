// Static source fixtures. No solver result is implied by this file.
const std::vector<ContinuousGuardCase> cases{
    {"end_guard", R"PDDL((define (domain guards) (:requirements :adl :fluents :durative-actions :continuous-effects) (:types item) (:constants a b - item) (:predicates (p) (done)) (:functions (x)) (:durative-action flow :parameters () :duration (= ?duration 1) :condition () :effect (when (at end (p)) (increase (x) #t))))
)PDDL", R"PDDL((define (problem guard-task) (:domain guards) (:init (= (x) 0) (p)) (:goal (and)) (:metric minimize total-time))
)PDDL", false},
    {"interval_guard", R"PDDL((define (domain guards) (:requirements :adl :fluents :durative-actions :continuous-effects) (:types item) (:constants a b - item) (:predicates (p) (done)) (:functions (x)) (:durative-action flow :parameters () :duration (= ?duration 1) :condition () :effect (when (over all (p)) (increase (x) #t))))
)PDDL", R"PDDL((define (problem guard-task) (:domain guards) (:init (= (x) 0) (p)) (:goal (and)) (:metric minimize total-time))
)PDDL", false},
    {"mixed_guard", R"PDDL((define (domain guards) (:requirements :adl :fluents :durative-actions :continuous-effects) (:types item) (:constants a b - item) (:predicates (p) (done)) (:functions (x)) (:durative-action flow :parameters () :duration (= ?duration 1) :condition () :effect (when (and (at start (p)) (over all (p))) (increase (x) #t))))
)PDDL", R"PDDL((define (problem guard-task) (:domain guards) (:init (= (x) 0) (p)) (:goal (and)) (:metric minimize total-time))
)PDDL", false},
    {"quantified_interval_guard", R"PDDL((define (domain guards) (:requirements :adl :fluents :durative-actions :continuous-effects) (:types item) (:constants a b - item) (:predicates (p) (done)) (:functions (x)) (:durative-action flow :parameters () :duration (= ?duration 1) :condition () :effect (forall (?o - item) (when (over all (p)) (increase (x) #t)))))
)PDDL", R"PDDL((define (problem guard-task) (:domain guards) (:init (= (x) 0) (p)) (:goal (and)) (:metric minimize total-time))
)PDDL", false},
    {"self_justifying_end_guard", R"PDDL((define (domain guards) (:requirements :adl :fluents :durative-actions :continuous-effects) (:types item) (:constants a b - item) (:predicates (p) (done)) (:functions (x)) (:durative-action flow :parameters () :duration (= ?duration 1) :condition () :effect (when (at end (> (x) 0)) (increase (x) #t))))
)PDDL", R"PDDL((define (problem guard-task) (:domain guards) (:init (= (x) 0) (p)) (:goal (and)) (:metric minimize total-time))
)PDDL", false},
    {"self_defeating_end_guard", R"PDDL((define (domain guards) (:requirements :adl :fluents :durative-actions :continuous-effects) (:types item) (:constants a b - item) (:predicates (p) (done)) (:functions (x)) (:durative-action flow :parameters () :duration (= ?duration 1) :condition () :effect (when (at end (< (x) 1)) (increase (x) #t))))
)PDDL", R"PDDL((define (problem guard-task) (:domain guards) (:init (= (x) 0) (p)) (:goal (and)) (:metric minimize total-time))
)PDDL", false},
    {"start_guard", R"PDDL((define (domain guards) (:requirements :adl :fluents :durative-actions :continuous-effects) (:types item) (:constants a b - item) (:predicates (p) (done)) (:functions (x)) (:durative-action flow :parameters () :duration (= ?duration 1) :condition () :effect (when (at start (p)) (increase (x) #t))))
)PDDL", R"PDDL((define (problem guard-task) (:domain guards) (:init (= (x) 0) (p)) (:goal (and)) (:metric minimize total-time))
)PDDL", true},
    {"start_guard_remembers_prestate", R"PDDL((define (domain guards) (:requirements :adl :fluents :durative-actions :continuous-effects) (:types item) (:constants a b - item) (:predicates (p) (done)) (:functions (x)) (:durative-action flow :parameters () :duration (= ?duration 1) :condition () :effect (and (at start (not (p))) (when (at start (p)) (increase (x) #t)))))
)PDDL", R"PDDL((define (problem guard-task) (:domain guards) (:init (= (x) 0) (p)) (:goal (and)) (:metric minimize total-time))
)PDDL", true},
    {"interval_guard_at_end_effect", R"PDDL((define (domain guards) (:requirements :adl :fluents :durative-actions :continuous-effects) (:types item) (:constants a b - item) (:predicates (p) (done)) (:functions (x)) (:durative-action flow :parameters () :duration (= ?duration 1) :condition () :effect (and (increase (x) #t) (when (over all (p)) (at end (done))))))
)PDDL", R"PDDL((define (problem guard-task) (:domain guards) (:init (= (x) 0) (p)) (:goal (and)) (:metric minimize total-time))
)PDDL", true},
    {"end_guard_at_end_effect", R"PDDL((define (domain guards) (:requirements :adl :fluents :durative-actions :continuous-effects) (:types item) (:constants a b - item) (:predicates (p) (done)) (:functions (x)) (:durative-action flow :parameters () :duration (= ?duration 1) :condition () :effect (and (increase (x) #t) (when (at end (p)) (at end (done))))))
)PDDL", R"PDDL((define (problem guard-task) (:domain guards) (:init (= (x) 0) (p)) (:goal (and)) (:metric minimize total-time))
)PDDL", true},
};
