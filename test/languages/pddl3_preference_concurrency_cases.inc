static const std::vector<Pddl3PreferenceConcurrencyCase> cases{
{"start_true_same",R"PDDL((define (domain d) (:requirements :adl :fluents :durative-actions :derived-predicates :preferences) (:predicates (p) (d) (done-a) (done-b)) (:functions (x)) (:derived (d) (p)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (preference pref (at start (p))) :effect (and (at start (and)) (at end (done-a))))(:action b :parameters () :effect (and (not (p)) (done-b))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init (p) (= (x) 0)) (:goal (and (done-a) (done-b))) (:metric minimize (is-violated pref)))
)PDDL",2},
{"start_false_same",R"PDDL((define (domain d) (:requirements :adl :fluents :durative-actions :derived-predicates :preferences) (:predicates (p) (d) (done-a) (done-b)) (:functions (x)) (:derived (d) (p)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (preference pref (at start (not (p)))) :effect (and (at start (and)) (at end (done-a))))(:action b :parameters () :effect (and (not (p)) (done-b))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init (p) (= (x) 0)) (:goal (and (done-a) (done-b))) (:metric minimize (is-violated pref)))
)PDDL",2},
{"start_folded_same",R"PDDL((define (domain d) (:requirements :adl :fluents :durative-actions :derived-predicates :preferences) (:predicates (p) (d) (done-a) (done-b)) (:functions (x)) (:derived (d) (p)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (preference pref (at start (or (and) (p)))) :effect (and (at start (and)) (at end (done-a))))(:action b :parameters () :effect (and (not (p)) (done-b))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init (p) (= (x) 0)) (:goal (and (done-a) (done-b))) (:metric minimize (is-violated pref)))
)PDDL",2},
{"start_derived_same",R"PDDL((define (domain d) (:requirements :adl :fluents :durative-actions :derived-predicates :preferences) (:predicates (p) (d) (done-a) (done-b)) (:functions (x)) (:derived (d) (p)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (preference pref (at start (d))) :effect (and (at start (and)) (at end (done-a))))(:action b :parameters () :effect (and (not (p)) (done-b))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init (p) (= (x) 0)) (:goal (and (done-a) (done-b))) (:metric minimize (is-violated pref)))
)PDDL",2},
{"start_numeric_same",R"PDDL((define (domain d) (:requirements :adl :fluents :durative-actions :derived-predicates :preferences) (:predicates (p) (d) (done-a) (done-b)) (:functions (x)) (:derived (d) (p)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (preference pref (at start (>= (x) 0))) :effect (and (at start (and)) (at end (done-a))))(:action b :parameters () :effect (and (assign (x) 2) (done-b))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init (p) (= (x) 0)) (:goal (and (done-a) (done-b))) (:metric minimize (is-violated pref)))
)PDDL",2},
{"start_separated",R"PDDL((define (domain d) (:requirements :adl :fluents :durative-actions :derived-predicates :preferences) (:predicates (p) (d) (done-a) (done-b)) (:functions (x)) (:derived (d) (p)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (preference pref (at start (p))) :effect (and (at start (and)) (at end (done-a))))(:action b :parameters () :effect (and (not (p)) (done-b))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init (p) (= (x) 0)) (:goal (and (done-a) (done-b))) (:metric minimize (is-violated pref)))
)PDDL",2},
{"end_same",R"PDDL((define (domain d) (:requirements :adl :fluents :durative-actions :derived-predicates :preferences) (:predicates (p) (d) (done-a) (done-b)) (:functions (x)) (:derived (d) (p)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (preference pref (at end (p))) :effect (and (at start (and)) (at end (done-a))))(:action b :parameters () :effect (and (not (p)) (done-b))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init (p) (= (x) 0)) (:goal (and (done-a) (done-b))) (:metric minimize (is-violated pref)))
)PDDL",2},
{"end_numeric_same",R"PDDL((define (domain d) (:requirements :adl :fluents :durative-actions :derived-predicates :preferences) (:predicates (p) (d) (done-a) (done-b)) (:functions (x)) (:derived (d) (p)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (preference pref (at end (>= (x) 0))) :effect (and (at start (and)) (at end (done-a))))(:action b :parameters () :effect (and (assign (x) 2) (done-b))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init (p) (= (x) 0)) (:goal (and (done-a) (done-b))) (:metric minimize (is-violated pref)))
)PDDL",2},
{"end_separated",R"PDDL((define (domain d) (:requirements :adl :fluents :durative-actions :derived-predicates :preferences) (:predicates (p) (d) (done-a) (done-b)) (:functions (x)) (:derived (d) (p)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (preference pref (at end (p))) :effect (and (at start (and)) (at end (done-a))))(:action b :parameters () :effect (and (not (p)) (done-b))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init (p) (= (x) 0)) (:goal (and (done-a) (done-b))) (:metric minimize (is-violated pref)))
)PDDL",2},
{"overall_internal",R"PDDL((define (domain d) (:requirements :adl :fluents :durative-actions :derived-predicates :preferences) (:predicates (p) (d) (done-a) (done-b)) (:functions (x)) (:derived (d) (p)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (preference pref (over all (p))) :effect (and (at start (and)) (at end (done-a))))(:action b :parameters () :effect (and (not (p)) (done-b))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init (p) (= (x) 0)) (:goal (and (done-a) (done-b))) (:metric minimize (is-violated pref)))
)PDDL",2},
{"overall_own_end",R"PDDL((define (domain d) (:requirements :adl :fluents :durative-actions :derived-predicates :preferences) (:predicates (p) (d) (done-a) (done-b)) (:functions (x)) (:derived (d) (p)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (preference pref (over all (p))) :effect (and (at start (and)) (at end (done-a))))(:action b :parameters () :effect (and (not (p)) (done-b))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init (p) (= (x) 0)) (:goal (and (done-a) (done-b))) (:metric minimize (is-violated pref)))
)PDDL",2},
{"overall_own_start",R"PDDL((define (domain d) (:requirements :adl :fluents :durative-actions :derived-predicates :preferences) (:predicates (p) (d) (done-a) (done-b)) (:functions (x)) (:derived (d) (p)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (preference pref (over all (p))) :effect (and (at start (and)) (at end (done-a))))(:action b :parameters () :effect (and (not (p)) (done-b))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init (p) (= (x) 0)) (:goal (and (done-a) (done-b))) (:metric minimize (is-violated pref)))
)PDDL",2},
{"instant_same",R"PDDL((define (domain d) (:requirements :adl :fluents :durative-actions :derived-predicates :preferences) (:predicates (p) (d) (done-a) (done-b)) (:functions (x)) (:derived (d) (p)) (:action a :parameters () :precondition (preference pref (p)) :effect (and (and) (done-a)))(:action b :parameters () :effect (and (not (p)) (done-b))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init (p) (= (x) 0)) (:goal (and (done-a) (done-b))) (:metric minimize (is-violated pref)))
)PDDL",2},
{"same_owner_prop",R"PDDL((define (domain d) (:requirements :adl :fluents :durative-actions :derived-predicates :preferences) (:predicates (p) (d) (done-a) (done-b)) (:functions (x)) (:derived (d) (p)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (preference pref (at start (not (p)))) :effect (and (at start (not (p))) (at end (done-a)))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init (p) (= (x) 0)) (:goal (done-a)) (:metric minimize (is-violated pref)))
)PDDL",1},
{"same_owner_numeric",R"PDDL((define (domain d) (:requirements :adl :fluents :durative-actions :derived-predicates :preferences) (:predicates (p) (d) (done-a) (done-b)) (:functions (x)) (:derived (d) (p)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (preference pref (at start (> (x) 0))) :effect (and (at start (assign (x) 2)) (at end (done-a)))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init (p) (= (x) 0)) (:goal (done-a)) (:metric minimize (is-violated pref)))
)PDDL",1},
{"continuous_internal_pre",R"PDDL((define (domain d) (:requirements :adl :fluents :durative-actions :continuous-effects :preferences :derived-predicates)
    (:predicates (done-a) (done-b) (d)) (:functions (x)) (:derived (d) (< (x) 0))
    (:durative-action a :parameters () :duration (= ?duration 2)
     :condition (preference pref (over all (d))) :effect (and (increase (x) #t) (at end (done-a))))
    (:action b :parameters () :effect (and (assign (x) -1) (done-b))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init (= (x) -1)) (:goal (and (done-a) (done-b))) (:metric minimize (is-violated pref)))
)PDDL",2},
{"continuous_internal_post",R"PDDL((define (domain d) (:requirements :adl :fluents :durative-actions :continuous-effects :preferences :derived-predicates)
    (:predicates (done-a) (done-b) (d)) (:functions (x)) (:derived (d) (< (x) 0))
    (:durative-action a :parameters () :duration (= ?duration 2)
     :condition (preference pref (over all (d))) :effect (and (decrease (x) #t) (at end (done-a))))
    (:action b :parameters () :effect (and (assign (x) 0) (done-b))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init (= (x) -1)) (:goal (and (done-a) (done-b))) (:metric minimize (is-violated pref)))
)PDDL",2},
{"continuous_internal_valid",R"PDDL((define (domain d) (:requirements :adl :fluents :durative-actions :continuous-effects :preferences :derived-predicates)
    (:predicates (done-a) (done-b) (d)) (:functions (x)) (:derived (d) (< (x) 0))
    (:durative-action a :parameters () :duration (= ?duration 2)
     :condition (preference pref (over all (d))) :effect (and (increase (x) (* #t 0)) (at end (done-a))))
    (:action b :parameters () :effect (and (assign (x) -1) (done-b))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init (= (x) -1)) (:goal (and (done-a) (done-b))) (:metric minimize (is-violated pref)))
)PDDL",2},
};
