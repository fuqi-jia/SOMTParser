static const std::vector<Pddl3TemporalCase> cases{
{"at_end_hard",R"PDDL((define (domain d) (:requirements :adl :preferences :constraints :durative-actions :fluents) (:types item) (:constants i j - item) (:predicates (p) (q)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (and) :effect (and (at start (p)) (at end (not (p))) (at end (q)))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init) (:goal (q)) (:constraints (at end (p))) )
)PDDL",1,true},
{"at_end_soft",R"PDDL((define (domain d) (:requirements :adl :preferences :constraints :durative-actions :fluents) (:types item) (:constants i j - item) (:predicates (p) (q)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (and) :effect (and (at start (p)) (at end (not (p))) (at end (q)))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init) (:goal (q)) (:constraints (preference pref (at end (p)))) (:metric minimize (is-violated pref)))
)PDDL",1,true},
{"always_hard",R"PDDL((define (domain d) (:requirements :adl :preferences :constraints :durative-actions :fluents) (:types item) (:constants i j - item) (:predicates (p) (q)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (and) :effect (and (at start (p)) (at end (not (p))) (at end (q)))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init) (:goal (q)) (:constraints (always (p))) )
)PDDL",1,true},
{"always_soft",R"PDDL((define (domain d) (:requirements :adl :preferences :constraints :durative-actions :fluents) (:types item) (:constants i j - item) (:predicates (p) (q)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (and) :effect (and (at start (p)) (at end (not (p))) (at end (q)))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init) (:goal (q)) (:constraints (preference pref (always (p)))) (:metric minimize (is-violated pref)))
)PDDL",1,true},
{"sometime_hard",R"PDDL((define (domain d) (:requirements :adl :preferences :constraints :durative-actions :fluents) (:types item) (:constants i j - item) (:predicates (p) (q)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (and) :effect (and (at start (p)) (at end (not (p))) (at end (q)))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init) (:goal (q)) (:constraints (sometime (q))) )
)PDDL",1,true},
{"sometime_soft",R"PDDL((define (domain d) (:requirements :adl :preferences :constraints :durative-actions :fluents) (:types item) (:constants i j - item) (:predicates (p) (q)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (and) :effect (and (at start (p)) (at end (not (p))) (at end (q)))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init) (:goal (q)) (:constraints (preference pref (sometime (q)))) (:metric minimize (is-violated pref)))
)PDDL",1,true},
{"within_hard",R"PDDL((define (domain d) (:requirements :adl :preferences :constraints :durative-actions :fluents) (:types item) (:constants i j - item) (:predicates (p) (q)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (and) :effect (and (at start (p)) (at end (not (p))) (at end (q)))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init) (:goal (q)) (:constraints (within 2 (q))) )
)PDDL",1,true},
{"within_soft",R"PDDL((define (domain d) (:requirements :adl :preferences :constraints :durative-actions :fluents) (:types item) (:constants i j - item) (:predicates (p) (q)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (and) :effect (and (at start (p)) (at end (not (p))) (at end (q)))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init) (:goal (q)) (:constraints (preference pref (within 2 (q)))) (:metric minimize (is-violated pref)))
)PDDL",1,true},
{"at_most_once_hard",R"PDDL((define (domain d) (:requirements :adl :preferences :constraints :durative-actions :fluents) (:types item) (:constants i j - item) (:predicates (p) (q)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (and) :effect (and (at start (p)) (at end (not (p))) (at end (q)))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init) (:goal (q)) (:constraints (at-most-once (p))) )
)PDDL",1,true},
{"at_most_once_soft",R"PDDL((define (domain d) (:requirements :adl :preferences :constraints :durative-actions :fluents) (:types item) (:constants i j - item) (:predicates (p) (q)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (and) :effect (and (at start (p)) (at end (not (p))) (at end (q)))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init) (:goal (q)) (:constraints (preference pref (at-most-once (p)))) (:metric minimize (is-violated pref)))
)PDDL",1,true},
{"before_hard",R"PDDL((define (domain d) (:requirements :adl :preferences :constraints :durative-actions :fluents) (:types item) (:constants i j - item) (:predicates (p) (q)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (and) :effect (and (at start (p)) (at end (not (p))) (at end (q)))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init) (:goal (q)) (:constraints (sometime-before (p) (q))) )
)PDDL",1,true},
{"before_soft",R"PDDL((define (domain d) (:requirements :adl :preferences :constraints :durative-actions :fluents) (:types item) (:constants i j - item) (:predicates (p) (q)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (and) :effect (and (at start (p)) (at end (not (p))) (at end (q)))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init) (:goal (q)) (:constraints (preference pref (sometime-before (p) (q)))) (:metric minimize (is-violated pref)))
)PDDL",1,true},
{"after_hard",R"PDDL((define (domain d) (:requirements :adl :preferences :constraints :durative-actions :fluents) (:types item) (:constants i j - item) (:predicates (p) (q)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (and) :effect (and (at start (p)) (at end (not (p))) (at end (q)))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init) (:goal (q)) (:constraints (sometime-after (p) (q))) )
)PDDL",1,true},
{"after_soft",R"PDDL((define (domain d) (:requirements :adl :preferences :constraints :durative-actions :fluents) (:types item) (:constants i j - item) (:predicates (p) (q)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (and) :effect (and (at start (p)) (at end (not (p))) (at end (q)))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init) (:goal (q)) (:constraints (preference pref (sometime-after (p) (q)))) (:metric minimize (is-violated pref)))
)PDDL",1,true},
{"always_within_hard",R"PDDL((define (domain d) (:requirements :adl :preferences :constraints :durative-actions :fluents) (:types item) (:constants i j - item) (:predicates (p) (q)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (and) :effect (and (at start (p)) (at end (not (p))) (at end (q)))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init) (:goal (q)) (:constraints (always-within 1 (p) (q))) )
)PDDL",1,true},
{"always_within_soft",R"PDDL((define (domain d) (:requirements :adl :preferences :constraints :durative-actions :fluents) (:types item) (:constants i j - item) (:predicates (p) (q)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (and) :effect (and (at start (p)) (at end (not (p))) (at end (q)))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init) (:goal (q)) (:constraints (preference pref (always-within 1 (p) (q)))) (:metric minimize (is-violated pref)))
)PDDL",1,true},
{"hold_during_hard",R"PDDL((define (domain d) (:requirements :adl :preferences :constraints :durative-actions :fluents) (:types item) (:constants i j - item) (:predicates (p) (q)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (and) :effect (and (at start (p)) (at end (not (p))) (at end (q)))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init) (:goal (q)) (:constraints (hold-during 1 3 (p))) )
)PDDL",1,true},
{"hold_during_soft",R"PDDL((define (domain d) (:requirements :adl :preferences :constraints :durative-actions :fluents) (:types item) (:constants i j - item) (:predicates (p) (q)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (and) :effect (and (at start (p)) (at end (not (p))) (at end (q)))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init) (:goal (q)) (:constraints (preference pref (hold-during 1 3 (p)))) (:metric minimize (is-violated pref)))
)PDDL",1,true},
{"hold_after_hard",R"PDDL((define (domain d) (:requirements :adl :preferences :constraints :durative-actions :fluents) (:types item) (:constants i j - item) (:predicates (p) (q)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (and) :effect (and (at start (p)) (at end (not (p))) (at end (q)))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init) (:goal (q)) (:constraints (hold-after 2 (p))) )
)PDDL",1,true},
{"hold_after_soft",R"PDDL((define (domain d) (:requirements :adl :preferences :constraints :durative-actions :fluents) (:types item) (:constants i j - item) (:predicates (p) (q)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (and) :effect (and (at start (p)) (at end (not (p))) (at end (q)))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init) (:goal (q)) (:constraints (preference pref (hold-after 2 (p)))) (:metric minimize (is-violated pref)))
)PDDL",1,true},
{"action_start",R"PDDL((define (domain d) (:requirements :adl :preferences :constraints :durative-actions :fluents) (:types item) (:constants i j - item) (:predicates (p) (q)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (preference pref (at start (p))) :effect (and (at start (p)) (at end (not (p))) (at end (q)))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init) (:goal (q))  (:metric minimize (is-violated pref)))
)PDDL",1,true},
{"action_end",R"PDDL((define (domain d) (:requirements :adl :preferences :constraints :durative-actions :fluents) (:types item) (:constants i j - item) (:predicates (p) (q)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (preference pref (at end (p))) :effect (and (at start (p)) (at end (not (p))) (at end (q)))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init) (:goal (q))  (:metric minimize (is-violated pref)))
)PDDL",1,true},
{"action_overall",R"PDDL((define (domain d) (:requirements :adl :preferences :constraints :durative-actions :fluents) (:types item) (:constants i j - item) (:predicates (p) (q)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (preference pref (over all (p))) :effect (and (at start (p)) (at end (not (p))) (at end (q)))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init) (:goal (q))  (:metric minimize (is-violated pref)))
)PDDL",1,true},
{"action_overall_false",R"PDDL((define (domain d) (:requirements :adl :preferences :constraints :durative-actions :fluents) (:types item) (:constants i j - item) (:predicates (p) (q)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (preference pref (over all (not (p)))) :effect (and (at start (p)) (at end (not (p))) (at end (q)))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init) (:goal (q))  (:metric minimize (is-violated pref)))
)PDDL",1,true},
{"action_overall_overlap",R"PDDL((define (domain d) (:requirements :adl :preferences :constraints :durative-actions :fluents) (:types item) (:constants i j - item) (:predicates (p) (q)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (preference pref (over all (p))) :effect (and (at start (p)) (at end (not (p))) (at end (q)))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init) (:goal (q))  (:metric minimize (is-violated pref)))
)PDDL",2,true},
{"action_start_overlap",R"PDDL((define (domain d) (:requirements :adl :preferences :constraints :durative-actions :fluents) (:types item) (:constants i j - item) (:predicates (p) (q)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (preference pref (at start (p))) :effect (and (at start (p)) (at end (not (p))) (at end (q)))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init) (:goal (q))  (:metric minimize (is-violated pref)))
)PDDL",2,true},
{"action_quantified",R"PDDL((define (domain d) (:requirements :adl :preferences :constraints :durative-actions :fluents) (:types item) (:constants i j - item) (:predicates (p) (q)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (forall (?x - item) (preference pref (at start (p)))) :effect (and (at start (p)) (at end (not (p))) (at end (q)))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init) (:goal (q))  (:metric minimize (is-violated pref)))
)PDDL",1,true},
{"action_undefined",R"PDDL((define (domain d) (:requirements :adl :preferences :constraints :durative-actions :fluents) (:types item) (:constants i j - item) (:predicates (p) (q)) (:functions (x))(:durative-action a :parameters () :duration (= ?duration 2) :condition (preference pref (over all (> (x) 0))) :effect (and (at start (p)) (at end (not (p))) (at end (q)))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init) (:goal (q))  (:metric minimize (is-violated pref)))
)PDDL",1,true},
{"instant_duplicate",R"PDDL((define (domain d) (:requirements :adl :preferences :constraints :durative-actions :fluents) (:types item) (:constants i j - item) (:predicates (p) (q)) (:action a :parameters () :precondition (preference pref (p)) :effect (q)))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init) (:goal (q))  (:metric minimize (is-violated pref)))
)PDDL",2,true},
{"anonymous_max",R"PDDL((define (domain d) (:requirements :adl :preferences :constraints :durative-actions :fluents) (:types item) (:constants i j - item) (:predicates (p) (q)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (preference (at start (p))) :effect (and (at start (p)) (at end (not (p))) (at end (q)))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init) (:goal (q))  (:metric maximize (- 10 total-time)))
)PDDL",1,true},
{"undefined_goal",R"PDDL((define (domain d) (:requirements :adl :preferences :constraints :durative-actions :fluents) (:types item) (:constants i j - item) (:predicates (p) (q)) (:functions (x))(:durative-action a :parameters () :duration (= ?duration 2) :condition (and) :effect (and (at start (p)) (at end (not (p))) (at end (q)))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init) (:goal (and (q) (preference pref (> (x) 0))))  (:metric minimize (is-violated pref)))
)PDDL",1,true},
{"empty_named",R"PDDL((define (domain d) (:requirements :adl :preferences :constraints :durative-actions :fluents) (:types item empty) (:constants i j - item) (:predicates (p) (q)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (and) :effect (and (at start (p)) (at end (not (p))) (at end (q)))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init) (:goal (and (q) (forall (?x - empty) (preference pref (p)))))  (:metric minimize (is-violated pref)))
)PDDL",1,true},
{"continuous_always_soft",R"PDDL((define (domain d) (:requirements :adl :fluents :durative-actions :continuous-effects :derived-predicates :constraints :preferences)
(:predicates (q) (d)) (:functions (x) (y)) (:derived (d) (< (x) 1))
(:durative-action a :parameters () :duration (= ?duration 1) :condition (and)
 :effect (and (increase (y) #t) (increase (x) (* #t (- 4 (* 8 (y))))) (at end (q)))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init (= (x) 0) (= (y) 0)) (:goal (q)) (:constraints (preference pref (always (d)))) (:metric minimize (is-violated pref)))
)PDDL",1,true},
{"continuous_always_hard",R"PDDL((define (domain d) (:requirements :adl :fluents :durative-actions :continuous-effects :derived-predicates :constraints :preferences)
(:predicates (q) (d)) (:functions (x) (y)) (:derived (d) (< (x) 1))
(:durative-action a :parameters () :duration (= ?duration 1) :condition (and)
 :effect (and (increase (y) #t) (increase (x) (* #t (- 4 (* 8 (y))))) (at end (q)))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init (= (x) 0) (= (y) 0)) (:goal (q)) (:constraints (always (d))) )
)PDDL",1,true},
{"continuous_sometime",R"PDDL((define (domain d) (:requirements :adl :fluents :durative-actions :continuous-effects :derived-predicates :constraints :preferences)
(:predicates (q) (d)) (:functions (x) (y)) (:derived (d) (< (x) 1))
(:durative-action a :parameters () :duration (= ?duration 1) :condition (and)
 :effect (and (increase (y) #t) (increase (x) (* #t (- 4 (* 8 (y))))) (at end (q)))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init (= (x) 0) (= (y) 0)) (:goal (q)) (:constraints (preference pref (sometime (>= (x) 1)))) (:metric minimize (is-violated pref)))
)PDDL",1,true},
{"continuous_at_most_once",R"PDDL((define (domain d) (:requirements :adl :fluents :durative-actions :continuous-effects :derived-predicates :constraints :preferences)
(:predicates (q) (d)) (:functions (x) (y)) (:derived (d) (< (x) 1))
(:durative-action a :parameters () :duration (= ?duration 1) :condition (and)
 :effect (and (increase (y) #t) (increase (x) (* #t (- 4 (* 8 (y))))) (at end (q)))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init (= (x) 0) (= (y) 0)) (:goal (q)) (:constraints (preference pref (at-most-once (d)))) (:metric minimize (is-violated pref)))
)PDDL",1,true},
{"continuous_overall",R"PDDL((define (domain d) (:requirements :adl :fluents :durative-actions :continuous-effects :derived-predicates :constraints :preferences)
(:predicates (q) (d)) (:functions (x) (y)) (:derived (d) (< (x) 1))
(:durative-action a :parameters () :duration (= ?duration 1) :condition (preference pref (over all (d)))
 :effect (and (increase (y) #t) (increase (x) (* #t (- 4 (* 8 (y))))) (at end (q)))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init (= (x) 0) (= (y) 0)) (:goal (q))  (:metric minimize (is-violated pref)))
)PDDL",1,true},
{"reject_inside_time",R"PDDL((define (domain d) (:requirements :adl :preferences :constraints :durative-actions :fluents) (:types item) (:constants i j - item) (:predicates (p) (q)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (at start (preference pref (p))) :effect (and (at start (p)) (at end (not (p))) (at end (q)))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init) (:goal (q))  )
)PDDL",0,false},
{"reject_multiple_timed",R"PDDL((define (domain d) (:requirements :adl :preferences :constraints :durative-actions :fluents) (:types item) (:constants i j - item) (:predicates (p) (q)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (preference pref (and (at start (p)) (at end (q)))) :effect (and (at start (p)) (at end (not (p))) (at end (q)))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init) (:goal (q))  )
)PDDL",0,false},
{"reject_nontimed",R"PDDL((define (domain d) (:requirements :adl :preferences :constraints :durative-actions :fluents) (:types item) (:constants i j - item) (:predicates (p) (q)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (preference pref (p)) :effect (and (at start (p)) (at end (not (p))) (at end (q)))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init) (:goal (q))  )
)PDDL",0,false},
{"reject_nested",R"PDDL((define (domain d) (:requirements :adl :preferences :constraints :durative-actions :fluents) (:types item) (:constants i j - item) (:predicates (p) (q)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (preference outer (at start (preference inner (p)))) :effect (and (at start (p)) (at end (not (p))) (at end (q)))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init) (:goal (q))  )
)PDDL",0,false},
{"reject_empty_bad",R"PDDL((define (domain d) (:requirements :adl :preferences :constraints :durative-actions :fluents) (:types item) (:constants i j - item) (:predicates (p) (q)) (:durative-action a :parameters () :duration (= ?duration 2) :condition (forall (?x - item) (preference pref (at start (missing ?x)))) :effect (and (at start (p)) (at end (not (p))) (at end (q)))))
)PDDL",R"PDDL((define (problem t) (:domain d) (:init) (:goal (q))  )
)PDDL",0,false},
};
