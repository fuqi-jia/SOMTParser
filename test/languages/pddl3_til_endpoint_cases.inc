static const std::vector<TilEndpointCase> cases{
{"rise_sometime_hard",R"PDDL((define (domain til-endpoint)
  (:requirements :strips :negative-preconditions :durative-actions
                 :timed-initial-literals :constraints :preferences)
  (:predicates (g) (p)))
)PDDL",R"PDDL((define (problem rise_sometime_hard) (:domain til-endpoint)
  (:init (g) (at 10 (p)))
  (:goal (g))
  (:constraints (sometime (p)))
  (:metric minimize total-time))
)PDDL"},
{"rise_sometime_soft",R"PDDL((define (domain til-endpoint)
  (:requirements :strips :negative-preconditions :durative-actions
                 :timed-initial-literals :constraints :preferences)
  (:predicates (g) (p)))
)PDDL",R"PDDL((define (problem rise_sometime_soft) (:domain til-endpoint)
  (:init (g) (at 10 (p)))
  (:goal (g))
  (:constraints (preference late (sometime (p))))
  (:metric minimize (+ total-time (* 7 (is-violated late)))))
)PDDL"},
{"rise_at_end_hard",R"PDDL((define (domain til-endpoint)
  (:requirements :strips :negative-preconditions :durative-actions
                 :timed-initial-literals :constraints :preferences)
  (:predicates (g) (p)))
)PDDL",R"PDDL((define (problem rise_at_end_hard) (:domain til-endpoint)
  (:init (g) (at 10 (p)))
  (:goal (g))
  (:constraints (at end (p)))
  (:metric minimize total-time))
)PDDL"},
{"rise_at_end_soft",R"PDDL((define (domain til-endpoint)
  (:requirements :strips :negative-preconditions :durative-actions
                 :timed-initial-literals :constraints :preferences)
  (:predicates (g) (p)))
)PDDL",R"PDDL((define (problem rise_at_end_soft) (:domain til-endpoint)
  (:init (g) (at 10 (p)))
  (:goal (g))
  (:constraints (preference late (at end (p))))
  (:metric minimize (+ total-time (* 7 (is-violated late)))))
)PDDL"},
{"rise_hold_after_hard",R"PDDL((define (domain til-endpoint)
  (:requirements :strips :negative-preconditions :durative-actions
                 :timed-initial-literals :constraints :preferences)
  (:predicates (g) (p)))
)PDDL",R"PDDL((define (problem rise_hold_after_hard) (:domain til-endpoint)
  (:init (g) (at 10 (p)))
  (:goal (g))
  (:constraints (hold-after 5 (p)))
  (:metric minimize total-time))
)PDDL"},
{"rise_hold_after_soft",R"PDDL((define (domain til-endpoint)
  (:requirements :strips :negative-preconditions :durative-actions
                 :timed-initial-literals :constraints :preferences)
  (:predicates (g) (p)))
)PDDL",R"PDDL((define (problem rise_hold_after_soft) (:domain til-endpoint)
  (:init (g) (at 10 (p)))
  (:goal (g))
  (:constraints (preference late (hold-after 5 (p))))
  (:metric minimize (+ total-time (* 7 (is-violated late)))))
)PDDL"},
{"rise_combined_max",R"PDDL((define (domain til-endpoint)
  (:requirements :strips :negative-preconditions :durative-actions
                 :timed-initial-literals :constraints :preferences)
  (:predicates (g) (p)))
)PDDL",R"PDDL((define (problem rise_combined_max) (:domain til-endpoint)
  (:init (g) (at 10 (p)))
  (:goal (g))
  (:constraints (and (preference late (sometime (p))) (preference late (at end (p))) (preference late (hold-after 5 (p)))))
  (:metric maximize (- 31 (+ total-time (* 7 (is-violated late))))))
)PDDL"},
{"rise_always_not_soft",R"PDDL((define (domain til-endpoint)
  (:requirements :strips :negative-preconditions :durative-actions
                 :timed-initial-literals :constraints :preferences)
  (:predicates (g) (p)))
)PDDL",R"PDDL((define (problem rise_always_not_soft) (:domain til-endpoint)
  (:init (g) (at 10 (p)))
  (:goal (g))
  (:constraints (preference safe (always (not (p)))))
  (:metric minimize (+ total-time (* 7 (is-violated safe)))))
)PDDL"},
{"rise_goal_soft",R"PDDL((define (domain til-endpoint)
  (:requirements :strips :negative-preconditions :durative-actions
                 :timed-initial-literals :constraints :preferences)
  (:predicates (g) (p)))
)PDDL",R"PDDL((define (problem rise_goal_soft) (:domain til-endpoint)
  (:init (g) (at 10 (p)))
  (:goal (and (g) (preference wanted (p))))
  (:constraints (and))
  (:metric minimize (+ total-time (* 7 (is-violated wanted)))))
)PDDL"},
{"fall_sometime_hard",R"PDDL((define (domain til-endpoint)
  (:requirements :strips :negative-preconditions :durative-actions
                 :timed-initial-literals :constraints :preferences)
  (:predicates (g) (p)))
)PDDL",R"PDDL((define (problem fall_sometime_hard) (:domain til-endpoint)
  (:init (g) (at 10 (p)) (at 12 (not (p))))
  (:goal (g))
  (:constraints (sometime (p)))
  (:metric minimize total-time))
)PDDL"},
{"fall_sometime_soft",R"PDDL((define (domain til-endpoint)
  (:requirements :strips :negative-preconditions :durative-actions
                 :timed-initial-literals :constraints :preferences)
  (:predicates (g) (p)))
)PDDL",R"PDDL((define (problem fall_sometime_soft) (:domain til-endpoint)
  (:init (g) (at 10 (p)) (at 12 (not (p))))
  (:goal (g))
  (:constraints (preference late (sometime (p))))
  (:metric minimize (+ total-time (* 7 (is-violated late)))))
)PDDL"},
{"fall_at_end_hard",R"PDDL((define (domain til-endpoint)
  (:requirements :strips :negative-preconditions :durative-actions
                 :timed-initial-literals :constraints :preferences)
  (:predicates (g) (p)))
)PDDL",R"PDDL((define (problem fall_at_end_hard) (:domain til-endpoint)
  (:init (g) (at 10 (p)) (at 12 (not (p))))
  (:goal (g))
  (:constraints (at end (p)))
  (:metric minimize total-time))
)PDDL"},
{"fall_at_end_soft",R"PDDL((define (domain til-endpoint)
  (:requirements :strips :negative-preconditions :durative-actions
                 :timed-initial-literals :constraints :preferences)
  (:predicates (g) (p)))
)PDDL",R"PDDL((define (problem fall_at_end_soft) (:domain til-endpoint)
  (:init (g) (at 10 (p)) (at 12 (not (p))))
  (:goal (g))
  (:constraints (preference late (at end (p))))
  (:metric minimize (+ total-time (* 7 (is-violated late)))))
)PDDL"},
{"fall_hold_after_hard",R"PDDL((define (domain til-endpoint)
  (:requirements :strips :negative-preconditions :durative-actions
                 :timed-initial-literals :constraints :preferences)
  (:predicates (g) (p)))
)PDDL",R"PDDL((define (problem fall_hold_after_hard) (:domain til-endpoint)
  (:init (g) (at 10 (p)) (at 12 (not (p))))
  (:goal (g))
  (:constraints (hold-after 5 (p)))
  (:metric minimize total-time))
)PDDL"},
{"fall_hold_after_soft",R"PDDL((define (domain til-endpoint)
  (:requirements :strips :negative-preconditions :durative-actions
                 :timed-initial-literals :constraints :preferences)
  (:predicates (g) (p)))
)PDDL",R"PDDL((define (problem fall_hold_after_soft) (:domain til-endpoint)
  (:init (g) (at 10 (p)) (at 12 (not (p))))
  (:goal (g))
  (:constraints (preference late (hold-after 5 (p))))
  (:metric minimize (+ total-time (* 7 (is-violated late)))))
)PDDL"},
{"fall_combined_max",R"PDDL((define (domain til-endpoint)
  (:requirements :strips :negative-preconditions :durative-actions
                 :timed-initial-literals :constraints :preferences)
  (:predicates (g) (p)))
)PDDL",R"PDDL((define (problem fall_combined_max) (:domain til-endpoint)
  (:init (g) (at 10 (p)) (at 12 (not (p))))
  (:goal (g))
  (:constraints (and (preference late (sometime (p))) (preference late (at end (p))) (preference late (hold-after 5 (p)))))
  (:metric maximize (- 31 (+ total-time (* 7 (is-violated late))))))
)PDDL"},
{"fall_always_not_soft",R"PDDL((define (domain til-endpoint)
  (:requirements :strips :negative-preconditions :durative-actions
                 :timed-initial-literals :constraints :preferences)
  (:predicates (g) (p)))
)PDDL",R"PDDL((define (problem fall_always_not_soft) (:domain til-endpoint)
  (:init (g) (at 10 (p)) (at 12 (not (p))))
  (:goal (g))
  (:constraints (preference safe (always (not (p)))))
  (:metric minimize (+ total-time (* 7 (is-violated safe)))))
)PDDL"},
{"fall_goal_soft",R"PDDL((define (domain til-endpoint)
  (:requirements :strips :negative-preconditions :durative-actions
                 :timed-initial-literals :constraints :preferences)
  (:predicates (g) (p)))
)PDDL",R"PDDL((define (problem fall_goal_soft) (:domain til-endpoint)
  (:init (g) (at 10 (p)) (at 12 (not (p))))
  (:goal (and (g) (preference wanted (p))))
  (:constraints (and))
  (:metric minimize (+ total-time (* 7 (is-violated wanted)))))
)PDDL"},
};
