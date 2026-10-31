"""Exact PDDL3.0 trajectory and preference HIR constructors.

``planning_finite_trajectory`` implements AI2009 Figure 1 on the complete
finite happening sequence. ``planning_observed_trajectory`` quantifies over
the caller's complete observation domain; it never samples a continuous
trajectory. The latter is an explicit-domain extension, not an assertion
that PDDL3.0 defines every continuous boundary convention.

Both return a satisfaction expression and separate domain constraints.
``encoding.to_model(context, hard=True)`` asserts satisfaction in a new copy;
``hard=False`` adds only the domain relation for soft preference use. These
functions never mutate the supplied model. Preferences return exact counts,
never hard assertions. Unknown preference names are rejected by
``counts.violation_count(name)`` instead of being silently assigned zero.

Quantified object expansion and action-occurrence identity are explicit at
the caller: one PreferenceInstance per distinct grounded preference/selected
action occurrence. An outer preference wrapping forall is one instance with
conjunctive satisfaction. A preference inside forall has one per binding.
"""
from ._somtparser import (
    TrajectoryOperator, HirTrajectorySample, HirTrajectoryPoint,
    HirTrajectoryObservationDomain, HirTrajectoryEncoding,
    HirPreferenceInstance, HirPreferenceEncoding,
    planning_finite_trajectory, planning_observed_trajectory,
    planning_preferences, planning_preference_metric,
)

__all__ = [
    'TrajectoryOperator', 'HirTrajectorySample', 'HirTrajectoryPoint',
    'HirTrajectoryObservationDomain', 'HirTrajectoryEncoding',
    'HirPreferenceInstance', 'HirPreferenceEncoding',
    'planning_finite_trajectory', 'planning_observed_trajectory',
    'planning_preferences', 'planning_preference_metric',
]
