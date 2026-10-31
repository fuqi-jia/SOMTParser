"""Public typed planning constructors for the shared native HIR.

Composition and mutation are explicit:

* Numeric, temporal and object constructors return expressions or constraint lists;
  they never append constraints to a model. Attach each returned constraint
  with ``model.constrain(expression)`` before translating.
* Object lookups expose obligations in ``constraints`` and guarded read
  metadata. Attach every obligation and retain object/numeric read namespaces
  when composing endpoint interference. Undefined-value and concurrent-writer
  policies are explicit arguments, never implicit defaults.
* Timed initial event constructors return constraints, matching expressions
  and endpoint accesses. Callers also compose state updates, happening order
  and interference; event placement alone is not a complete plan encoding.
* ``planning_derived_closure(model, ...)`` appends its validated declaration
  and constraint delta to that model. It returns the closure values and
  dependency information. Callers explicitly equate their observation atoms
  to the returned values. Invalid constructions leave the model unchanged.
* Trajectory constructors separate observation-domain constraints from modal
  satisfaction. For preferences, retain domain constraints and use the
  violation count; assert satisfaction only for hard constraints.
* Continuous constructors leave their context unchanged and return an
  encoding. ``encoding.to_model(context)`` creates a validated model copy
  containing the trajectory declarations and every flow constraint.

General continuous trajectories carry full continuity, differential and
invariant constraints; arbitrary ODE solving is not promised. A polynomial
witness checks a supplied curve and is not a complete search over solutions.
These constructors do not themselves establish PDDL frontend coverage.

The classes and planning functions below are native re-exports. The three
expression helpers build typed HIR nodes without evaluating source code or
parsing SMT. Native validation and translation retain their usual errors.
"""
from . import _somtparser as _native
from ._somtparser import (
    HirModel, HirSort, HirExpr,
    HirNumericStateCell, HirNumericValue, HirNumericCondition,
    NumericUpdateKind, HirNumericUpdate,
    planning_numeric_constant, planning_numeric_read,
    planning_numeric_arithmetic, planning_numeric_compare,
    planning_numeric_predicate, planning_numeric_logical,
    planning_numeric_satisfied, planning_numeric_transition,
    planning_derived_closure,
    HirRationalTimeCoordinate, HirTemporalHappening, HirDurativeOccurrence,
    HirTemporalConditionSamples, HirDurativeEncoding,
    TemporalEffectEndpoint, HirTemporalEndpointAccess,
    planning_temporal_rational_time, planning_temporal_happening_order,
    planning_temporal_durative_occurrence, planning_temporal_effect_guard,
    planning_temporal_interference,
    HirTimedInitialLiteral, HirTimedInitialEncoding, HirStableGoalMakespan,
    planning_timed_initial_literals, planning_stable_goal_makespan,
    FlowDerivativeDomain, HirContinuousCoordinate, HirContinuousInvariant,
    HirContinuousSegment, HirContinuousEncoding,
    planning_continuous_segment, planning_polynomial_flow_witness,
    HirObjectTypeDeclaration,
    HirPlanningObject,
    HirObjectType,
    HirObjectUniverse,
    HirObjectStateCell,
    HirObjectReadAccess,
    HirObjectValue,
    HirObjectCondition,
    ObjectUndefinedPolicy,
    ObjectAssignmentPolicy,
    HirObjectTable,
    HirObjectDispatch,
    HirObjectNumericValue,
    HirObjectAddress,
    HirObjectUpdate,
    planning_object_carrier,
    planning_object_subtype,
    planning_object_constant,
    planning_object_read,
    planning_object_equal,
    planning_object_logical,
    planning_object_satisfied,
    planning_object_dispatch,
    planning_object_lookup,
    planning_object_predicate,
    planning_object_numeric_lookup,
    planning_object_address,
    planning_object_transition,
    planning_object_initial_state,
    TrajectoryOperator,
    HirTrajectorySample,
    HirTrajectoryPoint,
    HirTrajectoryObservationDomain,
    HirTrajectoryEncoding,
    HirPreferenceInstance,
    HirPreferenceEncoding,
    planning_finite_trajectory,
    planning_observed_trajectory,
    planning_preferences,
    planning_preference_metric,
)


def literal(sort, text):
    """Build an exact typed literal, e.g. Real ``'1/3'`` or Bool ``'true'``.

    Text is passed unchanged to the native constructor. Python floats are
    not converted to decimal approximations and Bool is not coerced to Int.
    """
    return _native._hir_literal(sort, text)


def bound_variable(name, sort):
    """Build a bound-variable placeholder; this does not declare a free symbol.

    Continuous segment templates bind their time and coordinate placeholders.
    Other bound variables require their own enclosing HIR binder.
    """
    return _native._hir_ident(name, sort, True)


def operation(name, arguments):
    """Build a HIR operation using native names such as ``eq`` or ``add``.

    ``planning_numeric_arithmetic`` and ``planning_numeric_compare`` instead
    accept their documented PDDL-style names such as ``+`` and ``=`` and
    additionally propagate numeric definedness and read dependencies.
    """
    return _native._hir_op(name, arguments)


__all__ = [
    'HirModel', 'HirSort', 'HirExpr', 'literal', 'bound_variable', 'operation',
    'HirNumericStateCell', 'HirNumericValue', 'HirNumericCondition',
    'NumericUpdateKind', 'HirNumericUpdate',
    'planning_numeric_constant', 'planning_numeric_read',
    'planning_numeric_arithmetic', 'planning_numeric_compare',
    'planning_numeric_predicate', 'planning_numeric_logical',
    'planning_numeric_satisfied', 'planning_numeric_transition',
    'planning_derived_closure',
    'HirRationalTimeCoordinate', 'HirTemporalHappening', 'HirDurativeOccurrence',
    'HirTemporalConditionSamples', 'HirDurativeEncoding',
    'TemporalEffectEndpoint', 'HirTemporalEndpointAccess',
    'planning_temporal_rational_time', 'planning_temporal_happening_order',
    'planning_temporal_durative_occurrence', 'planning_temporal_effect_guard',
    'planning_temporal_interference',
    'HirTimedInitialLiteral', 'HirTimedInitialEncoding', 'HirStableGoalMakespan',
    'planning_timed_initial_literals', 'planning_stable_goal_makespan',
    'FlowDerivativeDomain', 'HirContinuousCoordinate', 'HirContinuousInvariant',
    'HirContinuousSegment', 'HirContinuousEncoding',
    'planning_continuous_segment', 'planning_polynomial_flow_witness',
    'HirObjectTypeDeclaration',
    'HirPlanningObject',
    'HirObjectType',
    'HirObjectUniverse',
    'HirObjectStateCell',
    'HirObjectReadAccess',
    'HirObjectValue',
    'HirObjectCondition',
    'ObjectUndefinedPolicy',
    'ObjectAssignmentPolicy',
    'HirObjectTable',
    'HirObjectDispatch',
    'HirObjectNumericValue',
    'HirObjectAddress',
    'HirObjectUpdate',
    'planning_object_carrier',
    'planning_object_subtype',
    'planning_object_constant',
    'planning_object_read',
    'planning_object_equal',
    'planning_object_logical',
    'planning_object_satisfied',
    'planning_object_dispatch',
    'planning_object_lookup',
    'planning_object_predicate',
    'planning_object_numeric_lookup',
    'planning_object_address',
    'planning_object_transition',
    'planning_object_initial_state',
    'TrajectoryOperator',
    'HirTrajectorySample',
    'HirTrajectoryPoint',
    'HirTrajectoryObservationDomain',
    'HirTrajectoryEncoding',
    'HirPreferenceInstance',
    'HirPreferenceEncoding',
    'planning_finite_trajectory',
    'planning_observed_trajectory',
    'planning_preferences',
    'planning_preference_metric',
]
