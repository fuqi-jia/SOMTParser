#ifndef SOMTPARSER_HIR_PLANNING_TRAJECTORY_HEADER
#define SOMTPARSER_HIR_PLANNING_TRAJECTORY_HEADER

#include "somtparser/hir/planning_numeric.h"
#include <map>

namespace SOMTParser::Uir::Hir::Planning {

enum class TrajectoryOperator {
    AT_END, ALWAYS, SOMETIME, WITHIN, AT_MOST_ONCE,
    SOMETIME_BEFORE, SOMETIME_AFTER, ALWAYS_WITHIN, HOLD_DURING, HOLD_AFTER
};

struct TrajectorySample {
    ExprPtr active; // Bool; samples form a nonempty active prefix.
    ExprPtr time;   // Real; initial time is zero, active successor times strictly increase.
    NumericCondition first;
    // Required only for BEFORE, AFTER and ALWAYS_WITHIN; absent otherwise.
    std::optional<NumericCondition> second;
};

struct TrajectoryEncoding {
    // Shape/order constraints only. Satisfaction is deliberately NOT asserted:
    // a hard constraint asserts it; a soft preference merely measures it.
    std::vector<ExprPtr> domain_constraints;
    ExprPtr satisfied;
};

// PDDL3.0, Gerevini et al., Artificial Intelligence 173 (2009), Figure 1.
// Exact finite happening trajectory; it is NOT a sampled continuous trace.
// Bounds are exact Real expressions (PDDL frontends require numeric literals).
// lower is the sole bound for WITHIN, ALWAYS_WITHIN and HOLD_AFTER;
// HOLD_DURING additionally requires upper. Other operators reject bounds.
// AFTER permits a same-state witness; BEFORE is strict. HOLD_AFTER requires
// some state strictly later than lower, or the final state if the trace ends
// at/before lower. HOLD_DURING uses [lower,upper), the state spanning lower,
// and the final-state fallback from Figure 1, including unusual bound orders.
//
// Each state satisfaction is defined && value. Source negation satisfaction
// is defined && !value, never !satisfaction. The meta-level implication in
// BEFORE/AFTER is triggered by satisfaction, not by mere definedness. No
// undefined state is made readable. All terms are checked, even inactive ones.
std::optional<TrajectoryEncoding> encodeFiniteTrajectory(
    const ConstraintModel& context, TrajectoryOperator operation,
    const std::vector<TrajectorySample>& samples, ExprPtr lower, ExprPtr upper,
    Diagnostics& diagnostics);

struct TrajectoryPoint { ExprPtr time; ExprPtr phase; }; // Real, Int.
struct TrajectoryObservationDomain {
    std::string time_variable;  // Free Real BOUND_VAR placeholder.
    std::string phase_variable; // Free Int BOUND_VAR placeholder.
    ExprPtr contains;           // Bool template over these placeholders.
    TrajectoryPoint first;
    TrajectoryPoint last;
};

// Exact quantified extension to the explicitly supplied observation domain.
// Points are ordered lexicographically by (Real time, Int phase). The domain
// includes both declared endpoints, starts at time zero, and is bounded by
// them. All quantifiers range over contains; no finite sampling occurs.
// A caller can include open flow intervals and explicit pre/post happening
// points, specifying their phase order. This explicit-domain extension is
// separate from the paper's finite happening semantics, not a claim that the
// paper defines every possible continuous endpoint convention.
//
// AT_MOST_ONCE extends the finite relation by order-convexity of the true
// region, with source-false (defined && !value) after its end. HOLD_DURING
// includes every domain point in the window and its latest predecessor if
// present; dense domains need no fictitious sampled predecessor.
// Templates are capture-avoiding; context helpers must be well-scoped.
std::optional<TrajectoryEncoding> encodeObservedTrajectory(
    const ConstraintModel& context, const TrajectoryObservationDomain& domain,
    TrajectoryOperator operation, const NumericCondition& first,
    const std::optional<NumericCondition>& second, ExprPtr lower, ExprPtr upper,
    Diagnostics& diagnostics);

struct PreferenceInstance {
    std::string instance_id; // Unique grounded syntax/occurrence identity.
    std::string name;        // Empty means anonymous, not a named empty group.
    ExprPtr active;          // Action occurrence selection; true for goal preferences.
    ExprPtr satisfied;       // Complete trajectory/state satisfaction, Bool.
};
struct PreferenceEncoding {
    std::map<std::string, ExprPtr> named_violations; // Exact Int sums.
    ExprPtr anonymous_violations;                  // Exact Int sum.
};

// A preference never restricts plan validity. Its violation is
// ite(active && !satisfied, 1, 0), once per unique instance, not per bad state.
// For a state preference pass numericSatisfied(condition): undefined makes
// that preference violated, not the plan illegal. For modal preferences use
// the complete modal satisfaction above, preserving vacuous implications.
// (preference p (forall x ...)) is ONE instance with conjunctive satisfaction;
// (forall x (preference p ...)) supplies one instance per grounded x.
// Action precondition preferences supply distinct IDs per executed occurrence,
// including quantified bindings; a durative invariant is one whole-interval
// satisfaction, never a charge per observation. Duplicate IDs are refused.
// declared_names registers names whose grounding/occurrence set may be empty;
// they correctly have count zero. Unknown metric names remain caller errors.
std::optional<PreferenceEncoding> encodePreferences(
    const ConstraintModel& context, const std::vector<PreferenceInstance>& instances,
    Diagnostics& diagnostics, const std::vector<std::string>& declared_names = {});

// Anonymous preferences have implicit unit cost: add for minimization,
// subtract for maximization. Named counts enter only an explicit metric.
// Int and Real base metrics are supported without approximate coercion.
std::optional<ExprPtr> preferenceMetric(
    const ConstraintModel& context, ExprPtr base, const PreferenceEncoding& preferences,
    bool minimize, Diagnostics& diagnostics);

} // namespace SOMTParser::Uir::Hir::Planning
#endif
