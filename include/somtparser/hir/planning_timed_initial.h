#ifndef SOMTPARSER_HIR_PLANNING_TIMED_INITIAL_HEADER
#define SOMTPARSER_HIR_PLANNING_TIMED_INITIAL_HEADER

#include "somtparser/hir/planning_temporal.h"

namespace SOMTParser::Uir::Hir::Planning {

struct TimedInitialLiteral {
    ExprPtr time; // Real. A source frontend supplies a positive exact constant.
    std::string proposition; // Canonical ground basic-fluent identity.
    bool value = true;
};

struct TimedInitialEncoding {
    std::vector<ExprPtr> constraints;
    // [event][happening]; each event is forced to match an active happening.
    std::vector<std::vector<ExprPtr>> matches;
    // Merge with action endpoint accesses before encodeTemporalInterference.
    std::vector<TemporalEndpointAccess> accesses;
};

/** Mandatory exogenous literal events. The caller also supplies happening
 * order, includes matches in occupied slots, and applies each matched literal
 * to its simultaneous basic-state transition. Events cannot be omitted just
 * because a goal has already been reached. Basic/derived classification and
 * source literal syntax are checked by the frontend, not inferred from names.
 * ownerPrefix must be disjoint from ordinary endpoint owner identities. */
std::optional<TimedInitialEncoding> encodeTimedInitialLiterals(
    const std::vector<TemporalHappening>& happenings,
    const std::vector<TimedInitialLiteral>& events,
    const std::string& ownerPrefix, Diagnostics& diagnostics);

struct StableGoalMakespan {
    // Append these constraints: lastActionEnd is 0 or an active happening,
    // and the final state achieves the goal.
    std::vector<ExprPtr> constraints;
    ExprPtr time;
};

/** PDDL2.2 stable-goal makespan, not the time of the last exogenous event.
 * goals has n+1 Boolean values: initial state, then each happening's post-state.
 * States are constant between ordered happenings; inactive suffix slots frame
 * the state. lastActionEnd is 0 for the empty action plan, otherwise its latest
 * actual action endpoint. Return the first state boundary at/after that time
 * from which the goal remains true through every later event. No arithmetic
 * sampling, epsilon, timestamp rounding or denominator bound is introduced. */
std::optional<StableGoalMakespan> encodeStableGoalMakespan(
    const std::vector<TemporalHappening>& happenings,
    const std::vector<ExprPtr>& goals, const ExprPtr& lastActionEnd,
    Diagnostics& diagnostics);

} // namespace SOMTParser::Uir::Hir::Planning
#endif
