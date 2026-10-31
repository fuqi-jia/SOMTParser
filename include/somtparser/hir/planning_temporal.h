/* Discrete temporal planning constructions over the shared typed HIR. */
#ifndef SOMTPARSER_HIR_PLANNING_TEMPORAL_HEADER
#define SOMTPARSER_HIR_PLANNING_TEMPORAL_HEADER

#include "somtparser/hir/hir.h"

#include <optional>
#include <set>
#include <string>
#include <vector>

namespace SOMTParser::Uir::Hir::Planning {

/** An optional happening, in a prefix of strictly increasing positive times.
 * Multiple action endpoints can occupy the same happening. Inactive suffix
 * slots do not constrain their time or represent source events. */
struct TemporalHappening {
    ExprPtr active;
    ExprPtr time;
};

/** An exact, unbounded rational coordinate represented in the Real target.
 * Integer numerator/denominator are witnesses, not a precision or step bound.
 * PDDL source timestamps require this extra constraint; a general temporal
 * HIR construction can instead use the Real-time APIs directly. */
struct RationalTimeCoordinate {
    ExprPtr time;
    ExprPtr numerator;
    ExprPtr denominator;
};

std::optional<std::vector<ExprPtr>> encodeRationalTime(
    const RationalTimeCoordinate& coordinate, const ExprPtr& active,
    Diagnostics& diagnostics);

/** One source action occurrence, including its own symbolic start and end.
 * Repeated or overlapping uses of one ground action need separate occurrences.
 * A duration of zero is not removed here: the source duration constraint and
 * endpoint interference determine whether it is admissible. */
struct DurativeOccurrence {
    ExprPtr active;
    ExprPtr start;
    ExprPtr end;
};

/** State-indexed conditions for a discrete trace with n happening slots.
 * atStart/atEnd, when present, have n entries evaluated in the state BEFORE
 * each happening. overAll has n-1 entries evaluated AFTER each happening,
 * throughout the following open interval. Empty vectors mean no condition.
 *
 * This contract requires piecewise-constant state between happenings. A
 * continuous-effect frontend must supply separate trajectory obligations;
 * checking these samples does not prove a continuous invariant. */
struct TemporalConditionSamples {
    std::vector<ExprPtr> atStart;
    std::vector<ExprPtr> atEnd;
    std::vector<ExprPtr> overAll;
};

struct DurativeEncoding {
    std::vector<ExprPtr> constraints;
    ExprPtr duration;
};

enum class TemporalEffectEndpoint { START, END };

/** Accesses of one applicable flattened endpoint branch. Include every
 * syntactic precondition read (including an inactive disjunct) and explicit
 * numeric RHS read. An additive update's implicit accumulator is a write,
 * not an extra read. Derived reads include their base-fluent dependencies.
 * Canonical fluent identities, not printed/concatenated argument names, are
 * required. A branch activation includes its conditional-effect guards. */
struct TemporalEndpointAccess {
    ExprPtr active;
    ExprPtr time;
    std::set<std::string> propositionReads;
    std::set<std::string> propositionAdds;
    std::set<std::string> propositionDeletes;
    std::set<std::string> numericReads;
    std::set<std::string> numericWrites;
    std::set<std::string> additiveWrites;
    // Records for guards and separate effects of one endpoint share an owner.
    // Different endpoint owners are checked against each other. Empty owners
    // retain the independent-record behavior.
    std::string owner_id;
};

/** Pure builders: on error no partial constraints are attached to a model.
 * The resulting model still passes the ordinary full HIR type checker. */
std::optional<std::vector<ExprPtr>> encodeHappeningOrder(
    const std::vector<TemporalHappening>& happenings, Diagnostics& diagnostics);

/** Match both endpoints to active happenings, preserve the duration and
 * require every applicable endpoint/interval condition. Include duration
 * tests in the appropriate atStart/atEnd samples, using end-start. */
std::optional<DurativeEncoding> encodeDurativeOccurrence(
    const std::vector<TemporalHappening>& happenings,
    const DurativeOccurrence& occurrence,
    const TemporalConditionSamples& conditions, Diagnostics& diagnostics);

/** Compute a history-sensitive effect guard from this occurrence's original
 * samples. Invariant-like conditional guards do NOT become required plan
 * conditions. START effects cannot depend on END or overAll conditions. */
ExprPtr temporalEffectGuard(
    const std::vector<TemporalHappening>& happenings,
    const DurativeOccurrence& occurrence,
    const TemporalConditionSamples& conditions,
    TemporalEffectEndpoint endpoint, Diagnostics& diagnostics);

/** PDDL's no-moving-targets/interference rule for simultaneous endpoints.
 * Numeric writes may overlap only when BOTH endpoints update additively.
 * This constrains concurrency; numeric/Boolean frame and update equations
 * must also be emitted by the shared state-transition construction. */
std::optional<std::vector<ExprPtr>> encodeTemporalInterference(
    const std::vector<TemporalEndpointAccess>& endpoints, Diagnostics& diagnostics);

} // namespace SOMTParser::Uir::Hir::Planning
#endif
