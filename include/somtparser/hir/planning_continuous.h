#ifndef SOMTPARSER_HIR_PLANNING_CONTINUOUS_HEADER
#define SOMTPARSER_HIR_PLANNING_CONTINUOUS_HEADER

#include "somtparser/hir/planning_numeric.h"

namespace SOMTParser::Uir::Hir::Planning {

// INTERIOR means the ODE and its RHS definedness hold on (start,end).
// CLOSED_ONE_SIDED also requires RHS definedness and the corresponding
// relative-interval derivative at both endpoints. Choosing a policy is part
// of the source semantics: neither is silently substituted for the other.
enum class FlowDerivativeDomain { INTERIOR, CLOSED_ONE_SIDED };

struct ContinuousCoordinate {
    std::string trajectory_name; // Fresh Real -> Real source trajectory symbol.
    std::string variable;        // Real BOUND_VAR placeholder in rates/invariants.
    NumericStateCell initial;
    NumericStateCell terminal;
    ExprPtr active;              // Bool; continuous update actually writes this cell.
    NumericValue rate;           // Summed signed instantaneous rates, not #t*rate.
};

struct ContinuousInvariant {
    ExprPtr guard;               // Segment-constant Bool activation condition.
    NumericCondition condition; // Template over time/state BOUND_VAR placeholders.
    bool include_start = false;
    bool include_end = false;
};

struct ContinuousSegment {
    ExprPtr enabled;
    ExprPtr start;
    ExprPtr end;
    std::string time_variable;   // Absolute Real time placeholder, not elapsed time.
    // Callers must select this explicitly. In particular, selecting INTERIOR
    // does not establish derivatives or RHS definedness at the endpoints.
    std::optional<FlowDerivativeDomain> derivative_domain;
    std::vector<ContinuousCoordinate> coordinates;
    std::vector<ContinuousInvariant> invariants;
};

struct ContinuousEncoding {
    std::vector<FunDecl> trajectories;
    std::vector<ExprPtr> constraints;
    FlowDerivativeDomain derivative_domain;
    bool polynomial_witness = false;
    bool requires_trajectory_source_observations = true;
};

// Complete continuous trajectory relation over a *finite, positive-length*
// enabled interval. Every coordinate is continuous on the closed interval;
// its derivative equals the active rate (or zero) everywhere in the selected
// derivative domain. Every invariant is required at all points of its stated
// open/closed interval, with strict numeric definedness.
//
// Active writes require a defined initial value. Definedness never changes
// during continuous flow. An untouched undefined coordinate has canonical
// value/trajectory zero while its definedness stays false; this is not a
// readable initial numeric value. ASSIGN initialization is a discrete update.
// A disabled segment imposes NO constraints on external states or start/end;
// its private trajectory is canonically zero. The frontend supplies disabled
// state frames. Outside an enabled closed interval, trajectory values are
// also zero and are not claimed to be continuous there.
//
// General trajectories are declared observation functions (auxiliary=false),
// not undefined target helpers. A frontend must extend its source trajectory
// signature/projection when incorporating them. Every declared trajectory
// receives continuity, differential, boundary and outside-domain constraints.
// This is a relation on exact real functions. It does not prove uniqueness of
// an ODE solution or promise a decision procedure for quantified real/UF logic.
// The context is immutable and a failed call returns no partial encoding.
// Initial and terminal Real/Bool state identifiers are pairwise distinct,
// including across coordinates; desired equality is an explicit constraint.
std::optional<ContinuousEncoding> encodeContinuousSegment(
    const ConstraintModel& context, const ContinuousSegment& segment,
    Diagnostics& diagnostics);

// Explicit known-polynomial trajectory witness. coefficients[i][k] is the
// exact Real coefficient of (time-start)^k for coordinate i; coefficients
// are independent of all time/state placeholders. Symbolic differentiation
// and universal equality to the original rate replace epsilon-delta tests;
// continuity/differentiability follow from the supplied polynomial itself.
// Empty coefficient lists denote the exact zero polynomial.
//
// This verifies the specified witness, not existence of an arbitrary ODE
// solution. Guessing a finite degree must never be reported as a complete
// general ODE translation. Returned functions have exact define-fun bodies;
// they are auxiliary=true and add no uninterpreted trajectory freedom.
std::optional<ContinuousEncoding> encodePolynomialFlowWitness(
    const ConstraintModel& context, const ContinuousSegment& segment,
    const std::vector<std::vector<ExprPtr>>& coefficients,
    Diagnostics& diagnostics);

} // namespace SOMTParser::Uir::Hir::Planning
#endif
