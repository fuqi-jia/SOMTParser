#ifndef SOMTPARSER_HIR_PLANNING_NUMERIC_HEADER
#define SOMTPARSER_HIR_PLANNING_NUMERIC_HEADER

#include "somtparser/hir/hir.h"
#include <cstddef>
#include <optional>
#include <string>
#include <vector>

namespace SOMTParser::Uir::Hir::Planning {

// PDDL2.1 numeric states range over Real plus undefined. The value carried by
// an undefined state cell is canonical zero, never an unconstrained number.
struct NumericStateCell {
    ExprPtr value;    // Real IDENT, declared in the supplied context.
    ExprPtr defined;  // Bool IDENT, declared in the supplied context.
};

struct NumericValue {
    ExprPtr value;    // Real expression.
    ExprPtr defined;  // Bool expression; evaluation is legal iff this holds.
    std::vector<std::size_t> reads; // Explicit old-state PNE reads, sorted/unique.
};

struct NumericCondition {
    ExprPtr value;
    ExprPtr defined;
    std::vector<std::size_t> reads;
};

std::optional<NumericValue> numericConstant(const std::string& exact,
                                           Diagnostics& diagnostics);
std::optional<NumericValue> numericRead(const NumericStateCell& cell,
                                       std::size_t index, Diagnostics& diagnostics);
std::optional<NumericValue> numericArithmetic(Op op, const std::vector<NumericValue>& args,
                                             Diagnostics& diagnostics);
std::optional<NumericCondition> numericCompare(Op op, const NumericValue& lhs,
                                               const NumericValue& rhs,
                                               Diagnostics& diagnostics);
std::optional<NumericCondition> numericPredicate(ExprPtr predicate,
                                                 Diagnostics& diagnostics);
// Logical combination is strict in definedness (Fox/Long 2003, Definition 9).
// In particular, neither NOT(undefined) nor OR(true, undefined) is satisfied.
std::optional<NumericCondition> numericLogical(Op op,
                                               const std::vector<NumericCondition>& args,
                                               Diagnostics& diagnostics);
ExprPtr numericSatisfied(const NumericCondition& condition);

enum class NumericUpdateKind { ASSIGN, INCREASE, DECREASE, SCALE_UP, SCALE_DOWN };

struct NumericUpdate {
    std::size_t target_index = 0;
    NumericUpdateKind kind = NumericUpdateKind::ASSIGN;
    NumericValue rhs;
    ExprPtr guard; // Complete selection AND conditional-effect guard, Bool.
    std::string owner_id; // Ground action/endpoint identity; not schema identity.
};

struct NumericTransition {
    std::vector<ExprPtr> constraints;
};

// Build simultaneous old-state updates and exact frames. Active right-hand
// sides must be defined. ASSIGN can initialize an undefined cell; relative
// updates require its old value. Conditional guard definedness must be required
// under its enclosing action selection by the caller, even when guard is false.
// Multiple additive updates combine. Within one owner, scaling updates combine;
// distinct owners may share a target only for additive writes. Simple assignment
// duplicates and mixed assignment families are excluded by activation constraints.
// Explicit RHS reads are left in NumericValue::reads for the caller's complete
// no-moving-targets check (precondition reads belong to the same access set).
// The implicit old accumulator of INCREASE/DECREASE is not an explicit RHS read.
// No future state cell may occur in a guard or RHS, including through a
// reachable defined function body. RHS read metadata likewise includes the
// free old-state identifiers captured by reachable definitions (BOUND_VAR
// formal parameters are lexical, and actual arguments are checked directly).
// Entire terms are typechecked
// against context, including terms unreachable under a constant-false guard.
std::optional<NumericTransition> buildNumericTransition(
    const ConstraintModel& context,
    const std::vector<NumericStateCell>& before,
    const std::vector<NumericStateCell>& after,
    const std::vector<NumericUpdate>& updates,
    Diagnostics& diagnostics);

} // namespace SOMTParser::Uir::Hir::Planning
#endif
