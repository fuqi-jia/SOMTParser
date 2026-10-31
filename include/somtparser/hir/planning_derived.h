#ifndef SOMTPARSER_HIR_PLANNING_DERIVED_HEADER
#define SOMTPARSER_HIR_PLANNING_DERIVED_HEADER

#include "somtparser/hir/hir.h"
#include "somtparser/translation/diagnostic.h"
#include <optional>
#include <set>

namespace SOMTParser::Uir::Hir::Planning {

/** One ground rule: a satisfied body derives atoms[head]. Numeric source
 * conditions must include their source-definedness guard in body. */
struct DerivedRule {
    std::size_t head = 0;
    ExprPtr body;
    SourceLoc loc;
};

struct DerivedClosure {
    std::vector<VarDecl> declarations;
    std::vector<Constraint> constraints;
    /** One value per input atom, in input order. Append the declarations and
     * constraints before using these values. The context is never modified. */
    std::vector<ExprPtr> values;
    /** Transitive syntactic reads, including negative basic conditions and
     * reads inside numeric expressions/definedness guards. These are needed
     * when deriving action interference, not just for formula construction. */
    std::vector<std::set<std::string>> base_dependencies;
    std::vector<std::set<std::string>> base_function_dependencies;
    std::size_t rounds = 0;
};

/** Exact least fixed point over a caller-supplied complete finite universe.
 *
 * atoms are distinct, declared Bool IDENTs in context; they serve as rule
 * placeholders and are not constrained by this function. values describe the
 * least solution, independently of any current values of those placeholders.
 * A frontend may equate its derived state observations to the returned values.
 *
 * Starting at all false, N synchronous inflationary rounds suffice for N
 * ground derived atoms: every non-fixed round adds at least one atom. N is a
 * semantic bound, not a user-selected unfolding depth. All generated equations
 * depend only on earlier layers, so unseeded recursion cannot justify itself.
 *
 * Derived occurrences must be positive through AND/OR/NOT/IMPLIES and Boolean
 * ITE branches (whose condition is independent of derived atoms). Other
 * contexts containing derived occurrences are rejected. Binder shadowing and
 * hidden derived captures in defined functions are rejected. Ordinary basic
 * subexpressions retain their complete well-typed HIR semantics.
 */
std::optional<DerivedClosure> buildDerivedClosure(
    const ConstraintModel& context, const std::vector<ExprPtr>& atoms,
    const std::vector<DerivedRule>& rules, const std::string& prefix,
    Diagnostics& diagnostics);

} // namespace SOMTParser::Uir::Hir::Planning
#endif
