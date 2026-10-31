#ifndef SOMTPARSER_LOWER_POSITIVE_EXISTS_HEADER
#define SOMTPARSER_LOWER_POSITIVE_EXISTS_HEADER

#include "somtparser/hir/hir.h"

namespace SOMTParser::Lower {

struct ExistentialWitness {
    std::size_t constraint_index;
    std::size_t quantifier_index;
    std::string bound_name;
    std::string symbol_name;
    Uir::Hir::Sort sort;
};

/** Lift hard-constraint top-level positive existential prefixes to fresh,
 *  auxiliary declarations. Only conjunctions and existential prefixes are
 *  traversed. Negation, reification, disjunction, implications, universal
 *  scopes, soft constraints, definitions and objectives remain scoped.
 *
 *  Requires a type-checked model. The result has exactly the same projection
 *  onto every original free symbol and therefore the same ordered objective
 *  values. Witness multiplicity is NOT a model-count preservation claim.
 *  Expressions are immutable; shared caller-owned expressions are untouched.
 */
std::vector<ExistentialWitness> liftPositiveExists(Uir::Hir::ConstraintModel& model);

} // namespace SOMTParser::Lower
#endif
