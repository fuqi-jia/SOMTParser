#ifndef SOMTPARSER_HIR_PACKED_CLAUSE_IO_HEADER
#define SOMTPARSER_HIR_PACKED_CLAUSE_IO_HEADER

#include "somtparser/hir/hir.h"
#include "somtparser/translation/diagnostic.h"

#include <iosfwd>
#include <string>

namespace SOMTParser::Uir::Hir {

/** Validate and stream the exact SMT-LIB form of a packed Boolean clause model.
 *
 * This deliberately accepts only the packed-clause HIR subset: no ordinary
 * declarations, constraints, functions, objectives, or extra sorts. The caller
 * must have run typeCheck(model) successfully. It emits declarations in range
 * order, hard clauses as assert, and soft clauses as assert-soft with their
 * original exact decimal weights. No per-variable or per-clause HIR nodes are
 * allocated. Returns false and records a diagnostic on unsupported/malformed
 * models or stream errors.
 */
bool validatePackedBoolClauseModel(const ConstraintModel& model,
                                   Diagnostics& diags);
bool writePackedBoolClausesSmt2(const ConstraintModel& model,
                                std::ostream& out,
                                Diagnostics& diags,
                                const std::string& gomt_soft_objective = {});
// A nonempty gomt_soft_objective is an already-declared GOMT MaxSMT objective
// symbol. Each soft clause targets it with :objective. The caller owns the
// enable-omt/define-maxsmt-objective preamble and optimize-sat query. An empty
// name preserves vendor assert-soft syntax; OptiMathSAT additionally requires
// its caller to activate the unnamed group with (minimize I).

} // namespace SOMTParser::Uir::Hir

#endif
