#ifndef SOMTPARSER_HIR_PACKED_LINEAR_IO_HEADER
#define SOMTPARSER_HIR_PACKED_LINEAR_IO_HEADER

#include "somtparser/hir/hir.h"
#include "somtparser/translation/diagnostic.h"

#include <iosfwd>
#include <string>
#include <vector>

namespace SOMTParser::Lower { class HirToParser; }

namespace SOMTParser::Uir::Hir {

/** Check every row, span, numeric declaration reference, source location and
 * exact decimal. Called by ordinary HIR typeCheck; does not recursively call
 * typeCheck itself. No row expression trees are constructed. */
bool validatePackedLinearRows(const ConstraintModel& model, Diagnostics& diags);

/** Exact canonical finite numeric literals can be emitted without retaining
 * parser comparison nodes. Other endpoint expressions use ordinary lowering.
 * This predicate is shared by the lowerer and writer, so their partition of
 * the declaration bounds cannot omit an endpoint. */
bool isPackedLinearBoundLiteral(const VarDecl& declaration, const ExprPtr& endpoint);

/** Emit numeric columns deliberately absent from the ordinary preamble.
 * The complete declaration-aligned name map includes reserved-name changes;
 * columns retained by the Parser are not declared again. All source columns,
 * including completely unused/free ones, remain observable. */
bool writePackedLinearDeclarationsSmt2(const ConstraintModel& model,
                                       const std::vector<std::string>& column_symbols,
                                       Lower::HirToParser& lowering,
                                       std::ostream& out, Diagnostics& diags);

/** Emit the literal bounds deferred by lowerPackedLinearPreamble's explicit
 * streaming mode. Symbols come from that lowerer's declaration-aligned map;
 * Int/Real comparison promotion retains fractional bounds without rounding. */
bool writePackedLinearBoundsSmt2(const ConstraintModel& model,
                                 const std::vector<std::string>& column_symbols,
                                 std::ostream& out, Diagnostics& diags);

/** Emit only the packed hard assertions. Ordinary declarations, nonliteral
 * bounds, constraints and objective commands use the existing lowering path;
 * deferred literal bounds use writePackedLinearBoundsSmt2. `column_symbols`
 * are declaration-aligned SMT symbols obtained from
 * that lowerer's emittedSymbolName map, including its quoting and reserved-name
 * conversion; they must not be reconstructed from source names. */
bool writePackedLinearRowsSmt2(const ConstraintModel& model,
                               const std::vector<std::string>& column_symbols,
                               std::ostream& out, Diagnostics& diags);

} // namespace SOMTParser::Uir::Hir

#endif
