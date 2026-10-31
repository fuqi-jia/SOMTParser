#ifndef SOMTPARSER_HIR_PACKED_SCALAR_IO_HEADER
#define SOMTPARSER_HIR_PACKED_SCALAR_IO_HEADER

#include "somtparser/hir/hir.h"
#include "somtparser/translation/diagnostic.h"

#include <iosfwd>
#include <string_view>
#include <unordered_map>

namespace SOMTParser::Lower { class HirToParser; }
namespace SOMTParser::Uir::Hir {

/** Borrowed range index; the model and its range vector outlive this view. */
class ScalarRangeIndex {
public:
    explicit ScalarRangeIndex(const ConstraintModel& model);
    const ScalarVarRange* find(const std::string& name,
                               std::uint64_t* range = nullptr,
                               std::uint64_t* offset = nullptr) const;
private:
    const ConstraintModel& model_;
    std::unordered_map<std::string_view, std::vector<std::size_t>> prefixes_;
};

/** Validates storage and typed call arguments without expanding any range. */
bool validatePackedScalarModel(const ConstraintModel& model, Diagnostics& diagnostics);

/** Ordinary HIR plus just the compact scalars mentioned by ordinary formulas
 * or function definitions. Bounds on those scalars remain in the compact
 * writer, so they are emitted exactly once alongside all unused coordinates. */
ConstraintModelPtr packedScalarPreamble(const ConstraintModel& model, Diagnostics& diagnostics);

/** Emit coordinates absent from the ordinary preamble before the packed
 * suffix references them. The ordinary module supplies the initial set-logic. */
bool writePackedScalarDeclarationsSmt2(const ConstraintModel& model,
                                      Lower::HirToParser& lowering,
                                      std::ostream& out, Diagnostics& diagnostics);

/** Emit every range bound and every packed asserted application. Ordinary names and function names come from the same
 * lowerer used for the preamble, including its reserved-symbol renaming. */
bool writePackedScalarsSmt2(const ConstraintModel& model,
                            Lower::HirToParser& lowering,
                            std::ostream& out, Diagnostics& diagnostics);

} // namespace SOMTParser::Uir::Hir
#endif
