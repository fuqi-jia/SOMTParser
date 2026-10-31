#include "somtparser/languages/opb.h"
#include "somtparser/hir/hir.h"
#include "test_helpers.h"

#include <string>
#include <unordered_set>
#include <vector>

int main() {
    using namespace SOMTParser;
    using namespace SOMTParser::Uir::Hir;
    Lang::SourceUnit unit;
    unit.main_path = "repeated.opb";
    constexpr int rows = 5000;
    for (int i = 0; i < rows; ++i) {
        unit.inline_source += "+1 x1 +1 ~x2 >= 1 ;\n";
    }
    auto language = Lang::mkOpbLanguage();
    auto parsed = language->parse(unit, Lang::ParseOptions{});
    VERIFY(parsed.ok());
    VERIFY(parsed.model->decls.size() == 2);
    VERIFY(parsed.model->constraints.size() == rows);
    std::unordered_set<const Expr*> nodes;
    std::vector<ExprPtr> pending;
    for (int i = 0; i < rows; ++i) {
        const auto& constraint = parsed.model->constraints[i];
        VERIFY(constraint.loc.line == i + 1);
        VERIFY(constraint.formula->loc.line == i + 1);
        pending.push_back(constraint.formula);
    }
    while (!pending.empty()) {
        auto expr = pending.back();
        pending.pop_back();
        if (!nodes.insert(expr.get()).second) { continue; }
        pending.insert(pending.end(), expr->args.begin(), expr->args.end());
    }
    // x1, x2, 1-x2, and the exact integer 1; sums and relations remain per row.
    VERIFY(nodes.size() == 2 * rows + 4);
    // OPB terms require a nonempty literal product. Removing a unit
    // coefficient therefore cannot turn a valid product into an empty one.
    unit.inline_source = "min: +1 ;\n";
    VERIFY(!language->parse(unit, Lang::ParseOptions{}).ok());
    unit.inline_source = "+1 >= 1 ;\n";
    VERIFY(!language->parse(unit, Lang::ParseOptions{}).ok());
}
