#include "somtparser/languages/mps.h"
#include "somtparser/hir/hir.h"
#include "test_helpers.h"

#include <string>
#include <unordered_set>
#include <vector>

int main() {
    using namespace SOMTParser;
    using namespace SOMTParser::Uir::Hir;
    Lang::SourceUnit unit;
    unit.main_path = "repeated.mps";
    unit.inline_source = "NAME repeated\nROWS\n N obj\n";
    constexpr int rows = 5000;
    for (int i = 0; i < rows; ++i) {
        unit.inline_source += " L r" + std::to_string(i) + "\n";
    }
    unit.inline_source += "COLUMNS\n x obj 2\n y obj -3\n";
    for (int i = 0; i < rows; ++i) {
        unit.inline_source += " x r" + std::to_string(i) + " 1.0\n";
        unit.inline_source += " y r" + std::to_string(i) + " -1e0\n";
    }
    unit.inline_source += "RHS\n";
    for (int i = 0; i < rows; ++i) {
        unit.inline_source += " rhs r" + std::to_string(i) + " 7\n";
    }
    unit.inline_source += "ENDATA\n";
    auto language = Lang::mkMpsLanguage();
    auto parsed = language->parse(unit, Lang::ParseOptions{});
    VERIFY(parsed.ok());
    VERIFY(parsed.model->constraints.size() == rows);
    VERIFY(parsed.model->objectives.size() == 1);
    std::unordered_set<const Expr*> nodes;
    std::vector<ExprPtr> pending;
    for (int i = 0; i < rows; ++i) {
        const auto& c = parsed.model->constraints[i];
        VERIFY(c.loc.line == i + 4);
        VERIFY(c.formula->loc.line == i + 4);
        pending.push_back(c.formula);
    }
    while (!pending.empty()) {
        auto expr = pending.back();
        pending.pop_back();
        if (!nodes.insert(expr.get()).second) { continue; }
        pending.insert(pending.end(), expr->args.begin(), expr->args.end());
    }
    // Every row retains its sum and relation; x, y, -y, -1 and RHS 7 are
    // shared, independent of the number of nonzero matrix entries.
    VERIFY(nodes.size() == 2 * rows + 5);
    auto again = language->parse(unit, Lang::ParseOptions{});
    VERIFY(again.ok());
    VERIFY(again.model->constraints.front().formula->args.front()->args.front()
           != parsed.model->constraints.front().formula->args.front()->args.front());
}
