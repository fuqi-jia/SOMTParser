// Literal sharing must keep repeated weighted clauses and their locations.
#include "somtparser/languages/wcnf.h"
#include "somtparser/hir/hir.h"
#include "test_helpers.h"

#include <string>
#include <unordered_set>
#include <vector>

int main() {
    using namespace SOMTParser;
    using namespace SOMTParser::Uir;
    using namespace SOMTParser::Uir::Hir;
    auto language = Lang::mkWcnfLanguage();
    Lang::SourceUnit unit;
    unit.main_path = "repeated.wcnf";
    unit.inline_source = "p wcnf 4 5001 100\nh 1 -2 0\n";
    for (int i = 0; i < 5000; ++i) {
        unit.inline_source += "7 1 -2 0\n";
    }
    auto result = language->parse(unit, Lang::ParseOptions{});
    VERIFY(result.ok());
    VERIFY(result.model->decls.size() == 4);
    VERIFY(result.model->decls.back().name == "x4");
    VERIFY(result.model->constraints.size() == 5001);
    std::unordered_set<const Expr*> nodes;
    std::vector<ExprPtr> pending;
    for (std::size_t i = 0; i < result.model->constraints.size(); ++i) {
        const auto& constraint = result.model->constraints[i];
        VERIFY(constraint.loc.line == static_cast<int>(i + 2));
        VERIFY(constraint.formula->loc.line == static_cast<int>(i + 2));
        VERIFY(constraint.soft == (i != 0));
        if (i != 0) { VERIFY(constraint.weight_text == "7"); }
        pending.push_back(constraint.formula);
    }
    while (!pending.empty()) {
        auto expression = pending.back();
        pending.pop_back();
        if (!nodes.insert(expression.get()).second) { continue; }
        pending.insert(pending.end(), expression->args.begin(), expression->args.end());
    }
    // Each clause still exists, but x1, x2 and not(x2) are shared. This bounds
    // allocation independently of how often a literal occurs in the input.
    VERIFY(nodes.size() == 5001 + 3);

    Lang::SourceUnit invalid;
    invalid.main_path = "overflow.wcnf";
    invalid.inline_source = "h -9223372036854775808 0\n";
    auto rejected = language->parse(invalid, Lang::ParseOptions{});
    VERIFY(!rejected.ok());
    VERIFY(rejected.diagnostics.all().front().code == ErrorCode::E_PARSE);
    VERIFY(rejected.diagnostics.all().front().loc.line == 1);
}
