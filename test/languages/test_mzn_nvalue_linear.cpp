// Structural regression for parseNvalue: unique HIR nodes should grow linearly.
#include "somtparser/languages/register_all.h"
#include "somtparser/hir/hir.h"
#include "somtparser/translation/language.h"
#include "test_helpers.h"

#include <iostream>
#include <string>
#include <unordered_set>

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

Lang::ParseOutcome parseNvalueSize(std::size_t n) {
    std::string source = "array[1.." + std::to_string(n)
        + "] of var int: x;\nconstraint nvalue(x) >= 0;\nsolve satisfy;\n";
    Lang::SourceUnit unit;
    unit.display_name = "<nvalue-size>";
    unit.inline_source = std::move(source);
    return Lang::LanguageRegistry::instance().byId("minizinc")->parse(unit, {});
}

void visit(const Hir::ExprPtr& expr, std::unordered_set<const Hir::Expr*>& seen) {
    if (!expr || !seen.insert(expr.get()).second) { return; }
    for (const auto& arg : expr->args) { visit(arg, seen); }
}

std::size_t uniqueConstraintNodes(const Hir::ConstraintModel& model) {
    std::unordered_set<const Hir::Expr*> seen;
    for (const auto& constraint : model.constraints) { visit(constraint.formula, seen); }
    for (const auto& decl : model.decls) {
        visit(decl.lower_bound, seen);
        visit(decl.upper_bound, seen);
    }
    return seen.size();
}

} // namespace

int main() {
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());
    const auto small = parseNvalueSize(32);
    const auto large = parseNvalueSize(64);
    VERIFY(small.ok() && large.ok());
    const auto small_nodes = uniqueConstraintNodes(*small.model);
    const auto large_nodes = uniqueConstraintNodes(*large.model);
    // A quadratic prior-pair expansion grows close to 4x here; the expected
    // shared SELECT/STORE chain, value cells, and sum grow near 2x.
    VERIFY(large_nodes <= 2 * small_nodes + 32);
    VERIFY(large_nodes > small_nodes);
    std::cout << "nvalue unique HIR nodes: " << small_nodes << " -> " << large_nodes << "\n";
}
