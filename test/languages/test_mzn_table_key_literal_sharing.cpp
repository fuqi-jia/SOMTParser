// A finite key domain must not allocate another literal for each table row.
#include "somtparser/languages/minizinc.h"
#include "somtparser/hir/hir.h"
#include "test_helpers.h"

#include <map>
#include <set>
#include <sstream>
#include <unordered_set>
#include <vector>

int main() {
    using namespace SOMTParser;
    using namespace SOMTParser::Uir::Hir;
    std::ostringstream source;
    source << "array[1..256,1..3] of int: t=array2d(1..256,1..3,[";
    for (int x = 0; x < 16; ++x) {
        for (int y = 0; y < 16; ++y) {
            if (x != 0 || y != 0) { source << ','; }
            source << (x + 3 * y) % 16 << ',' << x << ',' << y;
        }
    }
    source << "]);\nvar int: cost; var int: x; var int: y;\n"
           << "constraint table([cost,x,y],t);\nsolve satisfy;\n";
    Lang::SourceUnit unit;
    unit.main_path = "table-literal-sharing.mzn";
    unit.inline_source = source.str();
    const auto parsed = Lang::mkMiniZincLanguage()->parse(unit, Lang::ParseOptions{});
    VERIFY(parsed.ok());
    std::vector<ExprPtr> pending;
    for (const auto& function : parsed.model->funs) {
        if (function.name.find("__mzn_table@") == 0) { pending.push_back(function.body); }
    }
    VERIFY(!pending.empty());
    std::unordered_set<const Expr*> visited;
    std::map<long long, std::set<const Expr*>> literals;
    std::size_t stores = 0;
    while (!pending.empty()) {
        auto expression = pending.back();
        pending.pop_back();
        if (!expression || !visited.insert(expression.get()).second) { continue; }
        if (expression->kind == ExprKind::LIT_INT) {
            literals[expression->int_value].insert(expression.get());
        }
        if (expression->kind == ExprKind::OP && expression->op == Op::STORE) { ++stores; }
        pending.insert(pending.end(), expression->args.begin(), expression->args.end());
    }
    // Distinct table rows and finite-domain guards remain represented. The
    // memory bound is the number of distinct integer values, not store count.
    VERIFY(stores >= 128);
    VERIFY(literals.size() == 16);
    for (const auto& entry : literals) { VERIFY(entry.second.size() == 1); }
}
