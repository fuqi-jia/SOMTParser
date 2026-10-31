// Repeated decision reads must share the fixed table's HIR storage.
#include "somtparser/languages/minizinc.h"
#include "somtparser/hir/hir.h"
#include "test_helpers.h"

#include <string>
#include <unordered_set>
#include <vector>

int main() {
    using namespace SOMTParser;
    using namespace SOMTParser::Uir::Hir;
    Lang::SourceUnit unit;
    unit.main_path = "shared-table.mzn";
    unit.inline_source =
        "array[1..64] of int: table = [3*i | i in 1..64];\n"
        "array[1..128] of var 1..64: index;\n"
        "constraint forall(i in 1..128)(table[index[i]] > i);\n"
        "solve satisfy;\n";
    auto result = Lang::mkMiniZincLanguage()->parse(unit, Lang::ParseOptions{});
    VERIFY(result.ok());
    std::vector<ExprPtr> pending;
    for (const auto& c : result.model->constraints) { pending.push_back(c.formula); }
    std::unordered_set<const Expr*> nodes;
    while (!pending.empty()) {
        auto expression = pending.back();
        pending.pop_back();
        if (!nodes.insert(expression.get()).second) { continue; }
        pending.insert(pending.end(), expression->args.begin(), expression->args.end());
    }
    // A fresh 64-cell mux for every read exceeds 32,000 nodes. Leave room
    // for domain/definedness bookkeeping while guarding linear table reuse.
    VERIFY(nodes.size() < 10000);

    unit.inline_source =
        "array[1..1024, 1..2] of int: table = array2d(1..1024, 1..2, [i | i in 1..2048]);\n"
        "var 1..2: index;\n"
        "constraint table[512, index] > 0;\n"
        "solve satisfy;\n";
    result = Lang::mkMiniZincLanguage()->parse(unit, Lang::ParseOptions{});
    VERIFY(result.ok());
    nodes.clear();
    for (const auto& c : result.model->constraints) { pending.push_back(c.formula); }
    while (!pending.empty()) {
        auto expression = pending.back();
        pending.pop_back();
        if (!nodes.insert(expression.get()).second) { continue; }
        pending.insert(pending.end(), expression->args.begin(), expression->args.end());
    }
    // Selecting a fixed two-cell row must not materialize the entire table.
    VERIFY(nodes.size() < 100);
}
