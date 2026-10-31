// Parser-internal HIR structural regression for dynamic finite record-array
// reads. This intentionally calls the MiniZinc frontend directly, before any
// HIR passes can rebuild or duplicate expressions.
#include "somtparser/languages/minizinc.h"

#include <iostream>
#include <memory>
#include <set>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "test_helpers.h"

using namespace SOMTParser;
using namespace SOMTParser::Uir;
using namespace SOMTParser::Uir::Hir;

namespace {

struct SharingStats {
    std::unordered_map<const Expr*, std::size_t> selects_by_store_root;
    std::unordered_set<const Expr*> store_nodes;
};

void visit(const ExprPtr& expression, SharingStats& stats,
           std::unordered_set<const Expr*>& visited) {
    if (!expression || !visited.insert(expression.get()).second) { return; }
    if (expression->kind == ExprKind::OP && expression->op == Op::STORE) {
        stats.store_nodes.insert(expression.get());
    }
    if (expression->kind == ExprKind::OP && expression->op == Op::SELECT
        && expression->args.size() == 2 && expression->args[0]
        && expression->args[0]->kind == ExprKind::OP
        && expression->args[0]->op == Op::STORE
        && expression->args[0]->sort.elem
        && expression->args[0]->sort.elem->kind == SortKind::INT) {
        ++stats.selects_by_store_root[expression->args[0].get()];
    }
    for (const auto& argument : expression->args) { visit(argument, stats, visited); }
}

SharingStats statsFor(const ConstraintModel& model) {
    SharingStats stats;
    std::unordered_set<const Expr*> visited;
    for (const auto& constraint : model.constraints) {
        visit(constraint.formula, stats, visited);
    }
    for (const auto& objective : model.objectives) {
        visit(objective.term, stats, visited);
    }
    return stats;
}

} // namespace

int main() {
    Lang::SourceUnit unit;
    unit.display_name = "<dynamic-record-array-sharing>";
    unit.inline_source =
        "var 1..2:i;\n"
        "type Inner=record(int:x);type Outer=record(Inner:inner);\n"
        "array[3..4]of Outer:records=array1d(3..4,[(inner:(x:10)),(inner:(x:20))]);\n"
        "var 3..4:j;var bool:choose;var 0..0:d;\n"
        "constraint (let{any:a=array1d(3..4,[(x:10),(x:20)])}in "
        "(a[i+2].x=10*i) /\\ (a[i+2].x=10*i)) /\\ "
        "(let{any:b=array1d(3..4,[(x:30),(x:40)])}in "
        "(b[i+2].x=10*i+20) /\\ (b[i+2].x=10*i+20));\n"
        "constraint records[j].inner.x=10 /\\ records[j].inner.x=10;\n"
        "constraint let{any:conditional=if choose then (x:4) else (x:5) endif;}"
        "in conditional.x=4;\n"
        "constraint let{any:partial=if (1 div d=0) then (x:4) else (x:5) endif;}"
        "in partial.x=4;\n"
        "solve satisfy;\n";

    const auto parsed = Lang::mkMiniZincLanguage()->parse(unit, Lang::ParseOptions{});
    if (!parsed.ok()) {
        std::cerr << "MiniZinc parse failed in sharing regression\n";
        for (const auto& diagnostic : parsed.diagnostics.all()) {
            std::cerr << diagnostic.message << '\n';
        }
        VERIFY(false);
        return 1;
    }

    const SharingStats stats = statsFor(*parsed.model);
    std::size_t reused_roots = 0;
    for (const auto& entry : stats.selects_by_store_root) {
        if (entry.second >= 2) { ++reused_roots; }
    }
    // Two distinct let-local arrays must have distinct STORE roots; each
    // source array must nevertheless share its root across repeated reads.
    VERIFY(stats.selects_by_store_root.size() >= 2);
    VERIFY(reused_roots >= 2);
    VERIFY(stats.store_nodes.size() >= 4);
    return 0;
}
