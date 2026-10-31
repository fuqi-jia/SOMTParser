#include "somtparser/hir/hir.h"
#include "test_helpers.h"

using namespace SOMTParser::Uir;
using namespace SOMTParser::Uir::Hir;

static ExprPtr diamond(ExprPtr value, unsigned depth) {
    for (unsigned i = 0; i < depth; ++i) {
        value = mkOp(Op::AND, {value, value});
    }
    return value;
}

int main() {
    ConstraintModel model;
    // Only 81 nodes, but a tree walk performs more than 2^80 visits.
    model.constraints.push_back({diamond(mkBool(true), 80)});
    VERIFY(model.features().empty());
    VERIFY(model.maxQuantifierAlternations() == 0);

    // Nonlinearity below a binder used to be missed entirely.
    const auto integer = Sort::integer();
    const auto square = mkOp(Op::MUL, {mkBoundVar("x", integer), mkBoundVar("x", integer)});
    const auto nonlinear = mkForall({{"x", integer}}, mkOp(Op::GE, {square, mkInt(0)}));
    model.constraints.push_back({diamond(nonlinear, 80)});
    VERIFY(model.features().count(feat::nonlinear()) == 1);
    VERIFY(model.features().count(feat::quantifier()) == 1);
    VERIFY(model.maxQuantifierAlternations() == 0);

    // The exact same node is seen first without an enclosing quantifier,
    // then below exists. Caching only one numeric result would return 1.
    const auto shared = mkForall({{"a", integer}},
        mkExists({{"b", integer}}, mkBool(true)));
    model.constraints.push_back({shared});
    model.constraints.push_back({mkExists({{"c", integer}}, diamond(shared, 80))});
    VERIFY(model.maxQuantifierAlternations() == 2);

    // Functions and objectives must participate even without constraints.
    ConstraintModel roots;
    FunDecl function;
    function.name = "p";
    function.result = Sort::boolean();
    function.body = diamond(mkForall({{"a", integer}}, shared), 80);
    roots.funs.push_back(function);
    VERIFY(roots.maxQuantifierAlternations() == 1);
    Objective objective;
    objective.term = mkOp(Op::ITE,
        {mkExists({{"c", integer}}, shared), mkInt(1), mkInt(0)});
    roots.objectives.push_back(objective);
    VERIFY(roots.maxQuantifierAlternations() == 2);
    VERIFY(roots.features().count(feat::quantifier()) == 1);

    // A null definition is an uninterpreted function, not a traversal error.
    roots.funs.push_back(FunDecl{});
    VERIFY(roots.maxQuantifierAlternations() == 2);
    return 0;
}
