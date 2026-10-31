#include "somtparser/lowering/hir_to_parser.h"
#include "somtparser/frontend/parser.h"
#include "test_helpers.h"

#include <memory>
#include <vector>

namespace H = SOMTParser::Uir::Hir;
namespace U = SOMTParser::Uir;

static void releaseChain(H::ExprPtr& root) {
    std::vector<H::ExprPtr> parents_first;
    for (auto node = root; node; node = node->args.empty() ? nullptr : node->args[0]) {
        parents_first.push_back(node);
    }
    root.reset();
    for (auto& node : parents_first) { node.reset(); }
}

int main() {
    auto parser = SOMTParser::newParser();
    SOMTParser::Lower::HirToParser lowerer(parser);
    H::ConstraintModel model;
    model.decls.push_back({"b", H::Sort::boolean(), {}, {}, {}});
    U::TranslationReport report;
    U::Diagnostics diagnostics;
    VERIFY(lowerer.lower(model, report, diagnostics));
    auto expression = H::mkIdent("b", H::Sort::boolean());
    for (int i = 0; i < 20000; ++i) { expression = H::mkOp(H::Op::NOT, {expression}); }
    auto result = lowerer.lowerTerm(expression, diagnostics);
    VERIFY(result);
    VERIFY(!diagnostics.hasErrors());
    // Parser builders simplify pairs of negations, preserving the source leaf.
    VERIFY(result == lowerer.varMap().at("b"));
    releaseChain(expression);

    auto body = H::mkBoundVar("q", H::Sort::boolean());
    for (int i = 0; i < 3000; ++i) { body = H::mkOp(H::Op::NOT, {body}); }
    auto quantified = H::mkForall({H::Binder{"q", H::Sort::boolean()}}, body);
    VERIFY(lowerer.lowerTerm(quantified, diagnostics));
    U::Diagnostics unbound;
    VERIFY(!lowerer.lowerTerm(body, unbound));
    VERIFY(unbound.firstErrorCode() == U::ErrorCode::E_INTERNAL);
    quantified.reset();
    releaseChain(body);

    auto cyclic = std::make_shared<H::Expr>();
    cyclic->kind = H::ExprKind::OP;
    cyclic->op = H::Op::NOT;
    cyclic->sort = H::Sort::boolean();
    cyclic->args.push_back(cyclic);
    U::Diagnostics cycle_diagnostics;
    const auto cycle_result = lowerer.lowerTerm(cyclic, cycle_diagnostics);
    cyclic->args.clear();
    VERIFY(!cycle_result);
    VERIFY(cycle_diagnostics.firstErrorCode() == U::ErrorCode::E_INTERNAL);
    return 0;
}
