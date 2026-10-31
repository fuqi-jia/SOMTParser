#include "somtparser/lowering/decompose_globals_pass.h"
#include "somtparser/hir/typecheck.h"
#include "test_helpers.h"

#include <vector>

namespace H = SOMTParser::Uir::Hir;
namespace U = SOMTParser::Uir;

int main() {
    constexpr std::size_t depth = 40000;
    H::ConstraintModel model;
    auto variable = H::mkBoundVar("q", H::Sort::integer());
    auto leaf = H::mkGlobal("alldifferent", {variable, H::mkInt(0)});
    std::vector<H::ExprPtr> source_nodes{leaf};
    auto chain = leaf;
    for (std::size_t i = 0; i < depth; ++i) {
        chain = H::mkOp(H::Op::NOT, {chain});
        source_nodes.push_back(chain);
    }
    auto quantified = H::mkForall({H::Binder{"q", H::Sort::integer()}}, chain);
    model.constraints.push_back({quantified});
    model.constraints.push_back({quantified});

    // Defined bodies are inspected for unsupported globals, not rewritten.
    // Their deep ordinary traversal must not consume native call-stack space.
    H::FunDecl function;
    function.name = "plain";
    function.result = H::Sort::boolean();
    std::vector<H::ExprPtr> function_nodes{H::mkBool(true)};
    for (std::size_t i = 0; i < depth; ++i) {
        function_nodes.push_back(H::mkOp(H::Op::NOT, {function_nodes.back()}));
    }
    function.body = function_nodes.back();
    model.funs.push_back(function);

    U::TranslationReport report;
    U::Diagnostics diagnostics;
    U::LowerContext context{&report, &diagnostics};
    SOMTParser::Lower::DecomposeGlobalsPass pass;
    VERIFY(pass.run(model, context));
    VERIFY(!diagnostics.hasErrors());
    VERIFY(model.constraints[0].formula == model.constraints[1].formula);
    VERIFY(model.constraints[0].formula != quantified);
    VERIFY(model.funs[0].body == function.body);
    VERIFY(H::typeCheck(model, diagnostics));
    auto rewritten = model.constraints[0].formula;
    VERIFY(rewritten->binders.size() == 1);
    VERIFY(rewritten->binders[0].name == "q");
    std::vector<H::ExprPtr> output_nodes{rewritten};
    auto current = rewritten->args[0];
    std::size_t observed = 0;
    while (current->kind == H::ExprKind::OP && current->op == H::Op::NOT) {
        output_nodes.push_back(current);
        current = current->args[0];
        ++observed;
    }
    VERIFY(observed == depth);
    VERIFY(current->kind == H::ExprKind::OP && current->op == H::Op::DISTINCT);
    VERIFY(current->args[0] == variable);
    VERIFY(leaf->kind == H::ExprKind::GLOBAL); // Other holders retain the source.

    // Release both deep chains parent-first so the test isolates traversal.
    model.constraints.clear();
    model.funs.clear();
    rewritten.reset();
    quantified.reset();
    chain.reset();
    function.body.reset();
    for (auto& node : output_nodes) { node.reset(); }
    for (auto it = source_nodes.rbegin(); it != source_nodes.rend(); ++it) { it->reset(); }
    for (auto it = function_nodes.rbegin(); it != function_nodes.rend(); ++it) { it->reset(); }
    return 0;
}
