#include "somtparser/lowering/hir_to_parser.h"
#include "somtparser/hir/typecheck.h"
#include "test_helpers.h"

#include <memory>
#include <string>
#include <vector>

namespace H = SOMTParser::Uir::Hir;
namespace U = SOMTParser::Uir;
namespace L = SOMTParser::Lower;

static void checkQuantifiers() {
    auto parser = SOMTParser::newParser();
    L::HirToParser lowerer(parser);
    H::ConstraintModel context;
    context.decls.push_back({"g", H::Sort::boolean()});
    U::TranslationReport report;
    U::Diagnostics declarations;
    VERIFY(lowerer.lower(context, report, declarations));

    constexpr int depth = 12000;
    auto expression = H::mkOp(H::Op::EQ, {
        H::mkBoundVar("q0", H::Sort::boolean()),
        H::mkBoundVar("q11999", H::Sort::boolean())});
    for (int i = depth - 1; i >= 0; --i) {
        const std::vector<H::Binder> binders{{"q" + std::to_string(i), H::Sort::boolean()}};
        expression = i % 2 ? H::mkExists(binders, expression) : H::mkForall(binders, expression);
    }
    U::Diagnostics validation;
    VERIFY(H::typeCheckTerms(context, {{expression, {}}}, validation));
    U::Diagnostics lowered;
    auto node = lowerer.lowerTerm(expression, lowered);
    VERIFY(node && !lowered.hasErrors());
    std::shared_ptr<SOMTParser::DAGNode> outer, inner;
    for (int i = 0; i < depth; ++i) {
        VERIFY(node->getKind() == (i % 2 ? SOMTParser::NODE_KIND::NT_EXISTS
                                         : SOMTParser::NODE_KIND::NT_FORALL));
        const auto variables = node->getQuantVars();
        VERIFY(variables.size() == 1);
        VERIFY(variables[0]->getName() == "q" + std::to_string(i));
        if (i == 0) { outer = variables[0]; }
        if (i + 1 == depth) { inner = variables[0]; }
        node = node->getQuantBody();
    }
    VERIFY(node->isEq());
    VERIFY(node->getChildrenSize() == 2);
    VERIFY((node->getChild(0) == outer && node->getChild(1) == inner)
           || (node->getChild(1) == outer && node->getChild(0) == inner));
    U::Diagnostics escaped;
    VERIFY(!lowerer.lowerTerm(H::mkBoundVar("q0", H::Sort::boolean()), escaped));

    // A shared nontrivial operand appears outside and inside another binder.
    // Finishing the inner scope must not erase the outer cache entry.
    auto shared = H::mkIdent("g", H::Sort::boolean());
    for (int i = 0; i < 12001; ++i) { shared = H::mkOp(H::Op::NOT, {shared}); }
    const auto inside = H::mkForall({{"unused", H::Sort::boolean()}}, shared);
    const auto combined = H::mkOp(H::Op::AND, {shared, inside, shared});
    U::Diagnostics shared_result;
    VERIFY(lowerer.lowerTerm(combined, shared_result));
    VERIFY(!shared_result.hasErrors());

    // Deep body failure must restore all binders before another lowerTerm.
    auto failure = H::mkIdent("missing", H::Sort::boolean());
    for (int i = 0; i < depth; ++i) {
        failure = H::mkForall({{"failed" + std::to_string(i), H::Sort::boolean()}}, failure);
    }
    U::Diagnostics failed;
    VERIFY(!lowerer.lowerTerm(failure, failed));
    VERIFY(failed.all().size() == 1);
    U::Diagnostics after_failure;
    VERIFY(!lowerer.lowerTerm(H::mkBoundVar("failed0", H::Sort::boolean()), after_failure));
    const auto recovered = H::mkForall({{"failed0", H::Sort::boolean()}},
                                      H::mkBoundVar("failed0", H::Sort::boolean()));
    U::Diagnostics recovery;
    auto recovered_node = lowerer.lowerTerm(recovered, recovery);
    VERIFY(recovered_node && !recovery.hasErrors());
    VERIFY(recovered_node->getQuantBody() == recovered_node->getQuantVars()[0]);

    // A failure while building binder sorts happens before scope entry has
    // finished. The already-created first binder must still be removed.
    const auto partial = H::mkForall({{"partial", H::Sort::boolean()},
                                     {"bad_width", H::Sort::bitvec(0)}}, H::mkBool(true));
    U::Diagnostics bad_sort;
    VERIFY(!lowerer.lowerTerm(partial, bad_sort));
    U::Diagnostics partial_escape;
    VERIFY(!lowerer.lowerTerm(H::mkBoundVar("partial", H::Sort::boolean()), partial_escape));

    // Normal HIR checking rejects shadowing. Exercise the lower-level scope
    // restore contract directly as well: an inner binding with another sort
    // must not replace the outer binding used by the following sibling.
    const auto shadowed = H::mkForall({{"shadow", H::Sort::boolean()}}, H::mkOp(H::Op::AND, {
        H::mkExists({{"shadow", H::Sort::integer()}}, H::mkOp(H::Op::GE, {
            H::mkBoundVar("shadow", H::Sort::integer()), H::mkInt(0)})),
        H::mkBoundVar("shadow", H::Sort::boolean())}));
    U::Diagnostics shadow_diagnostics;
    auto shadow_node = lowerer.lowerTerm(shadowed, shadow_diagnostics);
    VERIFY(shadow_node && !shadow_diagnostics.hasErrors());
    const auto outer_shadow = shadow_node->getQuantVars()[0];
    const auto conjunction = shadow_node->getQuantBody();
    bool outer_used = false, inner_used = false;
    for (const auto& child : conjunction->getChildren()) {
        outer_used |= child == outer_shadow;
        if (child->getKind() == SOMTParser::NODE_KIND::NT_EXISTS) {
            const auto inner_shadow = child->getQuantVars()[0];
            VERIFY(inner_shadow != outer_shadow && inner_shadow->getSort()->isInt());
            inner_used = true;
        }
    }
    VERIFY(outer_shadow->getSort()->isBool() && outer_used && inner_used);
}

static void checkDefinitionOrder() {
    constexpr int count = 12000;
    H::ConstraintModel model;
    model.funs.reserve(count);
    for (int i = 0; i < count; ++i) {
        H::FunDecl function;
        function.name = "f" + std::to_string(i);
        function.result = H::Sort::boolean();
        function.body = i + 1 == count ? H::mkBool(true)
            : H::mkApply("f" + std::to_string(i + 1), H::Sort::boolean(), {});
        model.funs.push_back(std::move(function));
    }
    U::Diagnostics checked;
    VERIFY(H::typeCheck(model, checked));
    auto parser = SOMTParser::newParser();
    L::HirToParser lowerer(parser);
    U::TranslationReport report;
    U::Diagnostics diagnostics;
    VERIFY(lowerer.lower(model, report, diagnostics));
    VERIFY(!diagnostics.hasErrors());
    // Dependencies precede callers in the emitted declaration order, and
    // every source definition is present with a body.
    const auto& order = parser->getSymbolManager()->getFunctionNames();
    VERIFY(order.size() == count);
    for (int i = 0; i < count; ++i) {
        VERIFY(order[i] == "f" + std::to_string(count - 1 - i));
        const auto function = parser->getSymbolManager()->getFun("f" + std::to_string(i));
        VERIFY(function && function->isFuncDef());
        VERIFY(function->getFuncBody());
    }

    // Two functions form an explicitly labelled SCC; a caller declared
    // before that SCC must be ordered after the whole definition unit.
    H::ConstraintModel recursive;
    for (const std::string name : {"caller", "a", "b"}) {
        H::FunDecl function;
        function.name = name;
        function.result = H::Sort::boolean();
        function.params = {H::Sort::boolean()};
        function.binders = {{"n", H::Sort::boolean()}};
        const auto n = H::mkBoundVar("n", H::Sort::boolean());
        function.body = H::mkApply(name == "a" ? "b" : "a", H::Sort::boolean(), {n});
        if (name != "caller") { function.recursive_group = "mutual"; }
        recursive.funs.push_back(std::move(function));
    }
    U::Diagnostics recursive_checked;
    VERIFY(H::typeCheck(recursive, recursive_checked));
    auto recursive_parser = SOMTParser::newParser();
    L::HirToParser recursive_lowerer(recursive_parser);
    U::Diagnostics recursive_diagnostics;
    VERIFY(recursive_lowerer.lower(recursive, report, recursive_diagnostics));
    const auto* group = recursive_parser->getSymbolManager()->getRecFunGroup("a");
    VERIFY(group && group->size() == 2);
    VERIFY(recursive_parser->isDeclaredFunction("caller"));
}

static void checkCompositeSorts() {
    // Cover all structural lowering child positions with a deep Array/Set/
    // Tuple chain. Inspect native sorts directly, without involving dumping.
    constexpr int depth = 6000;
    auto sort = H::Sort::bitvec(7);
    for (int i = 0; i < depth; ++i) {
        switch (i % 3) {
        case 0: sort = H::Sort::array(H::Sort::boolean(), sort); break;
        case 1: sort = H::Sort::set(sort); break;
        case 2: sort = H::Sort::tuple({H::Sort::integer(), sort}); break;
        }
    }
    H::ConstraintModel model;
    model.decls.push_back({"deep", sort});
    auto parser = SOMTParser::newParser();
    L::HirToParser lowerer(parser);
    U::TranslationReport report;
    U::Diagnostics diagnostics;
    VERIFY(lowerer.lower(model, report, diagnostics));
    auto native = lowerer.varMap().at("deep")->getSort();
    for (int i = depth - 1; i >= 0; --i) {
        switch (i % 3) {
        case 0:
            VERIFY(native->isArray());
            VERIFY(native->getChild(0)->isBool());
            native = native->getChild(1);
            break;
        case 1:
            VERIFY(native->isSet());
            native = native->getChild(0);
            break;
        case 2:
            VERIFY(native->isTuple());
            VERIFY(native->getChild(0)->isInt());
            native = native->getChild(1);
            break;
        }
    }
    VERIFY(native->isBv() && native->getBitWidth() == 7);

    // Sort caches must not reuse a previous root's type-parameter context.
    H::DatatypeDecl box;
    box.name = "Box";
    box.params = {"T"};
    box.constructors = {{"box", {{"field", H::Sort::sortApp("U", {
        H::Sort::array(H::Sort::uninterpreted("T"), H::Sort::uninterpreted("T"))})}}}};
    H::ConstraintModel polymorphic;
    polymorphic.uninterpreted_sorts.push_back({"U", 1});
    polymorphic.datatypes.push_back(box);
    polymorphic.decls.push_back({"global_t", H::Sort::uninterpreted("T")});
    polymorphic.decls.push_back({"box_bool", H::Sort::datatype("Box", {H::Sort::boolean()})});
    polymorphic.decls.push_back({"box_int", H::Sort::datatype("Box", {H::Sort::integer()})});
    auto parametric_parser = SOMTParser::newParser();
    L::HirToParser parametric_lowerer(parametric_parser);
    U::Diagnostics parametric_diagnostics;
    VERIFY(parametric_lowerer.lower(polymorphic, report, parametric_diagnostics));
    VERIFY(parametric_parser->getSymbolManager()->resolveSort("T"));
    VERIFY(parametric_lowerer.varMap().at("box_bool")->getSort()->getChild(0)->isBool());
    VERIFY(parametric_lowerer.varMap().at("box_int")->getSort()->getChild(0)->isInt());
}

int main() {
    checkQuantifiers();
    checkDefinitionOrder();
    checkCompositeSorts();
    return 0;
}
