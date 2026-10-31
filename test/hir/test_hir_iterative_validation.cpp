#include "somtparser/hir/typecheck.h"
#include "test_helpers.h"

#include <memory>
#include <string>
#include <vector>

namespace H = SOMTParser::Uir::Hir;
namespace U = SOMTParser::Uir;

static H::Sort composite(H::Sort leaf, int depth) {
    for (int i = 0; i < depth; ++i) {
        switch (i % 3) {
        case 0: leaf = H::Sort::array(H::Sort::boolean(), leaf); break;
        case 1: leaf = H::Sort::tuple({leaf}); break;
        case 2: leaf = H::Sort::set(leaf); break;
        }
    }
    return leaf;
}

static H::FunDecl definition(const std::string& name, H::ExprPtr body,
                             const std::string& group = {}) {
    H::FunDecl function;
    function.name = name;
    function.result = H::Sort::boolean();
    function.body = std::move(body);
    function.recursive_group = group;
    return function;
}

static void checkDeepScopes() {
    constexpr int depth = 12000;
    const auto boolean = H::Sort::boolean();
    const auto outer = H::mkBoundVar("q0", boolean);
    const auto inner = H::mkBoundVar("q11999", boolean);
    auto root = H::mkOp(H::Op::EQ, {outer, inner});
    for (int i = depth - 1; i >= 0; --i) {
        const std::vector<H::Binder> binders{{"q" + std::to_string(i), boolean}};
        root = i % 2 ? H::mkExists(binders, root) : H::mkForall(binders, root);
    }
    H::ConstraintModel model;
    model.constraints.push_back({root});
    U::Diagnostics accepted;
    VERIFY(H::typeCheck(model, accepted));
    VERIFY(!accepted.hasErrors());

    // Successful nested checking must not bind either shared leaf globally.
    U::Diagnostics escaped;
    VERIFY(!H::typeCheckTerms(model, {{outer, {"scope.hir", 9, 2}}}, escaped));
    VERIFY(escaped.all().size() == 1);
    VERIFY(escaped.all()[0].loc.line == 9);

    // The same DAG node is needed by a parent before and after a child
    // quantifier visits it. A cache indexed by address alone evicts the
    // parent's completed operand and can restart recursive checking.
    H::ConstraintModel shared_context;
    shared_context.decls.push_back({"g", boolean});
    auto shared = H::mkIdent("g", boolean);
    for (int i = 0; i < 12000; ++i) { shared = H::mkOp(H::Op::NOT, {shared}); }
    const auto quantified = H::mkForall({{"unused", boolean}}, shared);
    shared_context.constraints.push_back({H::mkOp(H::Op::AND, {shared, quantified, shared})});
    U::Diagnostics shared_result;
    VERIFY(H::typeCheck(shared_context, shared_result));
    VERIFY(!shared_result.hasErrors());
}

static void checkScopeFailureRecovery() {
    const auto boolean = H::Sort::boolean();
    const auto q = H::mkBoundVar("q", boolean);
    const auto r = H::mkBoundVar("r", boolean);
    // Entering the inner frame adds r, then rejects shadowing q. Both that
    // partial frame and the outer frame must unwind before the next root.
    const auto bad = H::mkForall({{"q", boolean}},
        H::mkExists({{"r", boolean}, {"q", boolean}}, q));
    const auto good = H::mkForall({{"q", boolean}, {"r", boolean}},
        H::mkOp(H::Op::AND, {q, r}));
    U::Diagnostics shadowed;
    VERIFY(!H::typeCheckTerms({}, {
        {bad, {"scope.hir", 11, 1}}, {good, {"scope.hir", 22, 1}},
        {q, {"scope.hir", 33, 1}}}, shadowed));
    VERIFY(shadowed.all().size() == 2);
    VERIFY(shadowed.all()[0].loc.line == 11);
    VERIFY(shadowed.all()[0].message.find("already in scope") != std::string::npos);
    VERIFY(shadowed.all()[1].loc.line == 33);

    // Failure after entering all nested frames must restore them as well.
    auto failed_body = H::mkIdent("undeclared", boolean);
    for (int i = 0; i < 12000; ++i) {
        failed_body = H::mkForall({{"failure" + std::to_string(i), boolean}}, failed_body);
    }
    const auto recovered = H::mkForall({{"failure0", boolean}},
        H::mkBoundVar("failure0", boolean));
    U::Diagnostics body_error;
    VERIFY(!H::typeCheckTerms({}, {{failed_body, {"scope.hir", 44, 1}},
                                  {recovered, {"scope.hir", 55, 1}}}, body_error));
    VERIFY(body_error.all().size() == 1);
    VERIFY(body_error.all()[0].loc.line == 44);

    // The same bound leaf under a different sort is rechecked, and failure
    // does not prevent a later valid binder of the same spelling.
    const auto wrong_sort = H::mkForall({{"q", H::Sort::integer()}}, q);
    U::Diagnostics mismatch;
    VERIFY(!H::typeCheckTerms({}, {{good, {}}, {wrong_sort, {"scope.hir", 66, 1}},
                                  {good, {}}}, mismatch));
    VERIFY(mismatch.all().size() == 1);
    VERIFY(mismatch.all()[0].loc.line == 66);

    H::ConstraintModel global;
    global.decls.push_back({"q", boolean});
    U::Diagnostics global_shadow;
    VERIFY(!H::typeCheckTerms(global, {{good, {}}}, global_shadow));
    VERIFY(global_shadow.all()[0].message.find("already in scope") != std::string::npos);
}

static void checkFunctionComponents() {
    constexpr int count = 12000;
    H::ConstraintModel chain;
    chain.funs.reserve(count);
    for (int i = 0; i < count; ++i) {
        chain.funs.push_back(definition("f" + std::to_string(i),
            i + 1 == count ? H::mkBool(true)
                           : H::mkApply("f" + std::to_string(i + 1), H::Sort::boolean(), {})));
    }
    U::Diagnostics acyclic;
    VERIFY(H::typeCheck(chain, acyclic));
    VERIFY(!acyclic.hasErrors());
    // One long back edge turns the same graph into one SCC. It is accepted
    // only when every member opts into that same recursive equation group.
    chain.funs.back().body = H::mkApply("f0", H::Sort::boolean(), {});
    U::Diagnostics unlabelled;
    VERIFY(!H::typeCheck(chain, unlabelled));
    VERIFY(unlabelled.all().size() == 1);
    for (auto& function : chain.funs) { function.recursive_group = "one-component"; }
    U::Diagnostics labelled;
    VERIFY(H::typeCheck(chain, labelled));
    chain.funs[count / 2].recursive_group = "different-component";
    U::Diagnostics mixed;
    VERIFY(!H::typeCheck(chain, mixed));
    VERIFY(mixed.all().size() == 1);

    H::ConstraintModel disconnected;
    disconnected.funs = {
        definition("a", H::mkApply("a", H::Sort::boolean(), {}), "same-label"),
        definition("b", H::mkApply("b", H::Sort::boolean(), {}), "same-label")};
    U::Diagnostics reused_label;
    VERIFY(!H::typeCheck(disconnected, reused_label));
    VERIFY(reused_label.all().size() == 1);
    VERIFY(reused_label.all()[0].message.find("multiple call components") != std::string::npos);
}

static void checkCompositeSorts() {
    constexpr int depth = 12000;
    const auto formal = composite(H::Sort::uninterpreted("T"), depth);
    const auto actual = composite(H::Sort::integer(), depth);
    H::DatatypeDecl box;
    box.name = "Box";
    box.params = {"T"};
    box.constructors = {{"box", {{"field", formal}}}};
    H::ConstraintModel model;
    model.datatypes = {box};
    model.decls.push_back({"value", actual});
    const auto instance = H::Sort::datatype("Box", {H::Sort::integer()});
    const auto value = H::mkIdent("value", actual);
    const auto constructed = H::mkDtConstructor("box", instance, {value});
    const auto selected = H::mkDtSelector("field", actual, constructed);
    U::Diagnostics accepted;
    VERIFY(H::typeCheckTerms(model, {{constructed, {}}, {selected, {}}}, accepted));
    VERIFY(!accepted.hasErrors());

    const auto wrong = H::mkDtSelector("field", composite(H::Sort::real(), depth), constructed);
    U::Diagnostics mismatched_leaf;
    VERIFY(!H::typeCheckTerms(model, {{wrong, {"sort.hir", 7, 2}}}, mismatched_leaf));
    VERIFY(mismatched_leaf.all().size() == 1);
    VERIFY(mismatched_leaf.all()[0].loc.line == 7);

    // Nominal references nested through structural containers are checked,
    // including arity and null arguments; a cyclic sort is rejected finitely.
    H::ConstraintModel invalid;
    invalid.uninterpreted_sorts.push_back({"U", 1});
    invalid.decls.push_back({"bad_arity", composite(H::Sort::sortApp("U", {
        H::Sort::integer(), H::Sort::boolean()}), 3000)});
    U::Diagnostics arity;
    VERIFY(!H::typeCheck(invalid, arity));
    VERIFY(arity.all().size() == 1);
    VERIFY(arity.all()[0].message.find("arity is 1") != std::string::npos);

    auto null_argument = H::Sort::tuple({H::Sort::integer()});
    null_argument.args[0].reset();
    invalid.decls = {{"null_argument", null_argument}};
    U::Diagnostics null_sort;
    VERIFY(!H::typeCheck(invalid, null_sort));
    VERIFY(null_sort.all().size() == 1);
    VERIFY(null_sort.firstErrorCode() == U::ErrorCode::E_INTERNAL);

    auto cyclic = std::make_shared<H::Sort>();
    cyclic->kind = H::SortKind::SET;
    cyclic->elem = cyclic;
    invalid.decls = {{"cycle", *cyclic}};
    U::Diagnostics cycle;
    const bool cycle_accepted = H::typeCheck(invalid, cycle);
    cyclic->elem.reset();
    VERIFY(!cycle_accepted);
    VERIFY(cycle.firstErrorCode() == U::ErrorCode::E_INTERNAL);
}

int main() {
    checkDeepScopes();
    checkScopeFailureRecovery();
    checkFunctionComponents();
    checkCompositeSorts();
    return 0;
}
