#include "somtparser/translation/semantics.h"
#include "test_helpers.h"

#include <functional>

namespace H = SOMTParser::Uir::Hir;
namespace U = SOMTParser::Uir;
namespace S = SOMTParser::Uir::Sem;

static H::ConstraintModel sourceModel() {
    H::ConstraintModel model;
    model.decls.push_back({"x", H::Sort::integer(), H::mkInt(0), H::mkInt(3), {}});
    model.constraints.push_back({H::mkOp(H::Op::GE,
        {H::mkIdent("x", H::Sort::integer()), H::mkInt(0)})});
    model.objectives.push_back({H::ObjKind::MINIMIZE,
        H::mkIdent("x", H::Sort::integer()), {}, {}});
    return model;
}

static H::FunDecl helper(const std::string& name = "helper") {
    H::FunDecl result;
    result.name = name;
    result.params = {H::Sort::integer()};
    result.result = H::Sort::integer();
    result.binders = {{"t", H::Sort::integer()}};
    result.body = H::mkOp(H::Op::ADD,
        {H::mkBoundVar("t", H::Sort::integer()), H::mkIdent("x", H::Sort::integer())});
    result.auxiliary = true;
    return result;
}

static S::TranslationPipeline sourcePipeline(const H::ConstraintModel& model) {
    S::TranslationPipeline pipeline;
    pipeline.add(S::miniZincToRelationalContract(model));
    return pipeline;
}

int main() {
    const auto original = sourceModel();
    auto model = original;
    auto pipeline = sourcePipeline(original);
    U::Diagnostics diagnostics;
    const auto signature = pipeline.stages().back().target_signature;
    VERIFY(S::extendRelationalWithDefinedHelpers(model, "decompose-globals", pipeline, diagnostics));
    VERIFY(pipeline.stages().size() == 1);
    VERIFY(pipeline.stages().back().target_signature.sharesStorageWith(signature));
    model.funs.push_back(helper());
    VERIFY(S::extendRelationalWithDefinedHelpers(model, "decompose-globals", pipeline, diagnostics));
    VERIFY(pipeline.stages().size() == 2);
    const auto& extension = pipeline.stages().back();
    VERIFY(extension.source_signature.sharesStorageWith(signature));
    VERIFY(extension.source_signature.symbols.size() == 1);
    VERIFY(extension.target_signature.symbols.size() == 2);
    VERIFY(extension.target_axioms.size() == pipeline.stages().front().target_axioms.size() + 1);
    VERIFY(extension.target_axioms.back()->kind == H::ExprKind::FORALL);
    VERIFY(extension.projection.observables.size() == 1);
    VERIFY(extension.projection.observables.front().source_name == "x");
    pipeline.add(S::relationalToSmtContract(model, true, extension.projection,
        extension.target_axioms, &extension.target_signature));
    VERIFY(pipeline.validate(diagnostics));
    S::Assignment projected;
    VERIFY(pipeline.project({{"x", "2"}, {"helper", "unused helper interpretation"}}, projected, diagnostics));
    VERIFY(projected.size() == 1 && projected.at("x") == "2");
    VERIFY(!diagnostics.hasErrors());

    // A forward reference between fresh definitions is still an acyclic
    // conservative extension. Explicit SCC/type checking rejects cycles.
    model = original;
    model.funs = {helper("first"), helper("second")};
    model.funs[0].body = H::mkApply("second", H::Sort::integer(),
        {H::mkBoundVar("t", H::Sort::integer())});
    pipeline = sourcePipeline(original);
    VERIFY(S::extendRelationalWithDefinedHelpers(model, "decompose-globals", pipeline, diagnostics));
    VERIFY(pipeline.validate(diagnostics));

    // Legal parameter/global shadowing must not capture the free occurrence
    // when the function definition is expressed as a universal axiom.
    model = original;
    model.funs = {helper()};
    model.funs[0].binders[0].name = "x";
    model.funs[0].body = H::mkOp(H::Op::ADD,
        {H::mkBoundVar("x", H::Sort::integer()), H::mkIdent("x", H::Sort::integer())});
    pipeline = sourcePipeline(original);
    VERIFY(S::extendRelationalWithDefinedHelpers(model, "decompose-globals", pipeline, diagnostics));
    const auto equation = pipeline.stages().back().target_axioms.back();
    VERIFY(equation->binders[0].name != "x");
    const auto body = equation->args[0]->args[1];
    VERIFY(body->args[0]->kind == H::ExprKind::BOUND_VAR);
    VERIFY(body->args[0]->name == equation->binders[0].name);
    VERIFY(body->args[1]->kind == H::ExprKind::IDENT && body->args[1]->name == "x");
    VERIFY(pipeline.validate(diagnostics));

    const auto reject = [&](const std::function<void(H::ConstraintModel&)>& mutate) {
        auto invalid = original;
        invalid.funs.push_back(helper());
        mutate(invalid);
        auto rejected = sourcePipeline(original);
        U::Diagnostics errors;
        VERIFY(!S::extendRelationalWithDefinedHelpers(invalid, "decompose-globals", rejected, errors));
        VERIFY(errors.hasErrors());
        VERIFY(rejected.stages().size() == 1);
    };
    reject([](auto& m) { m.funs[0].body.reset(); });
    reject([](auto& m) { m.funs[0].auxiliary = false; });
    reject([](auto& m) { m.funs[0].recursive_group = "cycle"; });
    reject([](auto& m) { m.funs[0].body = H::mkApply("helper", H::Sort::integer(),
        {H::mkBoundVar("t", H::Sort::integer())}); });
    reject([](auto& m) {
        m.funs.push_back(helper("second"));
        m.funs[0].body = H::mkApply("second", H::Sort::integer(), {H::mkInt(0)});
        m.funs[1].body = H::mkApply("helper", H::Sort::integer(), {H::mkInt(0)});
    });
    reject([](auto& m) { m.funs[0].body = H::mkBool(true); });
    reject([](auto& m) { m.funs[0].body = H::mkBoundVar("missing", H::Sort::integer()); });
    reject([](auto& m) { m.funs[0].body = H::mkApply("missing", H::Sort::integer(), {H::mkInt(0)}); });
    reject([](auto& m) { m.funs.push_back(helper()); });
    reject([](auto& m) { m.funs[0].name = "|x|"; });
    reject([](auto& m) { m.decls[0].sort = H::Sort::boolean(); });
    reject([](auto& m) { m.decls.clear(); });
    reject([](auto& m) { m.decls.push_back({"extra", H::Sort::integer(), {}, {}, {}}); });
    reject([](auto& m) { m.uninterpreted_sorts.push_back({"Extra", 0, {}}); });
    reject([](auto& m) { m.bool_var_ranges.push_back({"b", 1, 10, H::Sort::boolean(), {}}); });
    reject([](auto& m) { m.objectives[0].kind = H::ObjKind::MAXIMIZE; });
    return 0;
}
