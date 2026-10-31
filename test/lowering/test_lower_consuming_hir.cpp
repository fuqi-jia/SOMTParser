#include "somtparser/lowering/hir_to_parser.h"
#include "somtparser/lowering/omt_emitter.h"
#include "somtparser/translation/semantics.h"
#include "somtparser/translation/translate.h"
#include "test_helpers.h"

#include <algorithm>
#include <memory>
#include <string>

namespace H = SOMTParser::Uir::Hir;
namespace U = SOMTParser::Uir;
namespace L = SOMTParser::Lower;

static H::ConstraintModel sample() {
    H::ConstraintModel model;
    H::VarDecl x;
    x.name = "x";
    x.sort = H::Sort::integer();
    x.lower_bound = H::mkInt(0);
    x.upper_bound = H::mkInt(9);
    model.decls.push_back(x);
    H::FunDecl f;
    f.name = "next";
    f.params = {H::Sort::integer()};
    f.result = H::Sort::integer();
    f.binders = {{"n", H::Sort::integer()}};
    f.body = H::mkOp(H::Op::ADD,
        {H::mkBoundVar("n", H::Sort::integer()), H::mkInt(1)});
    model.funs.push_back(f);
    H::Constraint hard;
    hard.formula = H::mkOp(H::Op::EQ,
        {H::mkApply("next", H::Sort::integer(),
            {H::mkIdent("x", H::Sort::integer())}), H::mkInt(4)});
    model.constraints.push_back(hard);
    H::Constraint quantified;
    quantified.formula = H::mkForall({{"a", H::Sort::integer()}},
        H::mkExists({{"b", H::Sort::integer()}},
            H::mkOp(H::Op::EQ, {H::mkBoundVar("a", H::Sort::integer()),
                                H::mkBoundVar("b", H::Sort::integer())})));
    model.constraints.push_back(quantified);
    H::Constraint soft;
    soft.formula = H::mkOp(H::Op::EQ,
        {H::mkIdent("x", H::Sort::integer()), H::mkInt(0)});
    soft.soft = true;
    soft.weight_text = "12345678901234567890123456789";
    soft.group = "preference";
    model.constraints.push_back(soft);
    H::Objective objective;
    objective.kind = H::ObjKind::MINIMIZE;
    objective.term = H::mkIdent("x", H::Sort::integer());
    model.objectives.push_back(objective);
    model.objective_combination = H::ObjectiveCombination::LEXICOGRAPHIC;
    return model;
}

int main() {
    auto original = sample();
    auto consumed = sample();
    std::weak_ptr<const H::Expr> hard = consumed.constraints[0].formula;
    std::weak_ptr<const H::Expr> soft = consumed.constraints[2].formula;
    std::weak_ptr<const H::Expr> definition = consumed.funs[0].body;
    auto plain_parser = SOMTParser::newParser();
    auto consuming_parser = SOMTParser::newParser();
    L::HirToParser plain(plain_parser), consuming(consuming_parser);
    U::TranslationReport plain_report, consuming_report;
    U::Diagnostics plain_diags, consuming_diags;
    VERIFY(plain.lower(original, plain_report, plain_diags));
    VERIFY(consuming.lowerConsuming(consumed, consuming_report, consuming_diags));
    VERIFY(hard.expired() && soft.expired() && definition.expired());
    VERIFY(original.constraints[0].formula && original.funs[0].body);
    VERIFY(plain_parser->dumpSMT2() == consuming_parser->dumpSMT2());
    VERIFY(plain_report.stats().num_constraints == consuming_report.stats().num_constraints);
    VERIFY(consuming_report.stats().num_constraints == 3);
    VERIFY(consuming_report.stats().max_quantifier_alternations == 1);
    VERIFY(plain_report.stats().num_smt_nodes == consuming_report.stats().num_smt_nodes);
    VERIFY(L::emitObjectives(original, L::OmtDialect::Z3, plain, plain_diags)
        == L::emitObjectives(consumed, L::OmtDialect::Z3, consuming, consuming_diags));
    VERIFY(!plain_diags.hasErrors() && !consuming_diags.hasErrors());
    // A soft-only optimization must retain its decision and objective metadata
    // after releasing the formula; erasing constraint records would lose it.
    consumed.objectives.clear();
    consumed.objective_combination = H::ObjectiveCombination::SINGLE;
    VERIFY(U::Sem::hasOptimization(consumed));
    const auto contract = U::Sem::relationalToSmtContract(consumed, true);
    U::Diagnostics contract_diags;
    VERIFY(contract.validate(contract_diags));
    VERIFY(contract.objectives.source == U::Sem::ObjectiveOrder::MINIMIZE);
    VERIFY(contract.objectives.source_directions.size() == 1);
    VERIFY(consumed.constraints[2].weight_text == "12345678901234567890123456789");
    VERIFY(consumed.decls[0].lower_bound && consumed.decls[0].upper_bound);

    // Pruning the private lookup environment must not drop declarations or
    // captured globals from function bodies, or break objective re-emission.
    {
        auto model = sample();
        model.decls.push_back({"g", H::Sort::integer(), {}, {}, {}});
        model.decls.push_back({"unused", H::Sort::integer(), {}, {}, {}});
        model.funs[0].body = H::mkOp(H::Op::ADD,
            {H::mkBoundVar("n", H::Sort::integer()),
             H::mkIdent("g", H::Sort::integer())});
        model.objectives[0].term = H::mkApply("next", H::Sort::integer(),
            {H::mkIdent("x", H::Sort::integer())});
        auto parser = SOMTParser::newParser();
        L::HirToParser lowering(parser);
        U::TranslationReport report;
        U::Diagnostics diags;
        VERIFY(lowering.lower(model, report, diags));
        VERIFY(L::validateObjectives(model, lowering, diags));
        const auto body = parser->dumpSMT2();
        const auto objective = L::emitObjectives(model, L::OmtDialect::Z3, lowering, diags);
        lowering.retainObjectiveBindings(model);
        VERIFY(lowering.varMap().size() == 1 && lowering.varMap().count("x") == 1);
        VERIFY(body == parser->dumpSMT2());
        VERIFY(objective == L::emitObjectives(model, L::OmtDialect::Z3, lowering, diags));
        VERIFY(objective == L::emitObjectives(model, L::OmtDialect::Z3, lowering, diags));
        VERIFY(!diags.hasErrors());
        model.objectives.clear();
        model.objective_combination = H::ObjectiveCombination::SINGLE;
        lowering.retainObjectiveBindings(model);
        VERIFY(lowering.varMap().empty());
        VERIFY(body == parser->dumpSMT2());
        VERIFY(L::emitObjectives(model, L::OmtDialect::Z3, lowering, diags).empty());
    }

    // A caller stored before its callee must be emitted after that callee in
    // both lowering modes. Consuming lowering clears body roots while defining
    // functions; that must not make definitions look like uninterpreted decls
    // when the symbol-name order is rebuilt.
    const auto verify_dependency_order = [](bool consume) {
        H::ConstraintModel model;
        H::FunDecl caller;
        caller.name = "caller";
        caller.params = {H::Sort::integer()};
        caller.result = H::Sort::integer();
        caller.binders = {{"x", H::Sort::integer()}};
        caller.body = H::mkApply("callee", H::Sort::integer(),
            {H::mkBoundVar("x", H::Sort::integer())});
        H::FunDecl callee;
        callee.name = "callee";
        callee.params = {H::Sort::integer()};
        callee.result = H::Sort::integer();
        callee.binders = {{"y", H::Sort::integer()}};
        callee.body = H::mkOp(H::Op::ADD,
            {H::mkBoundVar("y", H::Sort::integer()), H::mkInt(1)});
        model.funs.push_back(caller);
        model.funs.push_back(callee);
        H::Constraint constraint;
        constraint.formula = H::mkOp(H::Op::EQ,
            {H::mkApply("caller", H::Sort::integer(), {H::mkInt(0)}), H::mkInt(1)});
        model.constraints.push_back(std::move(constraint));
        auto parser = SOMTParser::newParser();
        L::HirToParser lowering(parser);
        U::TranslationReport report;
        U::Diagnostics diagnostics;
        const bool lowered = consume
            ? lowering.lowerConsuming(model, report, diagnostics)
            : lowering.lower(model, report, diagnostics);
        VERIFY(lowered && !diagnostics.hasErrors());
        if (consume) { VERIFY(!model.funs[0].body && !model.funs[1].body); }
        const auto& names = parser->getSymbolManager()->getFunctionNames();
        const auto callee_pos = std::find(names.begin(), names.end(), "callee");
        const auto caller_pos = std::find(names.begin(), names.end(), "caller");
        VERIFY(callee_pos != names.end() && caller_pos != names.end());
        VERIFY(callee_pos < caller_pos);
        const std::string smt = parser->dumpSMT2();
        auto reread = SOMTParser::newParser();
        VERIFY(reread->parseStr(smt));
        return smt;
    };
    VERIFY(verify_dependency_order(false) == verify_dependency_order(true));

    // Fresh formal spellings advance monotonically and still avoid source
    // globals that deliberately occupy early generated-name slots.
    {
        H::ConstraintModel model;
        model.decls.push_back({"__somt_hir_param_0", H::Sort::integer(), {}, {}, {}});
        model.decls.push_back({"__somt_hir_param_2", H::Sort::integer(), {}, {}, {}});
        H::FunDecl function;
        function.name = "many_params";
        function.result = H::Sort::integer();
        for (int i = 0; i < 48; ++i) {
            function.params.push_back(H::Sort::integer());
            function.binders.push_back({"p" + std::to_string(i), H::Sort::integer()});
        }
        function.body = H::mkOp(H::Op::ADD,
            {H::mkBoundVar("p0", H::Sort::integer()),
             H::mkIdent("__somt_hir_param_0", H::Sort::integer())});
        model.funs.push_back(std::move(function));
        auto parser = SOMTParser::newParser();
        L::HirToParser lowering(parser);
        U::TranslationReport report;
        U::Diagnostics diagnostics;
        VERIFY(lowering.lower(model, report, diagnostics));
        const std::string smt = parser->dumpSMT2();
        VERIFY(smt.find("(__somt_hir_param_1 Int)") != std::string::npos);
        VERIFY(smt.find("(__somt_hir_param_3 Int)") != std::string::npos);
        VERIFY(smt.find("(__somt_hir_param_0 Int)") == std::string::npos);
        VERIFY(smt.find("(__somt_hir_param_2 Int)") == std::string::npos);
        VERIFY(smt.find("(declare-fun __somt_hir_param_0 () Int)") != std::string::npos);
        auto reread = SOMTParser::newParser();
        VERIFY(reread->parseStr(smt));
    }

    // translateHir must consume its private container, never the caller's roots.
    SOMTParser::TranslateOptions options;
    options.omt_dialect = L::OmtDialect::Z3;
    const auto first = SOMTParser::translate(original, options);
    const auto second = SOMTParser::translate(original, options);
    VERIFY(first.ok() && second.ok());
    const std::string first_smt = first.toSmt2(L::OmtDialect::Z3);
    VERIFY(first_smt == first.toSmt2(L::OmtDialect::Z3));
    VERIFY(first_smt == second.toSmt2(L::OmtDialect::Z3));
    // Effective costs include the soft group before the explicit arithmetic
    // objective. The consuming path preserves both order and direction.
    VERIFY(first.objectiveCount() == 2);
    VERIFY(first.report().stats().num_objectives == 2);
    VERIFY(original.objectives.size() == 1);
    VERIFY(first.parser()->getSoftAssertions().size() == 1);
    const auto soft_position = first_smt.find(":id preference");
    const auto explicit_position = first_smt.find("(minimize x)");
    VERIFY(soft_position != std::string::npos && explicit_position != std::string::npos);
    VERIFY(soft_position < explicit_position);
    VERIFY(first_smt.find(":weight 12345678901234567890123456789") != std::string::npos);
    VERIFY(first_smt.find(":opt.priority lex") != std::string::npos);
    VERIFY(first_smt.find("(minimize ", explicit_position + 1) == std::string::npos);
    // Translation owns the HIR arithmetic objective; its lower-level Parser
    // contains the core relation and registered soft assertions. Verify the
    // complete objective above through Translation's explicit Z3 export.
    VERIFY(first.parser()->dumpSMT2(L::OmtDialect::Z3).find("(minimize x)") == std::string::npos);
    const std::vector<H::ObjKind> directions = {
        H::ObjKind::MINIMIZE, H::ObjKind::MINIMIZE};
    VERIFY(!first.semantics().stages().empty());
    for (const auto& stage : first.semantics().stages()) {
        VERIFY(stage.objectives.source == U::Sem::ObjectiveOrder::LEXICOGRAPHIC);
        VERIFY(stage.objectives.target == U::Sem::ObjectiveOrder::LEXICOGRAPHIC);
        VERIFY(stage.objectives.source_directions == directions);
        VERIFY(stage.objectives.target_directions == directions);
        VERIFY(stage.objectives.order_preserving && stage.objectives.order_reflecting);
    }
    U::Diagnostics pipeline_diags;
    VERIFY(first.semantics().validate(pipeline_diags));
    VERIFY(!pipeline_diags.hasErrors());
    VERIFY(original.constraints[0].formula && original.constraints[2].formula);
    VERIFY(original.funs[0].body && original.objectives[0].term);
    VERIFY(original.decls.size() == 1 && original.decls[0].lower_bound
           && original.decls[0].upper_bound);
    VERIFY(original.funs.size() == 1 && original.constraints.size() == 3);

    // Failed lowering consumes only completed entries and reports failure.
    H::ConstraintModel invalid;
    H::Constraint good, bad;
    good.formula = H::mkBool(true);
    bad.formula = H::mkIdent("missing", H::Sort::boolean());
    invalid.constraints = {good, bad};
    auto failed_parser = SOMTParser::newParser();
    L::HirToParser failed(failed_parser);
    U::TranslationReport failed_report;
    U::Diagnostics failed_diags;
    VERIFY(!failed.lowerConsuming(invalid, failed_report, failed_diags));
    VERIFY(failed_diags.hasErrors());
    VERIFY(!invalid.constraints[0].formula && invalid.constraints[1].formula);

    // Incremental hard-AND lowering preserves the target assertion structure
    // and leaves a shared immutable source root untouched.
    H::ConstraintModel hard_and_source;
    hard_and_source.decls = {{"p", H::Sort::boolean(), {}, {}, {}},
                             {"q", H::Sort::boolean(), {}, {}, {}}};
    const auto first_conjunct = H::mkIdent("p", H::Sort::boolean());
    const auto hard_and = H::mkOp(H::Op::AND,
        {first_conjunct, H::mkIdent("q", H::Sort::boolean())});
    hard_and_source.constraints.push_back({hard_and});
    H::ConstraintModel hard_and_consumed = hard_and_source;
    auto and_parser = SOMTParser::newParser();
    L::HirToParser and_lowering(and_parser);
    U::TranslationReport and_report;
    U::Diagnostics and_diags;
    VERIFY(and_lowering.lowerConsuming(hard_and_consumed, and_report, and_diags));
    VERIFY(!and_diags.hasErrors());
    VERIFY(and_parser->getAssertions().size() == 1);
    auto original_and_parser = SOMTParser::newParser();
    L::HirToParser original_and_lowering(original_and_parser);
    U::TranslationReport original_and_report;
    U::Diagnostics original_and_diags;
    VERIFY(original_and_lowering.lower(hard_and_source, original_and_report, original_and_diags));
    VERIFY(and_parser->dumpSMT2() == original_and_parser->dumpSMT2());
    VERIFY(hard_and_consumed.constraints[0].formula == nullptr);
    VERIFY(hard_and_source.constraints[0].formula == hard_and);
    VERIFY(hard_and->args.size() == 2 && hard_and->args[0] == first_conjunct);

    // A soft conjunction remains one weighted item with one group and weight.
    H::ConstraintModel soft_and;
    soft_and.decls = hard_and_source.decls;
    H::Constraint soft_group;
    soft_group.formula = hard_and;
    soft_group.soft = true;
    soft_group.weight_text = "7";
    soft_group.group = "one-preference";
    soft_and.constraints.push_back(soft_group);
    auto soft_and_parser = SOMTParser::newParser();
    L::HirToParser soft_and_lowering(soft_and_parser);
    U::TranslationReport soft_and_report;
    U::Diagnostics soft_and_diags;
    VERIFY(soft_and_lowering.lowerConsuming(soft_and, soft_and_report, soft_and_diags));
    VERIFY(!soft_and_diags.hasErrors());
    VERIFY(soft_and_parser->getAssertions().empty());
    VERIFY(soft_and_parser->getSoftAssertions().size() == 1);

    // Failure during a large hard conjunction consumes completed conjuncts
    // and retains only the unlowered suffix for a caller inspecting the model.
    H::ConstraintModel partial_and;
    partial_and.decls.push_back({"ok", H::Sort::boolean(), {}, {}, {}});
    H::ExprPtr completed = H::mkIdent("ok", H::Sort::boolean());
    const std::weak_ptr<const H::Expr> completed_weak = completed;
    partial_and.constraints.push_back({H::mkOp(H::Op::AND,
        {completed, H::mkIdent("missing", H::Sort::boolean())})});
    completed.reset();
    auto partial_parser = SOMTParser::newParser();
    L::HirToParser partial_lowering(partial_parser);
    U::TranslationReport partial_report;
    U::Diagnostics partial_diags;
    VERIFY(!partial_lowering.lowerConsuming(partial_and, partial_report, partial_diags));
    VERIFY(partial_diags.hasErrors());
    VERIFY(partial_parser->getAssertions().size() == 1);
    VERIFY(partial_and.constraints[0].formula);
    VERIFY(partial_and.constraints[0].formula->kind == H::ExprKind::IDENT);
    VERIFY(partial_and.constraints[0].formula->name == "missing");
    VERIFY(completed_weak.expired());
    return 0;
}
