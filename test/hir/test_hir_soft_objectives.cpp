#include "somtparser/hir/soft_objectives.h"
#include "somtparser/hir/typecheck.h"
#include "somtparser/translation/semantics.h"
#include "somtparser/translation/translate.h"
#include "test_helpers.h"

#include <algorithm>
#include <limits>
#include <string>
#include <utility>
#include <vector>

namespace H = SOMTParser::Uir::Hir;
namespace U = SOMTParser::Uir;
namespace L = SOMTParser::Lower;

static H::Constraint soft(H::ExprPtr formula, const std::string& weight,
                          const std::string& group = {}) {
    H::Constraint result;
    result.formula = std::move(formula);
    result.soft = true;
    result.weight_text = weight;
    result.group = group;
    result.loc = {"preferences.hir", 8, 3};
    return result;
}

static bool accepts(const H::ConstraintModel& model) {
    U::Diagnostics diagnostics;
    const bool result = H::typeCheck(model, diagnostics);
    VERIFY(result == !diagnostics.hasErrors());
    return result;
}

static H::ConstraintModel twoGroups() {
    H::ConstraintModel model;
    model.decls.push_back({"p", H::Sort::boolean(), {}, {}, {}});
    const auto p = H::mkIdent("p", H::Sort::boolean());
    model.constraints.push_back(soft(p, "1", "z_first"));
    model.constraints.push_back(soft(H::mkOp(H::Op::NOT, {p}), "100", "a_second"));
    return model;
}

// Only this regression fixture rewrites soft groups to explicit cost terms.
// Production translation retains assert-soft. The fixture exercises a genuine
// post-pass shape change without changing any feasible assignment or cost.
class ExplicitCostFixturePass : public U::Pass {
public:
    std::string id() const override { return "decompose-globals"; }
    U::PassTraits traits() const override {
        U::PassTraits result;
        result.reads_encoding_style = true;
        return result;
    }
    bool run(H::ConstraintModel& model, U::LowerContext& context) override {
        VERIFY(model.objectives.empty());
        const auto groups = H::softObjectiveGroups(model);
        for (const auto& group : groups) {
            std::vector<H::ExprPtr> costs;
            for (const auto& constraint : model.constraints) {
                if (constraint.soft && constraint.group == group) {
                    costs.push_back(H::mkOp(H::Op::ITE,
                        {constraint.formula, H::mkInt(0), H::mkInt(constraint.weight_text)}));
                }
            }
            VERIFY(!costs.empty());
            model.objectives.push_back({H::ObjKind::MINIMIZE,
                costs.size() == 1 ? costs.front() : H::mkOp(H::Op::ADD, costs), "", {}});
        }
        model.constraints.erase(std::remove_if(model.constraints.begin(), model.constraints.end(),
            [](const H::Constraint& constraint) { return constraint.soft; }), model.constraints.end());
        context.report->addChoice({"test-fixture", "soft-cost-vector", "explicit-cost-terms",
            U::Fidelity::exact(), "one exact violation-cost term per group, in unchanged order"});
        return true;
    }
};

int main() {
    // The old checker counted zero objectives here, accepting SINGLE while
    // rejecting the explicit lexicographic policy required for two costs.
    auto model = twoGroups();
    VERIFY(H::objectiveCountWithSoft(model) == 2);
    VERIFY(!accepts(model));
    model.objective_combination = H::ObjectiveCombination::LEXICOGRAPHIC;
    VERIFY(accepts(model));
    const std::vector<std::string> expected_groups = {"z_first", "a_second"};
    VERIFY(H::softObjectiveGroups(model) == expected_groups);

    // Semantic metadata describes the same complete vector as the emitter.
    model.decls.push_back({"x", H::Sort::integer(), {}, {}, {}});
    model.objectives.push_back({H::ObjKind::MAXIMIZE,
        H::mkIdent("x", H::Sort::integer()), "", {}});
    VERIFY(accepts(model));
    const auto contract = U::Sem::relationalToSmtContract(model, true);
    U::Diagnostics contract_diagnostics;
    VERIFY(contract.validate(contract_diagnostics));
    VERIFY(contract.objectives.source == U::Sem::ObjectiveOrder::LEXICOGRAPHIC);
    const std::vector<H::ObjKind> expected_directions = {
        H::ObjKind::MINIMIZE, H::ObjKind::MINIMIZE, H::ObjKind::MAXIMIZE};
    VERIFY(contract.objectives.source_directions == expected_directions);
    VERIFY(contract.objectives.target_directions == expected_directions);

    SOMTParser::TranslateOptions options;
    options.omt_dialect = L::OmtDialect::Z3;
    auto translated = SOMTParser::translate(model, options);
    for (const auto& diagnostic : translated.diagnostics().all())
        std::cerr << diagnostic.message << '\n';
    VERIFY(translated.ok());
    VERIFY(translated.objectiveCount() == 3);
    VERIFY(translated.report().stats().num_objectives == 3);
    const auto text = translated.toSmt2(L::OmtDialect::Z3);
    VERIFY(text.find(":opt.priority lex") != std::string::npos);
    VERIFY(text.find(":id z_first") < text.find(":id a_second"));
    VERIFY(text.find(":id a_second") < text.find("(maximize"));
    VERIFY(translated.toSmt2(L::OmtDialect::Z3) == text);
    VERIFY(model.constraints[0].formula && model.constraints[1].formula);
    VERIFY(translated.parser()->getSoftAssertions().size() == 2);

    // Vendor priorities and GOMT named soft objectives preserve the same
    // Pareto/independent grouping; GOMT has one optimization query, no check-sat.
    for (const auto combination : {H::ObjectiveCombination::PARETO,
                                  H::ObjectiveCombination::BOX}) {
        auto grouped = twoGroups();
        grouped.objective_combination = combination;
        auto result = SOMTParser::translate(grouped, options);
        VERIFY(result.ok() && result.objectiveCount() == 2);
        VERIFY(result.toSmt2(L::OmtDialect::Z3).find(
            combination == H::ObjectiveCombination::PARETO
                ? ":opt.priority pareto" : ":opt.priority box") != std::string::npos);
        options.omt_dialect = L::OmtDialect::SmtLib2025;
        const auto proposal = SOMTParser::translate(grouped, options);
        VERIFY(proposal.ok());
        const auto gomt = proposal.toSmt2(L::OmtDialect::Gomt);
        VERIFY(gomt.find("(define-maxsmt-objective ") != std::string::npos);
        VERIFY(gomt.find(":objective ") != std::string::npos);
        VERIFY(gomt.find(":id ") == std::string::npos);
        VERIFY(gomt.find("(optimize-sat ") != std::string::npos);
        VERIFY(gomt.find("(check-sat)") == std::string::npos);
        VERIFY(gomt.find(combination == H::ObjectiveCombination::PARETO
            ? "OBJECTIVE_PARETO" : "OBJECTIVE_BOX") != std::string::npos);
        options.omt_dialect = L::OmtDialect::Z3;
    }

    // Textual quoting does not create a second SMT symbol. The default group
    // is separate; repeated items in either group are not deduplicated.
    H::ConstraintModel names;
    names.constraints.push_back(soft(H::mkBool(true), "1", "g"));
    names.constraints.push_back(soft(H::mkBool(false), "3", "|g|"));
    VERIFY(H::objectiveCountWithSoft(names) == 1 && accepts(names));
    names.objective_combination = H::ObjectiveCombination::LEXICOGRAPHIC;
    VERIFY(!accepts(names));
    names.constraints.push_back(soft(H::mkBool(false), "5"));
    VERIFY(H::objectiveCountWithSoft(names) == 2 && accepts(names));

    // Packed WCNF's unnamed cost remains one effective objective and has
    // consistent metadata even though no materialized parser is available.
    H::ConstraintModel packed;
    packed.bool_var_ranges.push_back({"b", 1, 1, H::Sort::boolean(), {}});
    H::PackedBoolClauseBatch batch;
    batch.clause_offsets = {0, 1, 2};
    batch.literals = {1, -1};
    batch.weight_offsets = {0, 1, 2};
    batch.weight_bytes = "23";
    batch.source_lines = {1, 2};
    packed.packed_bool_clauses.push_back(batch);
    auto compact = SOMTParser::translate(packed, options);
    VERIFY(compact.ok() && compact.usesPackedSmtStream());
    VERIFY(compact.objectiveCount() == 1);
    VERIFY(compact.report().stats().num_objectives == 1);
    VERIFY(compact.toSmt2(L::OmtDialect::Z3).find("assert-soft") != std::string::npos);
    packed.packed_bool_clauses[0].weight_offsets = {0, 0, 0};
    packed.packed_bool_clauses[0].weight_bytes.clear();
    VERIFY(H::objectiveCountWithSoft(packed) == 0);

    // Validate native callers too, before a GMP constructor or raw :id emitter
    // can see invalid text. Preserve the existing fractional double interface.
    for (const auto* weight : {"0", "000", "-1", "+1", "1/2", "1.0", "1e3", "1)"}) {
        H::ConstraintModel bad;
        bad.constraints.push_back(soft(H::mkBool(true), weight));
        U::Diagnostics diagnostics;
        VERIFY(!H::typeCheck(bad, diagnostics));
        VERIFY(diagnostics.all().front().loc.file == "preferences.hir");
    }
    for (const auto* group : {"bad group", "1bad", "|unclosed", "||", "a|b", "|a\\b|", "let"}) {
        H::ConstraintModel bad;
        bad.constraints.push_back(soft(H::mkBool(true), "1", group));
        VERIFY(!accepts(bad));
    }
    H::ConstraintModel legacy;
    legacy.constraints.push_back(soft(H::mkBool(true), ""));
    legacy.constraints[0].weight = 2.5;
    VERIFY(accepts(legacy));
    for (const auto dialect : {L::OmtDialect::Z3, L::OmtDialect::OptiMathSAT, L::OmtDialect::Gomt}) {
        SOMTParser::TranslateOptions fractional_options;
        fractional_options.omt_dialect = dialect;
        const auto result = SOMTParser::translate(legacy, fractional_options);
        VERIFY(result.ok());
        const auto output = result.toSmt2(dialect);
        VERIFY(output.find(":weight 2.5") != std::string::npos);
        VERIFY(output.find(":weight 5/2") == std::string::npos);
        SOMTParser::Parser restored;
        VERIFY(restored.parseStr(output));
    }
    for (double weight : {0.0, -1.0, std::numeric_limits<double>::infinity(),
                          std::numeric_limits<double>::quiet_NaN()}) {
        legacy.constraints[0].weight = weight;
        VERIFY(!accepts(legacy));
    }
    legacy.constraints[0].weight_text = "100000000000000000000000000000000000000000000000001";
    VERIFY(accepts(legacy)); // Exact text is authoritative, even over NaN fallback.

    // OptiMathSAT's group identifier denotes an actual cost symbol. Reusing a
    // declared variable named same would constrain its value to the soft cost
    // and make this satisfiable fixture UNSAT (same=3, attainable costs 4/9).
    // The consuming path has released HIR declaration metadata at emission.
    {
        H::ConstraintModel collision;
        collision.decls.push_back({"p", H::Sort::boolean(), {}, {}, {}});
        collision.decls.push_back({"same", H::Sort::integer(), {}, {}, {}});
        const auto p = H::mkIdent("p", H::Sort::boolean());
        H::Constraint hard;
        hard.formula = H::mkOp(H::Op::EQ,
            {H::mkIdent("same", H::Sort::integer()), H::mkInt(3)});
        collision.constraints.push_back(hard);
        collision.constraints.push_back(soft(p, "9", "same"));
        collision.constraints.push_back(soft(H::mkOp(H::Op::NOT, {p}), "4", "same"));
        auto consumed = collision;
        auto parser = SOMTParser::newParser();
        L::HirToParser lowering(parser);
        U::TranslationReport report;
        U::Diagnostics diagnostics;
        VERIFY(lowering.lowerConsumingForTranslation(consumed, report, diagnostics));
        VERIFY(consumed.decls.empty());
        const auto commands = L::emitObjectives(consumed, L::OmtDialect::OptiMathSAT,
                                               lowering, diagnostics, 1);
        VERIFY(!diagnostics.hasErrors());
        VERIFY(commands.find(":id same_)") != std::string::npos);
        VERIFY(commands.find("(minimize same_)") != std::string::npos);
        VERIFY(commands.find(":id same)") == std::string::npos);
        options.omt_dialect = L::OmtDialect::OptiMathSAT;
        const auto translated = SOMTParser::translate(collision, options);
        VERIFY(translated.ok());
        const auto output = translated.toSmt2();
        VERIFY(output.find(":produce-models true") < output.find("(declare-"));
        VERIFY(output.find(":id same)") == std::string::npos);
        VERIFY(output.find("(minimize same_)") != std::string::npos);
        std::size_t assertions = 0, position = 0;
        while ((position = output.find("(assert-soft ", position)) != std::string::npos) {
            ++assertions;
            ++position;
        }
        VERIFY(assertions == 2); // Hard-only body must not duplicate soft records.
    }
    // Re-rendering real soft events also keeps the unnamed group separate
    // from an explicit group named I (OptiMathSAT's implicit default label).
    {
        H::ConstraintModel groups;
        groups.decls.push_back({"p", H::Sort::boolean(), {}, {}, {}});
        const auto p = H::mkIdent("p", H::Sort::boolean());
        groups.constraints.push_back(soft(p, "3"));
        groups.constraints.push_back(soft(H::mkOp(H::Op::NOT, {p}), "7", "I"));
        groups.objective_combination = H::ObjectiveCombination::LEXICOGRAPHIC;
        options.omt_dialect = L::OmtDialect::OptiMathSAT;
        const auto translated = SOMTParser::translate(groups, options);
        VERIFY(translated.ok());
        const auto output = translated.toSmt2();
        VERIFY(output.find("(minimize __somt_soft_default)") != std::string::npos);
        VERIFY(output.find("(minimize I)") != std::string::npos);
        VERIFY(output.find(":id __somt_soft_default)") != std::string::npos);
        VERIFY(output.find(":id I)") != std::string::npos);
    }

    // Keep this last: it replaces a built-in pass in this standalone process.
    // Pre-pass caching incorrectly remembers two soft groups and refuses the
    // perfectly renderable post-pass explicit vector under the 2025 dialect.
    U::PassRegistry::instance().add(std::make_shared<ExplicitCostFixturePass>());
    auto before_pass = twoGroups();
    before_pass.objective_combination = H::ObjectiveCombination::LEXICOGRAPHIC;
    options.omt_dialect = L::OmtDialect::SmtLib2025;
    auto rewritten = SOMTParser::translate(before_pass, options);
    for (const auto& diagnostic : rewritten.diagnostics().all())
        std::cerr << diagnostic.message << '\n';
    VERIFY(rewritten.ok());
    VERIFY(rewritten.objectiveCount() == 2);
    VERIFY(rewritten.report().stats().num_objectives == 2);
    VERIFY(rewritten.parser()->getSoftAssertions().empty());
    VERIFY(rewritten.toSmt2(L::OmtDialect::SmtLib2025).find("define-multi-objective")
        != std::string::npos);
    const auto rewritten_z3 = rewritten.toSmt2(L::OmtDialect::Z3);
    VERIFY(rewritten_z3.find("assert-soft") == std::string::npos);
    VERIFY(rewritten_z3.find(":opt.priority lex") != std::string::npos);
    VERIFY(before_pass.constraints.size() == 2 && before_pass.objectives.empty());
    return 0;
}
