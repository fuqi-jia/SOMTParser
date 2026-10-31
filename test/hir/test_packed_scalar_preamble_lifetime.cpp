#include "somtparser/translation/translate.h"
#include "test_helpers.h"

#include <fstream>
#include <memory>
#include <string>

using namespace SOMTParser;
namespace H = Uir::Hir;

namespace {
class ScalarLifetimeLanguage : public Lang::Language {
public:
    bool retain = false;
    H::ObjKind direction = H::ObjKind::MINIMIZE;
    H::ConstraintModelPtr retained;
    std::weak_ptr<const H::Expr> constraint;
    std::weak_ptr<const H::Expr> definition;

    std::string id() const override { return "scalar-lifetime"; }
    std::string displayName() const override { return "Scalar lifetime test"; }
    std::string version() const override { return "1"; }
    std::vector<std::string> extensions() const override { return {".scalar-lifetime"}; }
    const Lang::OpCoverage& coverage() const override { return coverage_; }

    Lang::ParseOutcome parse(const Lang::SourceUnit&, const Lang::ParseOptions&) override {
        auto model = std::make_shared<H::ConstraintModel>();
        H::VarDecl variable;
        variable.name = "x";
        variable.sort = H::Sort::integer();
        variable.lower_bound = H::mkInt(0);
        variable.upper_bound = H::mkInt(7);
        model->decls.push_back(variable);
        H::ScalarVarRange range;
        range.prefix = "cell[";
        range.count = 3;
        range.lower_bound = H::mkInt(-2);
        range.upper_bound = H::mkInt(5);
        model->scalar_var_ranges.push_back(range);
        H::FunDecl function;
        function.name = "relation";
        function.params = {H::Sort::integer()};
        function.result = H::Sort::boolean();
        function.binders = {{"u", H::Sort::integer()}};
        function.body = H::mkOp(H::Op::LE, {
            H::mkOp(H::Op::ADD, {H::mkBoundVar("u", H::Sort::integer()), H::mkInt(1)}),
            H::mkIdent("cell[0]", H::Sort::integer())});
        definition = function.body;
        model->funs.push_back(function);
        auto calls = std::make_shared<H::PackedFunctionCalls>();
        H::PackedFunctionCallBatch batch;
        batch.function = "relation";
        batch.arity = 1;
        batch.arguments = {{H::PackedScalarArgument::DECLARATION, 0}, {0, 1}};
        calls->batches.push_back(batch);
        model->packed_function_calls = calls;
        H::Constraint ordinary;
        ordinary.formula = H::mkOp(H::Op::AND, {
            H::mkOp(H::Op::GE, {H::mkIdent("x", H::Sort::integer()), H::mkInt(1)}),
            H::mkOp(H::Op::GT, {H::mkIdent("cell[0]", H::Sort::integer()), H::mkInt(0)}),
            H::mkForall({{"q", H::Sort::integer()}}, H::mkOp(H::Op::EQ, {
                H::mkBoundVar("q", H::Sort::integer()), H::mkBoundVar("q", H::Sort::integer())})),
            // Finite membership is intentionally decomposed to equalities by
            // the default pass. Subset keeps a real Set requirement until the
            // preamble is consumed, while also constraining the exported model.
            H::mkOp(H::Op::SET_SUBSET, {
                H::mkOp(H::Op::SET_SINGLETON, {H::mkIdent("x", H::Sort::integer())}),
                H::mkOp(H::Op::SET_UNION, {
                    H::mkOp(H::Op::SET_SINGLETON, {H::mkInt(1)}),
                    H::mkOp(H::Op::SET_SINGLETON, {H::mkInt(2)})})})});
        constraint = ordinary.formula;
        model->constraints.push_back(ordinary);
        H::Objective objective;
        objective.name = "cost";
        objective.kind = direction;
        objective.term = H::mkOp(H::Op::ADD, {
            H::mkIdent("x", H::Sort::integer()),
            H::mkIdent("cell[2]", H::Sort::integer())});
        model->objectives.push_back(objective);
        retained = retain ? model : nullptr;
        Lang::ParseOutcome outcome;
        outcome.model = std::move(model);
        return outcome;
    }
private:
    Lang::OpCoverage coverage_;
};
}

int main(int argc, char** argv) {
    auto language = std::make_shared<ScalarLifetimeLanguage>();
    Lang::LanguageRegistry::instance().add(language);
    Lang::SourceUnit source;
    source.inline_source = "model supplied by the test frontend";
    TranslateOptions options;
    options.language_id = language->id();
    options.omt_dialect = Lower::OmtDialect::Z3;
    std::size_t number = 0;
    for (const bool retained : {false, true}) {
        for (const auto direction : {H::ObjKind::MINIMIZE, H::ObjKind::MAXIMIZE}) {
            language->retain = retained;
            language->direction = direction;
            const auto translated = translate(source, options);
            VERIFY(translated.ok() && translated.usesPackedSmtStream());
            VERIFY(translated.report().stats().num_vars == 4);
            VERIFY(translated.objectiveCount() == 1);
            VERIFY(translated.setSolverRequirements().has_quantifiers);
            VERIFY(translated.setSolverRequirements().has_sets);
            if (retained) {
                VERIFY(!language->constraint.expired());
                VERIFY(!language->definition.expired());
                VERIFY(language->retained->constraints.size() == 1);
                VERIFY(language->retained->funs[0].body == language->definition.lock());
                VERIFY(language->retained->decls[0].lower_bound);
                VERIFY(language->retained->decls[0].upper_bound);
                // translateHir also gets its own container. Repeated use must
                // leave the caller's formulas, bounds, and definition intact.
                const auto repeated = translate(*language->retained, options);
                VERIFY(repeated.ok());
                VERIFY(language->retained->constraints[0].formula == language->constraint.lock());
            } else {
                // These are weak observations only: no test-held shared owner
                // can hide duplicated HIR roots retained after native lowering.
                VERIFY(language->constraint.expired());
                VERIFY(language->definition.expired());
            }
            const auto text = translated.toSmt2(Lower::OmtDialect::Z3);
            VERIFY(translated.toSmt2(Lower::OmtDialect::Z3) == text);
            VERIFY(text.find("cell[2]") != std::string::npos);
            VERIFY(translated.toSmt2(Lower::OmtDialect::SmtLib2025)
                       .find("(define-objective cost ") != std::string::npos);
            if (argc == 2) {
                std::ofstream file(std::string(argv[1]) + "/case-" + std::to_string(number) + ".smt2");
                file << text;
                VERIFY(file.good());
            }
            ++number;
        }
    }
    return 0;
}
