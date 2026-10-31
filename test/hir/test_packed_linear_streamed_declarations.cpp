#include "somtparser/hir/packed_linear_io.h"
#include "somtparser/translation/translate.h"
#include "test_helpers.h"

#include <fstream>
#include <sstream>
#include <streambuf>
#include <string>
#include <utility>
#include <vector>

namespace H = SOMTParser::Uir::Hir;
namespace S = SOMTParser::Uir::Sem;
using SOMTParser::Lower::OmtDialect;
using SOMTParser::Uir::Diagnostics;

namespace {

class FailedBuffer : public std::streambuf {
protected:
    int_type overflow(int_type) override { return traits_type::eof(); }
};

std::size_t occurrences(const std::string& text, const std::string& needle) {
    std::size_t result = 0, pos = 0;
    while ((pos = text.find(needle, pos)) != std::string::npos) {
        ++result;
        pos += needle.size();
    }
    return result;
}

H::ConstraintModel modelWithAllReferenceKinds() {
    H::ConstraintModel model;
    const auto add = [&](std::string name, H::Sort sort, H::ExprPtr lo = {},
                         H::ExprPtr hi = {}, bool auxiliary = false) {
        H::VarDecl declaration;
        declaration.name = std::move(name);
        declaration.sort = std::move(sort);
        declaration.lower_bound = std::move(lo);
        declaration.upper_bound = std::move(hi);
        declaration.auxiliary = auxiliary;
        model.decls.push_back(std::move(declaration));
    };
    add("true", H::Sort::integer(), H::mkInt(0), H::mkInt(2));
    add("true!0", H::Sort::integer());
    add("|false|", H::Sort::real());
    add("false!0", H::Sort::real(), H::mkReal("-7"), H::mkReal("7"));
    add("x", H::Sort::integer(), H::mkInt(-1), H::mkInt(4));
    add("dep", H::Sort::integer(), H::mkOp(H::Op::SUB,
        {H::mkIdent("bound_only", H::Sort::integer()), H::mkInt(1)}));
    add("unused", H::Sort::real());
    add("aux", H::Sort::real(), {}, {}, true);
    add("flag", H::Sort::boolean());
    add("bound_only", H::Sort::integer());
    add("space column", H::Sort::real());

    H::FunDecl helper;
    helper.name = "helper";
    helper.params = {H::Sort::integer()};
    helper.result = H::Sort::integer();
    // A bound name can shadow a streamed global of another sort. Only its
    // free IDENT occurrences, not BOUND_VAR occurrences, require that column.
    helper.binders = {{"unused", H::Sort::integer()}};
    helper.body = H::mkOp(H::Op::ADD, {
        H::mkBoundVar("unused", H::Sort::integer()), H::mkIdent("x", H::Sort::integer())});
    model.funs.push_back(std::move(helper));
    H::Constraint ordinary;
    ordinary.formula = H::mkOp(H::Op::EQ, {H::mkIdent("dep", H::Sort::integer()),
        H::mkApply("helper", H::Sort::integer(), {H::mkInt(1)})});
    model.constraints.push_back(std::move(ordinary));
    H::Objective objective;
    objective.name = "cost";
    objective.kind = H::ObjKind::MAXIMIZE;
    objective.term = H::mkOp(H::Op::SUB,
        {H::mkIdent("aux", H::Sort::real()), H::mkReal("0.25")});
    model.objectives.push_back(std::move(objective));

    auto rows = std::make_shared<H::PackedLinearRows>();
    rows->numbers = {"1", "-1", "0.5"};
    H::PackedLinearRowBatch batch;
    batch.source_file = "deferred-declarations.hir";
    batch.terms = {{0, 0}, {2, 0}, {7, 1}};
    H::PackedLinearRow row;
    row.begin = 0;
    row.end = batch.terms.size();
    row.rhs = 2;
    row.source_line = 1;
    row.relation = H::LinearRowRelation::EQ;
    batch.rows.push_back(row);
    rows->batches.push_back(std::move(batch));
    model.packed_linear_rows = std::move(rows);
    return model;
}

} // namespace

int main(int argc, char** argv) {
    const auto model = modelWithAllReferenceKinds();
    Diagnostics diagnostics;
    SOMTParser::Uir::TranslationReport report;
    const auto parser = SOMTParser::newParser();
    SOMTParser::Lower::HirToParser lowering(parser);
    VERIFY(lowering.lowerPackedLinearPreamble(model, report, diagnostics, true, true));
    VERIFY(!diagnostics.hasErrors());
    VERIFY(lowering.varMap().size() == 5);
    for (const std::string name : {"x", "dep", "aux", "flag", "bound_only"}) {
        VERIFY(lowering.varMap().count(name) == 1);
    }
    VERIFY(report.stats().num_vars == model.decls.size());
    std::vector<std::string> symbols;
    std::vector<std::string> emitted_names;
    for (const auto& declaration : model.decls) {
        emitted_names.push_back(lowering.emittedSymbolName(declaration.name, diagnostics));
        symbols.push_back(SOMTParser::smtSymbol(emitted_names.back()));
    }
    VERIFY(symbols[0] == "true!1" && symbols[1] == "true!0");
    VERIFY(symbols[2] == "false!1" && symbols[3] == "false!0");
    std::ostringstream deferred;
    VERIFY(H::writePackedLinearDeclarationsSmt2(model, symbols, lowering, deferred, diagnostics));
    VERIFY(occurrences(deferred.str(), "(declare-fun ") == 6);
    VERIFY(deferred.str().find("(declare-fun unused () Real)") != std::string::npos);
    VERIFY(deferred.str().find("(declare-fun |space column| () Real)") != std::string::npos);

    // Direct callers keep their previous complete Parser variable map unless
    // they explicitly request complementary declaration streaming.
    const auto old_parser = SOMTParser::newParser();
    SOMTParser::Lower::HirToParser old_lowering(old_parser);
    VERIFY(old_lowering.lowerPackedLinearPreamble(model, report, diagnostics, true));
    VERIFY(old_lowering.varMap().size() == model.decls.size());
    std::ostringstream no_duplicates;
    VERIFY(H::writePackedLinearDeclarationsSmt2(model, symbols, old_lowering, no_duplicates, diagnostics));
    VERIFY(no_duplicates.str().empty());

    // Incorrect maps and output failures must not be reported as a complete
    // streamed module. The map preflight precedes any declaration output.
    auto wrong = symbols;
    wrong.back() = "unrelated";
    std::ostringstream untouched;
    Diagnostics rejected;
    VERIFY(!H::writePackedLinearDeclarationsSmt2(model, wrong, lowering, untouched, rejected));
    VERIFY(untouched.str().empty());
    wrong.pop_back();
    Diagnostics short_map;
    VERIFY(!H::writePackedLinearDeclarationsSmt2(model, wrong, lowering, untouched, short_map));
    VERIFY(untouched.str().empty());
    FailedBuffer buffer;
    std::ostream failed(&buffer);
    Diagnostics io;
    VERIFY(!H::writePackedLinearDeclarationsSmt2(model, symbols, lowering, failed, io));
    VERIFY(io.hasErrors());

    SOMTParser::TranslateOptions options;
    options.profile_id = "feasibility";
    options.omt_dialect = OmtDialect::None;
    const auto actual = SOMTParser::translate(model, options);
    if (!actual.ok()) {
        for (const auto& d : actual.diagnostics().all()) std::cerr << d.message << '\n';
    }
    VERIFY(actual.ok() && actual.usesPackedSmtStream());
    VERIFY(actual.objectiveCount() == 1);
    for (const auto dialect : {OmtDialect::None, OmtDialect::Z3,
                               OmtDialect::SmtLib2025, OmtDialect::OptiMathSAT}) {
        const auto text = actual.toSmt2(dialect);
        for (const auto& symbol : symbols) {
            VERIFY(occurrences(text, "(declare-fun " + symbol + " () ") == 1);
        }
        VERIFY((text.find("(maximize ") != std::string::npos)
               == (dialect == OmtDialect::Z3 || dialect == OmtDialect::OptiMathSAT));
        VERIFY((text.find("(define-objective cost ") != std::string::npos)
               == (dialect == OmtDialect::SmtLib2025));
    }
    const auto& target = actual.semantics().stages().back();
    for (const auto& symbol : emitted_names) {
        std::size_t found = 0;
        for (const auto& entry : target.target_signature.symbols) {
            if (entry.name == symbol) { ++found; }
        }
        VERIFY(found == 1);
    }
    const auto source_contract = S::directLanguageToRelationalContract(
        model, "mps", SOMTParser::Uir::Fidelity::exact());
    bool has_unused = false;
    for (const auto& observation : source_contract.projection.observables) {
        VERIFY(observation.source_name != "aux" && observation.target_name != "aux");
        has_unused |= observation.source_name == "unused";
    }
    VERIFY(has_unused);
    for (const auto& symbol : source_contract.source_signature.symbols) { VERIFY(symbol.name != "aux"); }

    auto expanded = model;
    expanded.packed_linear_rows.reset();
    H::Constraint equation;
    equation.formula = H::mkOp(H::Op::EQ, {
        H::mkOp(H::Op::ADD, {H::mkIdent("true", H::Sort::integer()),
                             H::mkIdent("|false|", H::Sort::real())}),
        H::mkOp(H::Op::ADD, {H::mkIdent("aux", H::Sort::real()), H::mkReal("0.5")})});
    expanded.constraints.push_back(std::move(equation));
    const auto expected = SOMTParser::translate(expanded, options);
    VERIFY(expected.ok());
    if (argc == 2) {
        std::ofstream packed(std::string(argv[1]) + "/packed.smt2");
        std::ofstream ordinary(std::string(argv[1]) + "/expanded.smt2");
        packed << actual.toSmt2(OmtDialect::Z3);
        ordinary << expected.toSmt2(OmtDialect::Z3);
        VERIFY(packed.good() && ordinary.good());
    }

    H::ConstraintModel free_columns;
    free_columns.packed_linear_rows = std::make_shared<H::PackedLinearRows>();
    for (std::size_t i = 0; i < 2048; ++i) {
        H::VarDecl declaration;
        declaration.name = "free" + std::to_string(i);
        declaration.sort = H::Sort::real();
        free_columns.decls.push_back(std::move(declaration));
    }
    const auto free_parser = SOMTParser::newParser();
    SOMTParser::Lower::HirToParser free_lowering(free_parser);
    VERIFY(free_lowering.lowerPackedLinearPreamble(free_columns, report, diagnostics, true, true));
    VERIFY(free_lowering.varMap().empty());
    const auto free_translation = SOMTParser::translate(free_columns, options);
    VERIFY(free_translation.ok());
    VERIFY(occurrences(free_translation.toSmt2(OmtDialect::None), "(declare-fun free") == 2048);
    VERIFY(free_translation.semantics().stages().back().target_signature.symbols.size() == 2048);
    return 0;
}
