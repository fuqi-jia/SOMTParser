#include "somtparser/translation/translate.h"
#include "test_helpers.h"

#include <algorithm>
#include <fstream>
#include <memory>
#include <sstream>
#include <streambuf>
#include <string>
#include <utility>

namespace H = SOMTParser::Uir::Hir;
using SOMTParser::TranslateOptions;
using SOMTParser::Lower::OmtDialect;

namespace {

class FailingBuffer : public std::streambuf {
public:
    explicit FailingBuffer(std::size_t limit) : remaining_(limit) {}
protected:
    std::streamsize xsputn(const char*, std::streamsize size) override {
        const auto count = std::min(remaining_, static_cast<std::size_t>(size));
        remaining_ -= count;
        return static_cast<std::streamsize>(count);
    }
    int_type overflow(int_type value) override {
        if (traits_type::eq_int_type(value, traits_type::eof())) return traits_type::not_eof(value);
        if (!remaining_) return traits_type::eof();
        --remaining_;
        return value;
    }
private:
    std::size_t remaining_;
};

H::ConstraintModel makeModel(const std::string& name, bool integral, H::ObjKind direction) {
    H::ConstraintModel model;
    H::VarDecl declaration;
    declaration.name = name;
    declaration.sort = integral ? H::Sort::integer() : H::Sort::real();
    declaration.lower_bound = integral ? H::mkInt(0) : H::mkReal("0.0");
    declaration.upper_bound = integral ? H::mkInt(10) : H::mkReal("10.0");
    model.decls.push_back(declaration);
    const auto x = H::mkIdent(name, declaration.sort);
    H::Constraint guard;
    guard.formula = H::mkOp(H::Op::GE, {x, integral ? H::mkInt(1) : H::mkReal("1.0")});
    model.constraints.push_back(guard);
    H::Objective objective;
    objective.kind = direction;
    objective.name = "cost";
    objective.term = H::mkOp(H::Op::ADD, {x, H::mkReal("4.25")});
    model.objectives.push_back(objective);
    auto rows = std::make_shared<H::PackedLinearRows>();
    rows->numbers = {"1", "3.5"};
    H::PackedLinearRowBatch batch;
    batch.source_file = "mixed-numeric-hir";
    batch.terms.push_back({0, 0});
    H::PackedLinearRow row;
    row.begin = 0;
    row.end = 1;
    row.rhs = 1;
    row.source_line = 1;
    row.relation = H::LinearRowRelation::LE;
    batch.rows.push_back(row);
    rows->batches.push_back(std::move(batch));
    model.packed_linear_rows = std::move(rows);
    return model;
}

} // namespace

int main(int argc, char** argv) {
    std::size_t case_number = 0;
    for (const std::string name : {"true", "x y"}) {
        for (const bool integral : {true, false}) {
            for (const auto direction : {H::ObjKind::MINIMIZE, H::ObjKind::MAXIMIZE}) {
                auto model = makeModel(name, integral, direction);
                const auto storage = model.packed_linear_rows;
                TranslateOptions options;
                options.profile_id = "feasibility";
                options.omt_dialect = OmtDialect::None;
                const auto packed = SOMTParser::translate(model, options);
                if (!packed.ok()) {
                    for (const auto& diagnostic : packed.diagnostics().all()) std::cerr << diagnostic.message << '\n';
                }
                VERIFY(packed.ok());
                VERIFY(packed.usesPackedSmtStream());
                VERIFY(!packed.hasParser());
                VERIFY(packed.objectiveCount() == 1);
                VERIFY(model.packed_linear_rows == storage);
                VERIFY(model.constraints.size() == 1);
                // The explicit preamble route does not copy or consume input
                // declarations; ordinary lowering must still refuse to drop
                // packed rows. Compare its body to a separately assembled
                // ordinary-only model before testing complete packed export.
                {
                    SOMTParser::Uir::TranslationReport report;
                    SOMTParser::Uir::Diagnostics rejected_diags, preamble_diags, ordinary_diags;
                    auto rejected_parser = SOMTParser::newParser();
                    SOMTParser::Lower::HirToParser rejected(rejected_parser);
                    VERIFY(!rejected.lower(model, report, rejected_diags));
                    auto preamble_parser = SOMTParser::newParser();
                    SOMTParser::Lower::HirToParser preamble(preamble_parser);
                    VERIFY(preamble.lowerPackedLinearPreamble(model, report, preamble_diags));
                    auto ordinary = model;
                    ordinary.packed_linear_rows.reset();
                    auto ordinary_parser = SOMTParser::newParser();
                    SOMTParser::Lower::HirToParser ordinary_lowerer(ordinary_parser);
                    VERIFY(ordinary_lowerer.lower(ordinary, report, ordinary_diags));
                    std::ostringstream actual, expected;
                    preamble_parser->writeSMT2Module(actual);
                    ordinary_parser->writeSMT2Module(expected);
                    VERIFY(actual.str() == expected.str());
                    VERIFY(model.packed_linear_rows == storage);
                    VERIFY(model.decls.size() == 1 && model.constraints.size() == 1);
                    SOMTParser::Uir::Diagnostics wrong_mode;
                    VERIFY(!ordinary_lowerer.lowerPackedLinearPreamble(ordinary, report, wrong_mode));
                }
                bool parser_rejected = false;
                try { (void)packed.parser(); }
                catch (const std::logic_error&) { parser_rejected = true; }
                VERIFY(parser_rejected);

                const std::string keyword = direction == H::ObjKind::MINIMIZE ? "(minimize " : "(maximize ";
                const auto pure = packed.toSmt2(OmtDialect::None);
                const auto z3 = packed.toSmt2(OmtDialect::Z3);
                const auto standard = packed.toSmt2(OmtDialect::SmtLib2025);
                const auto opti = packed.toSmt2(OmtDialect::OptiMathSAT);
                VERIFY(pure.find(keyword) == std::string::npos);
                VERIFY(z3.find(keyword) != std::string::npos);
                VERIFY(standard.find("(define-objective cost ") != std::string::npos);
                VERIFY(standard.find("(optimize-sat cost)") != std::string::npos);
                VERIFY(opti.find(keyword) != std::string::npos);
                VERIFY(opti.find("(set-option :produce-models true)") != std::string::npos);
                // A failure in the ordinary preamble, a packed assertion, or
                // the objective/footer must never yield a successful prefix.
                for (const auto limit : {std::size_t(0), pure.size() / 2, z3.size() - 1}) {
                    FailingBuffer buffer(limit);
                    std::ostream output(&buffer);
                    bool rejected = false;
                    try { packed.writeSmt2(output, OmtDialect::Z3); }
                    catch (const std::runtime_error&) { rejected = true; }
                    VERIFY(rejected);
                    VERIFY(!output);
                }

                // The counterpart is constructed independently as ordinary
                // typed HIR. Optional files permit external Z3 comparison of
                // the complete feasible relation and objective after this test.
                model.packed_linear_rows.reset();
                H::Constraint row;
                row.formula = H::mkOp(H::Op::LE,
                    {H::mkIdent(name, model.decls.front().sort), H::mkReal("3.5")});
                model.constraints.push_back(row);
                const auto expanded = SOMTParser::translate(model, options);
                VERIFY(expanded.ok());
                if (argc == 2) {
                    for (const auto& item : {
                            std::make_pair("packed", z3),
                            std::make_pair("expanded", expanded.toSmt2(OmtDialect::Z3))}) {
                        std::ofstream file(std::string(argv[1]) + "/case-" + std::to_string(case_number)
                                           + "-" + item.first + ".smt2");
                        file << item.second;
                        VERIFY(file.good());
                    }
                }
                ++case_number;
            }
        }
    }
    VERIFY(case_number == 8);
    return 0;
}
