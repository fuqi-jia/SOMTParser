#include "somtparser/languages/mps.h"
#include "somtparser/hir/packed_linear_io.h"
#include "somtparser/hir/typecheck.h"
#include "somtparser/translation/translate.h"
#include "somtparser/translation/pass.h"
#include "test_helpers.h"

#include <functional>
#include <limits>
#include <sstream>
#include <string>

using namespace SOMTParser;
namespace H = Uir::Hir;

namespace {
class UnawarePass final : public Uir::Pass {
public:
    std::string id() const override { return "unaware"; }
    Uir::PassTraits traits() const override { return {}; }
    bool run(H::ConstraintModel&, Uir::LowerContext&) override { ran = true; return true; }
    bool ran = false;
};

H::ConstraintModel smallModel() {
    H::ConstraintModel model;
    H::VarDecl x; x.name = "x"; x.sort = H::Sort::real(); model.decls.push_back(x);
    H::VarDecl y; y.name = "y"; y.sort = H::Sort::integer(); model.decls.push_back(y);
    auto data = std::make_shared<H::PackedLinearRows>();
    data->numbers = {"0", "1", "-1", "1.25", "9007199254740993", "-2.5", "2"};
    H::PackedLinearRowBatch batch;
    batch.source_file = "small.mps";
    batch.terms = {{0, 1}, {1, 2}, {0, 4}, {0, 1}, {1, 1}};
    batch.rows = {
        {0, 2, 3, 0, 4, H::LinearRowRelation::LE},
        {2, 3, 4, 0, 5, H::LinearRowRelation::EQ},
        {3, 5, 5, 6, 6, H::LinearRowRelation::RANGE},
        {5, 5, 0, 0, 7, H::LinearRowRelation::GE},
    };
    data->batches.push_back(std::move(batch));
    model.packed_linear_rows = std::move(data);
    return model;
}

void rejects(const std::function<void(H::PackedLinearRows&, H::ConstraintModel&)>& change) {
    auto model = smallModel();
    auto data = std::make_shared<H::PackedLinearRows>(*model.packed_linear_rows);
    change(*data, model);
    model.packed_linear_rows = std::move(data);
    Uir::Diagnostics diagnostics;
    VERIFY(!H::typeCheck(model, diagnostics));
    VERIFY(diagnostics.hasErrors());
}
} // namespace

int main() {
    auto model = smallModel();
    Uir::Diagnostics diagnostics;
    VERIFY(H::typeCheck(model, diagnostics));
    auto snapshot = model;
    VERIFY(snapshot.packed_linear_rows == model.packed_linear_rows);
    std::ostringstream raw;
    VERIFY(H::writePackedLinearRowsSmt2(model, {"x", "y"}, raw, diagnostics));
    VERIFY(raw.str().find("9007199254740993.0") != std::string::npos);
    VERIFY(raw.str().find("(and (<= (- 2.5) (+ x y)) (<= (+ x y) 2.0))") != std::string::npos);
    VERIFY(raw.str().find("(assert (>= 0.0 0.0))") != std::string::npos);
    TranslateOptions opts; opts.omt_dialect = Lower::OmtDialect::Z3;
    auto translated = translate(model, opts);
    VERIFY(translated.ok());
    VERIFY(translated.usesPackedSmtStream());
    VERIFY(!translated.hasParser());
    VERIFY(translated.report().stats().num_constraints == 4);
    VERIFY(model.packed_linear_rows == snapshot.packed_linear_rows);
    VERIFY(model.packed_linear_rows->batches.front().terms.size() == 5);
    bool no_partial_parser = false;
    try { (void)translated.parser(); } catch (const std::logic_error&) { no_partial_parser = true; }
    VERIFY(no_partial_parser);

    // A pass written for expression-tree HIR must explicitly opt in before it
    // can process a model whose hard constraints also live in packed storage.
    Uir::PassRegistry registry;
    auto unaware = std::make_shared<UnawarePass>();
    registry.add(unaware);
    const auto profile = Uir::EncodingProfile::make("test-unaware",
        {{"unaware", {}}}, Uir::Fidelity::exact());
    Uir::Diagnostics pass_diagnostics;
    Uir::TranslationReport pass_report;
    VERIFY(!Uir::PassManager::run(model, *profile, registry, pass_report, pass_diagnostics));
    VERIFY(!unaware->ran);
    VERIFY(pass_diagnostics.hasErrors());
    VERIFY(pass_diagnostics.all().front().code == Uir::ErrorCode::E_PASS_PIPELINE);
    auto partial_parser = newParser();
    Lower::HirToParser direct(partial_parser);
    Uir::Diagnostics direct_diagnostics;
    Uir::TranslationReport direct_report;
    VERIFY(!direct.lower(model, direct_report, direct_diagnostics));
    VERIFY(direct_diagnostics.hasErrors());
    VERIFY(direct_diagnostics.all().front().code == Uir::ErrorCode::E_UNSUPPORTED_CONSTRUCT);

    rejects([](auto& data, auto&) { data.batches[0].rows[1].begin = 1; });
    rejects([](auto& data, auto&) { data.batches[0].rows[0].end = 100; });
    rejects([](auto& data, auto&) { data.batches[0].terms.push_back({0, 1}); });
    rejects([](auto& data, auto&) { data.batches[0].terms[0].column = 2; });
    rejects([](auto& data, auto&) { data.batches[0].terms[0].coefficient = 99; });
    rejects([](auto& data, auto&) { data.batches[0].rows[0].rhs = 99; });
    rejects([](auto& data, auto&) { data.batches[0].rows[2].upper = 99; });
    rejects([](auto& data, auto&) { data.batches[0].rows[0].source_line = 0; });
    rejects([](auto& data, auto&) { data.batches[0].rows[0].source_line = std::numeric_limits<std::uint32_t>::max(); });
    rejects([](auto& data, auto&) { data.batches[0].rows[0].relation = static_cast<H::LinearRowRelation>(99); });
    rejects([](auto&, auto& bad) { bad.decls[0].sort = H::Sort::boolean(); });
    for (const std::string value : {"", "+1", "01", "-0", "1.0", "1e3", "nan", "1/3", "1."}) {
        rejects([&](auto& data, auto&) { data.numbers[0] = value; });
    }

    // Reach the production threshold naturally; no test-only parser mode.
    Lang::SourceUnit source;
    source.main_path = "large.mps";
    source.inline_source = "NAME large\nOBJNAME objective\nROWS\n N free\n N objective\n";
    constexpr std::size_t rows = 65536;
    for (std::size_t i = 0; i < rows; ++i) {
        const char relation = i == 1 || i == 5 ? 'G' : i == 2 || i == 3 || i == 6 ? 'E' : 'L';
        source.inline_source += std::string(" ") + relation + " r" + std::to_string(i) + "\n";
    }
    source.inline_source += "COLUMNS\n x objective 1.25\n";
    for (std::size_t i = 0; i < rows; ++i) {
        source.inline_source += " x r" + std::to_string(i) + " 1\n";
    }
    source.inline_source += " i objective -1\n s objective 0\nRHS\n rhs objective 2.5\n"
        " rhs r0 10\n rhs r1 10\n rhs r2 10\n rhs r3 10\n rhs r6 9007199254740993\n"
        "RANGES\n range r0 2\n range r1 -2\n range r2 2\n range r3 -2\n"
        "BOUNDS\n FR bound x\n BV bound i\n LO bound s 2\n SC bound s 10\nENDATA\n";
    auto parsed = Lang::mkMpsLanguage()->parse(source, Lang::ParseOptions{});
    VERIFY(parsed.ok());
    VERIFY(parsed.model->packed_linear_rows);
    VERIFY(parsed.model->constraints.size() == 1); // semicontinuous domain
    VERIFY(parsed.model->constraints.front().formula->op == H::Op::OR);
    VERIFY(parsed.model->decls[1].sort.kind == H::SortKind::INT);
    VERIFY(parsed.model->decls[1].lower_bound && parsed.model->decls[1].upper_bound);
    VERIFY(!parsed.model->decls[0].lower_bound && !parsed.model->decls[0].upper_bound);
    VERIFY(parsed.model->objectives.size() == 1);
    VERIFY(parsed.model->objectives.front().name == "objective");
    VERIFY(parsed.model->objectives.front().term->op == H::Op::SUB);
    const auto& storage = *parsed.model->packed_linear_rows;
    std::size_t count = 0;
    for (const auto& batch : storage.batches) {
        VERIFY(batch.source_file == "large.mps");
        for (const auto& row : batch.rows) {
            VERIFY(row.source_line == count + 6);
            VERIFY(row.end == row.begin + 1);
            ++count;
        }
    }
    VERIFY(count == rows);
    const auto& first = storage.batches.front().rows;
    VERIFY(storage.numbers[first[0].rhs] == "8" && storage.numbers[first[0].upper] == "10");
    VERIFY(storage.numbers[first[1].rhs] == "10" && storage.numbers[first[1].upper] == "12");
    VERIFY(storage.numbers[first[2].rhs] == "10" && storage.numbers[first[2].upper] == "12");
    VERIFY(storage.numbers[first[3].rhs] == "8" && storage.numbers[first[3].upper] == "10");
    VERIFY(storage.numbers[first[4].rhs] == "0" && first[4].relation == H::LinearRowRelation::LE);
    VERIFY(storage.numbers[first[5].rhs] == "0" && first[5].relation == H::LinearRowRelation::GE);
    VERIFY(storage.numbers[first[6].rhs] == "9007199254740993");
    Uir::Diagnostics large_diagnostics;
    VERIFY(H::typeCheck(*parsed.model, large_diagnostics));
    auto large = translate(*parsed.model, opts);
    VERIFY(large.ok());
    VERIFY(large.report().stats().num_constraints == rows + 1);
    VERIFY(large.objectiveCount() == 1);
}
