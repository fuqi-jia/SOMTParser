#include "somtparser/languages/lp.h"
#include "somtparser/hir/typecheck.h"
#include "test_helpers.h"

#include <cstdint>
#include <filesystem>
#include <fstream>
#include <string>

using namespace SOMTParser;
namespace H = Uir::Hir;

int main() {
    constexpr std::size_t terms = 65536;
    Lang::SourceUnit unit;
    unit.main_path = "wide-linear.lp";
    unit.inline_source = "Maximize\n cost: 0.5 x + 1.25\nSubject To\n row: -2.5 <=";
    for (std::size_t i = 0; i < terms; ++i) {
        unit.inline_source += i % 2 == 0 ? " + 0.125 x" : " - 0.25 y";
    }
    unit.inline_source += " + 0.25 - 0.5 <= 7.5\n"
        " q: [ x^2 ] / 3 + y <= 2\nBounds\n x free\n y free\nGenerals\n y\nEnd";
    auto parsed = Lang::mkLpLanguage()->parse(unit, Lang::ParseOptions{});
    VERIFY(parsed.ok());
    VERIFY(parsed.model->decls.size() == 2);
    VERIFY(parsed.model->decls[1].sort.kind == H::SortKind::INT);
    VERIFY(parsed.model->packed_linear_rows);
    VERIFY(parsed.model->constraints.size() == 1); // the quadratic row stays HIR
    const auto& packed = *parsed.model->packed_linear_rows;
    VERIFY(packed.batches.size() == 1);
    const auto& batch = packed.batches.front();
    VERIFY(batch.rows.size() == 1 && batch.terms.size() == terms);
    const auto& row = batch.rows.front();
    VERIFY(row.relation == H::LinearRowRelation::RANGE);
    VERIFY(packed.numbers[row.rhs] == "-2.25");
    VERIFY(packed.numbers[row.upper] == "7.75");
    VERIFY(row.begin == 0 && row.end == terms && row.source_line == 4);
    for (std::size_t i = 0; i < terms; ++i) {
        VERIFY(batch.terms[i].column == i % 2);
        VERIFY(packed.numbers[batch.terms[i].coefficient] == (i % 2 == 0 ? "0.125" : "-0.25"));
    }
    VERIFY(parsed.model->objectives.size() == 1);
    VERIFY(parsed.model->objectives.front().kind == H::ObjKind::MAXIMIZE);
    Uir::Diagnostics diagnostics;
    VERIFY(H::typeCheck(*parsed.model, diagnostics));
    VERIFY(parsed.semantics.validate(diagnostics));

    // The file path follows the same parser, including an EOF without newline.
    const auto path = std::filesystem::temp_directory_path()
        / ("somt-lp-packed-" + std::to_string(reinterpret_cast<std::uintptr_t>(&unit)) + ".lp");
    { std::ofstream output(path); output << unit.inline_source; VERIFY(output.good()); }
    Lang::SourceUnit from_file;
    from_file.main_path = path.string();
    const auto disk = Lang::mkLpLanguage()->parse(from_file, Lang::ParseOptions{});
    std::filesystem::remove(path);
    VERIFY(disk.ok());
    VERIFY(disk.model->packed_linear_rows->batches.front().terms.size() == terms);
    VERIFY(disk.model->packed_linear_rows->numbers == packed.numbers);
    VERIFY(disk.model->constraints.size() == parsed.model->constraints.size());

    // A wide objective's Real value is uniquely defined and private. Its
    // signed offset and every duplicate term remain in the equality.
    unit.inline_source = "Minimize\n cost:\n";
    for (std::size_t i = 0; i < terms; ++i) { unit.inline_source += " + 0.125 x\n"; }
    unit.inline_source += " - 1.25 + 0 __somt_lp_objective_value + 0 __somt_lp_objective_value1\n"
        "Subject To\n r: x >= -2\nBounds\n x free\nGenerals\n x\nEnd\n";
    const auto objective = Lang::mkLpLanguage()->parse(unit, Lang::ParseOptions{});
    VERIFY(objective.ok());
    VERIFY(objective.model->packed_linear_rows);
    const auto& value = objective.model->decls.back();
    VERIFY(value.name == "__somt_lp_objective_value2");
    VERIFY(value.auxiliary && value.sort.kind == H::SortKind::REAL);
    VERIFY(!value.lower_bound && !value.upper_bound);
    VERIFY(objective.model->decls[0].sort.kind == H::SortKind::INT);
    const auto& data = *objective.model->packed_linear_rows;
    VERIFY(data.batches.size() == 2);
    VERIFY(data.batches[0].rows.size() == 1);
    const auto& definition = data.batches.back();
    VERIFY(definition.rows.size() == 1 && definition.terms.size() == terms + 3);
    VERIFY(definition.rows.front().relation == H::LinearRowRelation::EQ);
    VERIFY(data.numbers[definition.rows.front().rhs] == "1.25");
    VERIFY(definition.terms.back().column == 3);
    VERIFY(data.numbers[definition.terms.back().coefficient] == "-1");
    VERIFY(objective.model->objectives.front().term->name == value.name);
    const auto& contract = objective.semantics.stages().front();
    VERIFY(contract.source_signature.symbols.size() == 3);
    VERIFY(contract.target_signature.symbols.size() == 4);
    VERIFY(contract.projection.observables.size() == 3);
    for (const auto& observable : contract.projection.observables) {
        VERIFY(observable.source_name != value.name && observable.target_name != value.name);
    }
    VERIFY(H::typeCheck(*objective.model, diagnostics));
    VERIFY(objective.semantics.validate(diagnostics));

    // Packing spans batches without losing a row around an ordinary quadratic
    // constraint. Decimal exponents, signed zero and a >2^53 endpoint stay exact.
    unit.inline_source = "Minimize\n cost: x\nSubject To\n";
    for (std::size_t i = 0; i < 4097; ++i) {
        unit.inline_source += " r" + std::to_string(i) + ":";
        for (std::size_t j = 0; j < 8; ++j) {
            unit.inline_source += " + 0.0005e3 x - 0.000e2 x";
        }
        unit.inline_source += " + 0.001e3 <= 9007199254740993.25\n";
        if (i == 100) { unit.inline_source += " quadratic: [ x^2 ] <= 4\n"; }
    }
    unit.inline_source += "Bounds\n x free\nEnd\n";
    const auto batches = Lang::mkLpLanguage()->parse(unit, Lang::ParseOptions{});
    VERIFY(batches.ok());
    VERIFY(batches.model->constraints.size() == 1);
    const auto& many = *batches.model->packed_linear_rows;
    VERIFY(many.batches.size() == 2);
    VERIFY(many.batches[0].rows.size() == 4096);
    VERIFY(many.batches[1].rows.size() == 1);
    std::size_t rows = 0;
    for (const auto& block : many.batches) {
        VERIFY(block.terms.size() == block.rows.size() * 16);
        for (const auto& item : block.rows) {
            VERIFY(item.end - item.begin == 16);
            VERIFY(many.numbers[item.rhs] == "9007199254740992.25");
            for (auto t = item.begin; t < item.end; ++t) {
                VERIFY(block.terms[t].column == 0);
                VERIFY(many.numbers[block.terms[t].coefficient] == (t % 2 == 0 ? "0.5" : "0"));
            }
            ++rows;
        }
    }
    VERIFY(rows == 4097);
    VERIFY(H::typeCheck(*batches.model, diagnostics));
    VERIFY(batches.semantics.validate(diagnostics));
}
