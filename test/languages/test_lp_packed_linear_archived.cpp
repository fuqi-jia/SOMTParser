#include "somtparser/languages/lp.h"
#include "somtparser/translation/translate.h"
#include "somtparser/hir/typecheck.h"
#include "test_helpers.h"

#include <string>

using namespace SOMTParser;
namespace H = Uir::Hir;

namespace {
constexpr std::size_t threshold = 65536;

Lang::ParseOutcome parse(const std::string& text, const std::string& file = "packed.lp") {
    Lang::SourceUnit source;
    source.main_path = file;
    source.inline_source = text;
    return Lang::mkLpLanguage()->parse(source, Lang::ParseOptions{});
}

std::string repeated(const std::string& term, std::size_t count) {
    std::string text;
    for (std::size_t i = 0; i < count; ++i) { text += " + " + term; }
    return text;
}

void valid(const Lang::ParseOutcome& parsed) {
    VERIFY(parsed.ok());
    Uir::Diagnostics diagnostics;
    VERIFY(H::typeCheck(*parsed.model, diagnostics));
    VERIFY(parsed.semantics.validate(diagnostics));
}
} // namespace

int main() {
    // Exercise the actual production threshold, including its ordinary side.
    for (const std::size_t width : {threshold - 1, threshold}) {
        auto parsed = parse("Minimize x\nSubject To\nr:" + repeated("x", width)
            + " <= 3\nBounds\nx free\nEnd\n");
        valid(parsed);
        VERIFY(bool(parsed.model->packed_linear_rows) == (width == threshold));
        if (width == threshold) {
            const auto& batch = parsed.model->packed_linear_rows->batches.front();
            VERIFY(parsed.model->constraints.empty());
            VERIFY(batch.rows.size() == 1 && batch.terms.size() == width);
            VERIFY(batch.rows.front().source_line == 3);
            for (const auto& term : batch.terms) { VERIFY(term.column == 0); }
        } else {
            VERIFY(parsed.model->constraints.size() == 1);
            VERIFY(parsed.model->constraints.front().formula->args.front()->args.size() == width);
        }
    }
    {
        // A real wide row, not many dummy constraints. Preserve source order,
        // duplicate terms, zeros and exact spelling normalization in storage.
        const std::string group = " + 9007199254740993 x - 9007199254740992 x"
            " + .125e1 i + 0 x";
        std::string row;
        for (std::size_t i = 0; i < threshold / 4; ++i) { row += group; }
        auto parsed = parse("Minimize x\nSubject To\nr: -2.5 <= " + row
            + " + 0.1 + 0.2 <= 7.25\nq: [ x ^ 2 ] / 3 <= 4\n"
              "Bounds\nx free\ni free\nGenerals\ni\nEnd\n", "wide.lp");
        valid(parsed);
        const auto& data = *parsed.model->packed_linear_rows;
        VERIFY(data.batches.size() == 1);
        const auto& batch = data.batches.front();
        VERIFY(batch.source_file == "wide.lp" && batch.rows.size() == 1);
        VERIFY(batch.terms.size() == threshold);
        VERIFY(batch.rows[0].relation == H::LinearRowRelation::RANGE);
        VERIFY(data.numbers[batch.rows[0].rhs] == "-2.8");
        VERIFY(data.numbers[batch.rows[0].upper] == "6.95");
        for (std::size_t n = 0; n < threshold; n += 4) {
            VERIFY(data.numbers[batch.terms[n].coefficient] == "9007199254740993");
            VERIFY(data.numbers[batch.terms[n + 1].coefficient] == "-9007199254740992");
            VERIFY(data.numbers[batch.terms[n + 2].coefficient] == "1.25");
            VERIFY(data.numbers[batch.terms[n + 3].coefficient] == "0");
            VERIFY(batch.terms[n].column == 0 && batch.terms[n + 2].column == 1);
        }
        VERIFY(parsed.model->decls[0].sort.kind == H::SortKind::REAL);
        VERIFY(parsed.model->decls[1].sort.kind == H::SortKind::INT);
        // The quadratic row retains its original expression and source line.
        VERIFY(parsed.model->constraints.size() == 1);
        VERIFY(parsed.model->constraints[0].loc.line == 4);
        VERIFY(parsed.model->constraints[0].formula->op == H::Op::LE);
        TranslateOptions options;
        options.omt_dialect = Lower::OmtDialect::Z3;
        auto translated = translate(*parsed.model, options);
        VERIFY(translated.ok() && translated.usesPackedSmtStream());
        VERIFY(translated.report().stats().num_constraints == 2);
        VERIFY(translated.objectiveCount() == 1);
    }
    {
        std::string source = "Minimize x\nSubject To\n";
        for (std::size_t n = 0; n < threshold; ++n) {
            source += "r" + std::to_string(n) + ": x <= 3\n";
        }
        source += "Bounds\nx free\nEnd\n";
        auto parsed = parse(source, "many.lp");
        valid(parsed);
        VERIFY(parsed.model->constraints.empty());
        VERIFY(parsed.model->packed_linear_rows->batches.size() == 16);
        std::size_t seen = 0;
        for (const auto& batch : parsed.model->packed_linear_rows->batches) {
            VERIFY(batch.rows.size() == 4096 && batch.terms.size() == 4096);
            for (const auto& row : batch.rows) {
                VERIFY(row.source_line == seen + 3 && row.end == row.begin + 1);
                ++seen;
            }
        }
        VERIFY(seen == threshold);
    }
    {
        auto parsed = parse("Maximize\n__somt_lp_objective_value2:" + repeated(".125 x - .25 i", threshold / 2)
            + " + 9007199254740993.125\nSubject To\nr: x + i <= 3\nBounds\n"
              "x free\ni free\n__somt_lp_objective_value free\n"
              "__somt_lp_objective_value1 free\nGenerals\ni\nEnd\n", "cost.lp");
        valid(parsed);
        const auto& value = parsed.model->decls.back();
        VERIFY(value.name == "__somt_lp_objective_value3" && value.auxiliary);
        VERIFY(value.sort.kind == H::SortKind::REAL && !value.lower_bound && !value.upper_bound);
        VERIFY(value.loc.file == "cost.lp" && value.loc.line == 2);
        VERIFY(parsed.model->objectives.front().kind == H::ObjKind::MAXIMIZE);
        VERIFY(parsed.model->objectives.front().term->kind == H::ExprKind::IDENT);
        const auto& data = *parsed.model->packed_linear_rows;
        const auto& definition = data.batches.back();
        VERIFY(definition.rows.size() == 1 && definition.terms.size() == threshold + 1);
        VERIFY(definition.rows[0].relation == H::LinearRowRelation::EQ);
        VERIFY(data.numbers[definition.rows[0].rhs] == "-9007199254740993.125");
        VERIFY(definition.terms.back().column == parsed.model->decls.size() - 1);
        VERIFY(data.numbers[definition.terms.back().coefficient] == "-1");
        const auto& contract = parsed.semantics.stages().front();
        VERIFY(contract.source_signature.symbols.size() == 4);
        VERIFY(contract.target_signature.symbols.size() == 5);
        VERIFY(contract.projection.observables.size() == 4);
        for (const auto& symbol : contract.source_signature.symbols) {
            VERIFY(symbol.name != value.name);
        }
    }
    {
        // Invalid source remains rejected at its source line before packing.
        auto parsed = parse("Minimize x\nSubject To\nr:" + repeated("x", threshold)
            + " <= 3\nbad: x <= nope\nEnd\n", "invalid.lp");
        VERIFY(!parsed.ok() && parsed.diagnostics.hasErrors());
        VERIFY(parsed.diagnostics.all().front().loc.line == 4);
        VERIFY(parsed.diagnostics.all().front().message.find("not a number") != std::string::npos);
    }
}
