#include "somtparser/languages/mps.h"
#include "somtparser/hir/typecheck.h"
#include "test_helpers.h"

#include <string>

using namespace SOMTParser;
namespace H = Uir::Hir;

int main() {
    Lang::SourceUnit source;
    source.main_path = "wide-objective.mps";
    source.inline_source = "NAME objective\nOBJNAME cost\nROWS\n L before\n N free\n N cost\n G after\n"
        "COLUMNS\n marker0 'MARKER' 'INTORG'\n";
    constexpr std::size_t entries = 65536;
    for (std::size_t i = 0; i < entries; ++i) {
        source.inline_source += i % 2 == 0 ? " x cost 0.125\n" : " y cost -0.25\n";
    }
    source.inline_source += " x before 1\n y after 1\n x free 999\n"
        " marker1 'MARKER' 'INTEND'\n __somt_mps_objective_value cost 0\n"
        " __somt_mps_objective_value1 cost 0\nRHS\n rhs cost -1.25\n"
        " rhs before 3\n rhs after -2\nBOUNDS\n FR bounds x\n FR bounds y\n"
        " FR bounds __somt_mps_objective_value\n FR bounds __somt_mps_objective_value1\nENDATA\n";
    const auto parsed = Lang::mkMpsLanguage()->parse(source, Lang::ParseOptions{});
    VERIFY(parsed.ok());
    VERIFY(parsed.model->packed_linear_rows);
    VERIFY(parsed.model->decls.size() == 5);
    VERIFY(parsed.model->decls[0].sort.kind == H::SortKind::INT);
    VERIFY(parsed.model->decls[1].sort.kind == H::SortKind::INT);
    const auto& value = parsed.model->decls.back();
    VERIFY(value.name == "__somt_mps_objective_value2");
    VERIFY(value.auxiliary && value.sort.kind == H::SortKind::REAL);
    VERIFY(!value.lower_bound && !value.upper_bound);
    VERIFY(parsed.model->objectives.size() == 1);
    const auto& objective = parsed.model->objectives.front();
    VERIFY(objective.kind == H::ObjKind::MINIMIZE && objective.name == "cost");
    VERIFY(objective.term->kind == H::ExprKind::IDENT && objective.term->name == value.name);
    VERIFY(objective.term->sort.kind == H::SortKind::REAL && objective.term->args.empty());
    // The objective sits between matrix rows in the source. Its dedicated
    // batch must not absorb/duplicate either neighboring row or the free N row.
    const auto& data = *parsed.model->packed_linear_rows;
    VERIFY(data.batches.size() == 3);
    for (const auto& batch : data.batches) { VERIFY(batch.rows.size() == 1); }
    VERIFY(data.batches[0].rows[0].relation == H::LinearRowRelation::LE);
    VERIFY(data.batches[2].rows[0].relation == H::LinearRowRelation::GE);
    const auto& definition = data.batches[1];
    VERIFY(definition.terms.size() == entries + 3); // two explicit zero columns plus helper
    VERIFY(definition.rows[0].relation == H::LinearRowRelation::EQ);
    VERIFY(data.numbers[definition.rows[0].rhs] == "-1.25");
    VERIFY(definition.terms.back().column == 4);
    VERIFY(data.numbers[definition.terms.back().coefficient] == "-1");
    VERIFY(definition.rows[0].source_line == 6);
    VERIFY(value.loc.line == 6 && value.loc.file == source.main_path);
    for (const auto& declaration : parsed.model->decls) {
        if (declaration.name != value.name) { VERIFY(!declaration.auxiliary); }
    }
    const auto& contract = parsed.semantics.stages().front();
    VERIFY(contract.source_signature.symbols.size() == 4);
    VERIFY(contract.target_signature.symbols.size() == 5);
    VERIFY(contract.projection.observables.size() == 4);
    for (const auto& symbol : contract.source_signature.symbols) { VERIFY(symbol.name != value.name); }
    for (const auto& observable : contract.projection.observables) {
        VERIFY(observable.source_name != value.name && observable.target_name != value.name);
    }
    Uir::Diagnostics diagnostics;
    VERIFY(H::typeCheck(*parsed.model, diagnostics));
    VERIFY(parsed.semantics.validate(diagnostics));
}
