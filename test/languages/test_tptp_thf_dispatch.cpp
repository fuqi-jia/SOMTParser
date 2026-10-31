// End-to-end frontend-to-HIR/SMT export check for the pinned THF0 case.
#include "somtparser/languages/tptp.h"
#include "somtparser/lowering/hir_to_parser.h"
#include "somtparser/frontend/parser.h"
#include "somtparser/translation/semantics.h"
#include "somtparser/hir/typecheck.h"
#include "test_helpers.h"

#include <fstream>
#include <iostream>
#include <string>

using namespace SOMTParser;

int main(int argc, char** argv) {
    VERIFY(argc == 1 || argc == 3);
    Lang::SourceUnit unit;
    if (argc == 3) {
        unit.main_path = argv[1];
    } else {
        unit.display_name = "thf-dispatch-smoke.p";
        unit.inline_source =
            "thf(type_u,type,(u:$tType)).\n"
            "thf(type_p,type,(p:u > $o)).\n"
            "thf(fact,axiom, ! [X:u] : (p @ X)).\n"
            "thf(goal_a,conjecture, ! [X:u] : (p @ X)).\n"
            "thf(goal_b,conjecture, ! [X:u] : (p @ X)).\n";
    }
    Lang::ParseOptions options;
    const auto language = Lang::mkTptpLanguage();
    Lang::ParseOutcome parsed = language->parse(unit, options);
    if (!parsed.ok()) {
        for (const auto& diagnostic : parsed.diagnostics.all()) {
            std::cerr << diagnostic.message << '\n';
        }
        return 2;
    }
    if (parsed.semantics.stages().size() != 1) {
        std::cerr << "unexpected semantic stage count: "
                  << parsed.semantics.stages().size() << '\n';
        for (const auto& diagnostic : parsed.diagnostics.all()) {
            std::cerr << diagnostic.message << '\n';
        }
        return 3;
    }
    Uir::Diagnostics contract_diagnostics;
    const auto spec = Uir::Sem::sourceSemanticSpec("tptp");
    VERIFY(Uir::Sem::validateSourceContract(
        spec, parsed.semantics.stages().front(), contract_diagnostics));
    VERIFY(parsed.semantics.validate(contract_diagnostics));
    const auto& contract = parsed.semantics.stages().front();
    VERIFY(contract.decision.source == Uir::Sem::DecisionKind::VALIDITY);
    VERIFY(contract.decision.target == Uir::Sem::DecisionKind::SATISFIABILITY);
    VERIFY(contract.decision.polarity == Uir::Sem::VerdictPolarity::INVERT);
    VERIFY(parsed.report.choices().size() == 1);

    Uir::Diagnostics type_diagnostics;
    VERIFY(Uir::Hir::typeCheck(*parsed.model, type_diagnostics));

    ParserPtr parser = newParser();
    Lower::HirToParser lowerer(parser);
    Uir::TranslationReport report;
    Uir::Diagnostics lower_diagnostics;
    VERIFY(lowerer.lower(*parsed.model, report, lower_diagnostics));
    // No check-sat is emitted: Z3's independent invocation validates every
    // declaration/assertion in the exported module without spending time on
    // the theorem search.
    const std::string smt = parser->dumpSMT2Module();
    VERIFY(!smt.empty());
    if (argc == 3) {
        std::ofstream out(argv[2], std::ios::binary | std::ios::trunc);
        VERIFY(static_cast<bool>(out));
        out << smt;
        out.flush();
        VERIFY(static_cast<bool>(out));
    }

    // Unsupported arithmetic base types must fail at the THF adapter with an
    // explicit unsupported-construct diagnostic, not fall through to the FOL
    // parser or return a partially published model.
    Lang::SourceUnit unsupported_unit;
    unsupported_unit.display_name = "unsupported-thf-arithmetic.p";
    unsupported_unit.inline_source = "thf(type_n,type,(n:$int)).\n";
    const Lang::ParseOutcome unsupported = language->parse(unsupported_unit, options);
    VERIFY(!unsupported.ok());
    bool explicitly_refused = false;
    for (const auto& diagnostic : unsupported.diagnostics.all()) {
        explicitly_refused = explicitly_refused
            || diagnostic.code == Uir::ErrorCode::E_UNSUPPORTED_CONSTRUCT;
    }
    VERIFY(explicitly_refused);

    // Dispatch must scan beyond preceding records. An include before the first
    // THF formula is still routed to the THF reader; a missing dependency is
    // an error, since silently dropping it would change the theorem.
    Lang::SourceUnit mixed_unit;
    mixed_unit.display_name = "unsupported-thf-include.p";
    mixed_unit.inline_source =
        "include('missing-axioms.p').\n"
        "thf(goal,conjecture,$true).\n";
    const Lang::ParseOutcome mixed = language->parse(mixed_unit, options);
    VERIFY(!mixed.ok());
    VERIFY(mixed.diagnostics.firstErrorCode() == Uir::ErrorCode::E_IO);
    bool include_refused = false;
    for (const auto& diagnostic : mixed.diagnostics.all()) {
        include_refused = include_refused
            || diagnostic.message.find("cannot resolve include") != std::string::npos;
    }
    VERIFY(include_refused);

    // Dispatch an include-only wrapper by its selected statements. The same
    // two-pass signature is shared across all source files.
    Lang::SourceUnit wrapper;
    wrapper.display_name = "languages/tptp/instances/ok/wrapper.p";
    wrapper.inline_source = "include('thf-includes.p').\n";
    auto included = language->parse(wrapper, options);
    VERIFY(included.ok());
    VERIFY(included.report.choices().size() == 1);
    VERIFY(included.semantics.stages().front().decision.source ==
           Uir::Sem::DecisionKind::VALIDITY);
    Uir::Diagnostics included_types;
    VERIFY(Uir::Hir::typeCheck(*included.model, included_types));
    wrapper.inline_source = "include('support/thf-include-leaf.ax',[]).\n";
    const auto empty_selection = language->parse(wrapper, options);
    VERIFY(empty_selection.ok());
    return 0;
}
