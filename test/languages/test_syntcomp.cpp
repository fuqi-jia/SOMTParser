#include "somtparser/frontend/parser.h"
#include "somtparser/languages/register_all.h"
#include "somtparser/translation/translate.h"

#include <cassert>
#include <iostream>
#include <string>

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

bool has(const std::string& haystack, const std::string& needle) {
    return haystack.find(needle) != std::string::npos;
}

Translation run(const std::string& path) {
    Lang::SourceUnit unit;
    unit.main_path = path;
    unit.display_name = path;
    TranslateOptions options;
    options.language_id = "syntcomp";
    return translate(unit, options);
}

} // namespace

int main() {
    std::cout << "======= SYNTCOMP invariant games =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    Lang::Language* language = Lang::LanguageRegistry::instance().byId("syntcomp");
    assert(language != nullptr);
    assert(!has(language->displayName(), "pending"));

    // SyFCo's MAIN parser discards empty semicolon-delimited items. This
    // official finite benchmark has an extra empty item after its INPUTS.
    {
        const std::string with_empty_item =
            "INFO { TITLE: \"uright06\" DESCRIPTION: \"Patterns/Uright\" "
            "SEMANTICS: Finite,Moore TARGET: Moore } "
            "MAIN { INPUTS { p1; p3; p2; ; } OUTPUTS { p6; p5; p4; } "
            "GUARANTEES { p1 U (p2 U (p3 U (p4 U (p5 U p6)))); } }";
        const std::string without_empty_item =
            "INFO { TITLE: \"uright06\" DESCRIPTION: \"Patterns/Uright\" "
            "SEMANTICS: Finite,Moore TARGET: Moore } "
            "MAIN { INPUTS { p1; p3; p2; } OUTPUTS { p6; p5; p4; } "
            "GUARANTEES { p1 U (p2 U (p3 U (p4 U (p5 U p6)))); } }";
        const auto translate_inline = [](const std::string& source) {
            Lang::SourceUnit unit;
            unit.main_path = "uright06.tlsf";
            unit.inline_source = source;
            TranslateOptions options;
            options.language_id = "syntcomp";
            return translate(unit, options);
        };
        const Translation original = translate_inline(with_empty_item);
        const Translation normalized = translate_inline(without_empty_item);
        assert(original.ok());
        assert(normalized.ok());
        assert(original.toSmt2() == normalized.toSmt2());
    }

    // Empty items may be skipped; malformed signal separators may not.
    {
        Lang::SourceUnit unit;
        unit.main_path = "malformed-signal-item.tlsf";
        unit.inline_source =
            "INFO { SEMANTICS: Mealy TARGET: Mealy } "
            "MAIN { INPUTS { r; ?; } OUTPUTS { g; } "
            "GUARANTEES { G (r -> g); } }";
        TranslateOptions options;
        options.language_id = "syntcomp";
        const Translation translation = translate(unit, options);
        assert(!translation.ok());
        assert(translation.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
    }

    // Mealy responses are indexed by the current environment valuation.
    {
        const Translation translation = run(
            "languages/syntcomp/instances/ok/mealy-copy.tlsf");
        assert(translation.ok());
        const std::string smt = translation.toSmt2();
        assert(has(smt, "__somt_syntcomp_output_0_env_0"));
        assert(has(smt, "__somt_syntcomp_output_0_env_1"));
        assert(has(smt, "(assert (not __somt_syntcomp_output_0_env_0))"));
        assert(has(smt, "(assert __somt_syntcomp_output_0_env_1)"));
        ParserPtr parser = newParser();
        assert(parser->parseStr(smt));

        const auto& stages = translation.semantics().stages();
        assert(stages.size() == 2);
        assert(stages.front().id == "syntcomp-to-typed-relational-core-v1");
        assert(stages.front().source.id == "syntcomp");
        assert(stages.front().decision.source
               == Sem::DecisionKind::REACTIVE_REALIZABILITY);
        assert(stages.front().source_signature.symbols.size() == 2);
        assert(stages.front().symbol_map.size() == 2);
        assert(stages.front().projection.observables.size() == 2);
        Diagnostics diagnostics;
        assert(translation.semantics().validate(diagnostics));

        Sem::Assignment target{
            {"__somt_syntcomp_output_0_env_0", "false"},
            {"__somt_syntcomp_output_0_env_1", "true"},
        };
        Sem::Assignment source;
        assert(translation.semantics().project(target, source, diagnostics));
        assert(source.at("controller[grant](request=false)") == "false");
        assert(source.at("controller[grant](request=true)") == "true");
    }

    // Moore outputs cannot observe the current input, so both environment
    // valuations constrain the same controller coordinate.
    {
        const Translation realizable = run(
            "languages/syntcomp/instances/ok/moore-constant.tlsf");
        const Translation unrealizable = run(
            "languages/syntcomp/instances/ok/moore-cannot-copy.tlsf");
        assert(realizable.ok() && unrealizable.ok());
        assert(realizable.semantics().stages().front().projection.observables.size() == 1);
        assert(has(unrealizable.toSmt2(),
                   "(assert (not __somt_syntcomp_output_0_env_0))"));
        assert(has(unrealizable.toSmt2(),
                   "(assert __somt_syntcomp_output_0_env_0)"));
    }

    // Input-only invariant assumptions restrict environment valuations. An
    // assumption violation makes that valuation vacuous, not a controller move.
    {
        const Translation translation = run(
            "languages/syntcomp/instances/ok/assumption.tlsf");
        assert(translation.ok());
        assert(has(translation.toSmt2(), "(assert true)"));
    }

    // The full truth table is complete for this stateless invariant fragment;
    // no play/strategy bound is claimed or needed.
    {
        const Translation translation = run(
            "languages/syntcomp/instances/ok/mealy-copy.tlsf");
        assert(translation.report().fidelity().sound && translation.report().fidelity().complete && translation.report().fidelity().preserves_optimum && translation.report().fidelity().bounds.empty() && translation.report().fidelity().count_status == CountStatus::UNASSESSED);
        assert(translation.report().fidelity().bounds.empty());
        const Sem::SourceSemanticSpec spec = Sem::sourceSemanticSpec("syntcomp");
        assert(spec.smt_embedding == Sem::SmtEmbeddingKind::DIRECT_REDUCTION);
        assert(spec.required_bounds.empty());
    }

    // General LTL is not replaced by bounded trace checking.
    {
        const Translation translation = run(
            "languages/syntcomp/instances/reject/arbiter.tlsf");
        assert(!translation.ok());
        assert(translation.diagnostics().firstErrorCode()
               == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        assert(has(translation.diagnostics().all()[0].message,
                   "LTL-to-automaton/parity-game"));
        assert(has(translation.diagnostics().all()[0].message,
                   "not reactive realizability"));
    }

    // Output-dependent assumptions use the exact infinite contract monitor.
    {
        Lang::SourceUnit unit;
        unit.main_path = "bad-assumption.tlsf";
        unit.inline_source =
            "INFO { SEMANTICS: Mealy TARGET: Mealy } "
            "MAIN { INPUTS { r; } OUTPUTS { g; } "
            "ASSUMPTIONS { G g; } GUARANTEES { G r; } }";
        TranslateOptions options;
        options.language_id = "syntcomp";
        const Translation translation = translate(unit, options);
        assert(translation.ok());
        assert(has(translation.toSmt2(), "__somt_syntcomp_buchi_"));
    }

    // TARGET is required semantic data; silently defaulting it would leave the
    // Mealy/Moore causality of the requested implementation ambiguous.
    {
        Lang::SourceUnit unit;
        unit.main_path = "missing-target.tlsf";
        unit.inline_source =
            "INFO { SEMANTICS: Mealy } MAIN { INPUTS { r; } OUTPUTS { g; } "
            "GUARANTEE { G (r -> g); } }";
        TranslateOptions options;
        options.language_id = "syntcomp";
        const Translation translation = translate(unit, options);
        assert(!translation.ok());
        assert(translation.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
        assert(has(translation.diagnostics().all()[0].message, "TARGET"));
    }

    const Lang::OpCoverage& coverage = language->coverage();
    assert(coverage.supported == 1 && coverage.total == 3);
    assert(coverage.missing.size() == coverage.total - coverage.supported);

    std::cout << "All SYNTCOMP tests passed." << std::endl;
    return 0;
}
