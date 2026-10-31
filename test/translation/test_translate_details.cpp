#include "somtparser/translation/translate.h"
#include "test_helpers.h"

using namespace SOMTParser;

int main() {
    Uir::TranslationReport full, light;
    light.setDetailsEnabled(false);
    const Uir::EncodingChoice choice{"test", "bool", "native", Uir::Fidelity::exact(), "validated"};
    full.addChoice(choice); light.addChoice(choice);
    full.beginPhase(); light.beginPhase();
    full.addChoice(choice); light.addChoice(choice);
    VERIFY(full.choices().size() == 2);
    VERIFY(light.choices().empty());
    VERIFY(full.phaseFidelity().sound == light.phaseFidelity().sound);
    VERIFY(full.phaseFidelity().count_status == light.phaseFidelity().count_status);

    Uir::Hir::ConstraintModel model;
    TranslateOptions options;
    options.omt_dialect = Lower::OmtDialect::Z3;
    const auto detailed = translate(model, options);
    options.details = false;
    const auto summary = translate(model, options);
    VERIFY(detailed.exitCode() == summary.exitCode());
    VERIFY(detailed.smt2() == summary.smt2());
    VERIFY(detailed.diagnosticText() == summary.diagnosticText());
    VERIFY(!summary.hasDetails());
    VERIFY(!summary.hasParser());
    bool rejected = false;
    try { (void)summary.report(); } catch (const std::logic_error&) { rejected = true; }
    VERIFY(rejected);
    rejected = false;
    try { (void)summary.parser(); } catch (const std::logic_error&) { rejected = true; }
    VERIFY(rejected);
}
