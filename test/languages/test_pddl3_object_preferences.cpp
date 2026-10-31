#include "somtparser/languages/pddl_internal.h"
#include "somtparser/hir/typecheck.h"
#include "planning_public_pipeline.h"
#include "test_helpers.h"
#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>

struct Pddl3ObjectPreferenceCase {
    std::string name, domain, problem;
    unsigned horizon;
};

int main(int argc, char** argv) {
    const std::filesystem::path output = argc == 2 ? argv[1] : "";
    if (!output.empty()) { std::filesystem::create_directories(output); }
    const std::vector<Pddl3ObjectPreferenceCase> examples{
#include "pddl3_object_preference_cases.inc"
    };
    std::ofstream ledger;
    if (!output.empty()) { ledger.open(output / "pddl3-object-preference-controls.tsv"); }
    for (const auto& example : examples) {
        const auto translated = SomtPlanningTest::publicTranslation(example.domain,
            example.problem, example.name, example.horizon, true);
        SOMTParser::Uir::Diagnostics diagnostics;
        SOMTParser::Uir::TranslationReport report;
        const auto internal = SOMTParser::Lang::PddlInternal::buildClassicalEncoding(
            example.domain, example.problem, example.name, example.horizon, diagnostics, report);
        VERIFY(internal.model);
        VERIFY(SOMTParser::Uir::Hir::typeCheck(*internal.model, diagnostics));
        VERIFY(internal.model->objectives.size() == 1);
        if (!output.empty()) {
            translated.writeSmt2((output / (example.name + ".smt2")).string(), SOMTParser::Lower::OmtDialect::Z3);
            std::ofstream(output / (example.name + ".domain.pddl")) << example.domain;
            std::ofstream(output / (example.name + ".problem.pddl")) << example.problem;
            std::ofstream mapping(output / (example.name + ".tsv"));
            for (const auto& entry : internal.symbol_map) {
                mapping << entry.source << '\t' << entry.target << '\n';
            }
            std::ofstream choices(output / (example.name + ".choices.tsv"));
            for (const auto& choice : internal.projection.choices) {
                for (const auto& alternative : choice.alternatives) {
                    choices << choice.source_name << '\t' << alternative.label << '\t' << alternative.target_name << '\n';
                }
            }
            ledger << example.name << '\t' << example.horizon << '\n';
        }
    }
    std::cout << "PDDL3 object preference source controls: " << examples.size() << '\n';
    return 0;
}
