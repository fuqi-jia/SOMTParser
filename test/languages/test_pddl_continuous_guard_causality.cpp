#include "somtparser/languages/pddl_internal.h"
#include "planning_public_pipeline.h"
#include "test_helpers.h"

#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>

struct ContinuousGuardCase {
    std::string name, domain, problem;
    bool accepted;
};
#include "pddl_continuous_guard_causality_cases.inc"

int main(int argc, char** argv) {
    VERIFY(argc == 1 || argc == 2);
    const std::filesystem::path output = argc == 2 ? argv[1] : "";
    if (!output.empty()) { std::filesystem::create_directories(output); }
    for (const auto& example : cases) {
        auto translated = SomtPlanningTest::publicTranslation(
            example.domain, example.problem, example.name, 1, example.accepted);
        SOMTParser::Uir::Diagnostics diagnostics;
        SOMTParser::Uir::TranslationReport report;
        const auto internal = SOMTParser::Lang::PddlInternal::buildClassicalEncoding(
            example.domain, example.problem, example.name, 1, diagnostics, report);
        VERIFY(static_cast<bool>(internal.model) == example.accepted);
        if (!example.accepted) {
            // The BNF is permissive. This is a causal well-formedness error,
            // not a missing continuous numerical integration algorithm.
            const SOMTParser::Uir::Diagnostics* messageSets[] = {
                &diagnostics, &translated.diagnostics()};
            for (const auto* messages : messageSets) {
                bool found = false;
                for (const auto& diagnostic : messages->all()) {
                    if (diagnostic.code == SOMTParser::Uir::ErrorCode::E_PARSE
                        && diagnostic.message.find("a continuous effect cannot depend") != std::string::npos
                        && diagnostic.message.find("future conditions") != std::string::npos) {
                        found = true;
                    }
                }
                VERIFY(found);
            }
        }
        if (output.empty()) { continue; }
        const auto write = [&](const std::string& suffix, const std::string& text) {
            const auto path = output / (example.name + suffix);
            VERIFY(!std::filesystem::exists(path));
            std::ofstream stream(path, std::ios::binary);
            stream << text;
            stream.close();
            VERIFY(stream.good());
        };
        write(".domain.pddl", example.domain);
        write(".problem.pddl", example.problem);
        std::string log;
        for (const auto& diagnostic : translated.diagnostics().all()) {
            log += std::string(SOMTParser::Uir::errorCodeName(diagnostic.code))
                + ": " + diagnostic.message + '\n';
        }
        write(".diagnostics.txt", log);
        if (example.accepted) {
            const auto target = output / (example.name + ".smt2");
            VERIFY(!std::filesystem::exists(target));
            translated.writeSmt2(target.string(), SOMTParser::Lower::OmtDialect::Z3);
        }
    }
    std::cout << "Continuous guard causal well-formedness source controls: " << cases.size() << '\n';
    return 0;
}
