#include "somtparser/languages/pddl_internal.h"
#include "somtparser/hir/typecheck.h"
#include "planning_public_pipeline.h"
#include "test_helpers.h"
#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>

namespace U = SOMTParser::Uir;
namespace H = U::Hir;
struct Pddl3ClassicalCase { std::string name, domain, problem; unsigned horizon; bool accepted; };
#include "pddl3_classical_cases.inc"

int main(int argc, char** argv) {
    const std::filesystem::path output = argc == 2 ? argv[1] : "";
    if (!output.empty()) { std::filesystem::create_directories(output); }
    unsigned accepted = 0, refused = 0;
    for (const auto& example : cases) {
        auto translated = SomtPlanningTest::publicTranslation(example.domain, example.problem,
            example.name, example.horizon, example.accepted);
        if (!output.empty()) {
            std::ofstream diagnosticsFile(output / (example.name + ".diagnostics.txt"));
            for (const auto& message : translated.diagnostics().all()) { diagnosticsFile << message.message << '\n'; }
            std::ofstream(output / (example.name + ".domain.pddl")) << example.domain;
            std::ofstream(output / (example.name + ".problem.pddl")) << example.problem;
        }
        if (!example.accepted) { ++refused; continue; }
        ++accepted;
        if (!output.empty()) {
            // Public complete-module writer orders objectives before query/exit.
            translated.writeSmt2((output / (example.name + ".smt2")).string(),
                                 SOMTParser::Lower::OmtDialect::Z3);
        }
        U::Diagnostics diagnostics;
        U::TranslationReport report;
        auto internal = SOMTParser::Lang::PddlInternal::buildClassicalEncoding(
            example.domain, example.problem, example.name, example.horizon, diagnostics, report);
        VERIFY(internal.model);
        VERIFY(H::typeCheck(*internal.model, diagnostics));
        if (!output.empty()) {
            std::ofstream mapping(output / (example.name + ".tsv"));
            for (const auto& entry : internal.symbol_map) { mapping << entry.source << '\t' << entry.target << '\n'; }
        }
    }
    std::cout << "PDDL3 classical source controls: " << accepted << " accepted, " << refused << " refused\n";
    return 0;
}
