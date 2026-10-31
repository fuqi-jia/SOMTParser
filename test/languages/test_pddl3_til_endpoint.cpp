#include "somtparser/languages/pddl_internal.h"
#include "somtparser/hir/typecheck.h"
#include "planning_public_pipeline.h"
#include "test_helpers.h"

#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>

struct TilEndpointCase { std::string name, domain, problem; };
#include "pddl3_til_endpoint_cases.inc"

int main(int argc, char** argv) {
    VERIFY(argc == 1 || argc == 2);
    const std::filesystem::path output = argc == 2 ? argv[1] : "";
    if (!output.empty()) { std::filesystem::create_directories(output); }
    for (const auto& example : cases) {
        // An inconsistent hard trajectory is a translated UNSAT relation,
        // not a source rejection. Zero selected actions still have all TILs.
        auto translated = SomtPlanningTest::publicTranslation(
            example.domain, example.problem, example.name, 0, true);
        SOMTParser::Uir::Diagnostics diagnostics;
        SOMTParser::Uir::TranslationReport report;
        auto internal = SOMTParser::Lang::PddlInternal::buildClassicalEncoding(
            example.domain, example.problem, example.name, 0, diagnostics, report);
        VERIFY(internal.model);
        VERIFY(SOMTParser::Uir::Hir::typeCheck(*internal.model, diagnostics));
        VERIFY(internal.model->objectives.size() == 1);
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
        std::string mapping;
        for (const auto& entry : internal.symbol_map) {
            mapping += entry.source + '\t' + entry.target + '\n';
        }
        write(".tsv", mapping);
        const auto target = output / (example.name + ".smt2");
        VERIFY(!std::filesystem::exists(target));
        translated.writeSmt2(target.string(), SOMTParser::Lower::OmtDialect::Z3);
        VERIFY(std::filesystem::is_regular_file(target));
    }
    std::cout << "PDDL3 TIL endpoint source controls: " << cases.size() << '\n';
    return 0;
}
