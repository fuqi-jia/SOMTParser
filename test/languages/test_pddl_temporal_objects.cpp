#include "somtparser/frontend/parser.h"
#include "somtparser/languages/pddl_internal.h"
#include "somtparser/lowering/hir_to_parser.h"
#include "somtparser/lowering/omt_emitter.h"
#include "somtparser/hir/typecheck.h"
#include "planning_public_pipeline.h"
#include "test_helpers.h"
#include <filesystem>
#include <fstream>
#include <iostream>

namespace U = SOMTParser::Uir;
namespace H = U::Hir;
namespace L = SOMTParser::Lower;
struct TemporalObjectCase { std::string name, domain, problem; unsigned horizon; bool accepted; };

int main(int argc, char** argv) {
    const std::filesystem::path output = argc == 2 ? argv[1] : "";
    if (!output.empty()) { std::filesystem::create_directories(output); }
    const std::vector<TemporalObjectCase> cases{
#include "pddl_object_temporal_cases.inc"
    };
    std::ofstream ledger;
    if (!output.empty()) { ledger.open(output / "object-temporal-source-controls.tsv"); }
    for (const auto& example : cases) {
        const auto directory = example.accepted ? output : output / "rejected";
        if (!output.empty()) {
            std::filesystem::create_directories(directory);
            std::ofstream(directory / (example.name + ".domain.pddl")) << example.domain;
            std::ofstream(directory / (example.name + ".problem.pddl")) << example.problem;
        }
        U::Diagnostics diagnostics; U::TranslationReport report;
        auto result = SOMTParser::Lang::PddlInternal::buildClassicalEncoding(
            example.domain, example.problem, example.name, example.horizon, diagnostics, report);
        if (static_cast<bool>(result.model) != example.accepted) {
            std::cerr << "object source case " << example.name << '\n';
            for (const auto& message : diagnostics.all()) { std::cerr << message.message << '\n'; }
        }
        VERIFY(static_cast<bool>(result.model) == example.accepted);
        auto translated = SomtPlanningTest::publicTranslation(example.domain, example.problem,
            example.name, example.horizon, example.accepted);
        if (ledger) { ledger << example.name << '\t' << example.horizon << '\t' << example.accepted << '\n'; }
        if (!example.accepted) {
            VERIFY(diagnostics.hasErrors());
            if (!output.empty()) {
                std::ofstream log(directory / (example.name + ".diagnostics.txt"));
                for (const auto& message : diagnostics.all()) { log << message.message << '\n'; }
            }
            continue;
        }
        bool recordedPolicy = false;
        for (const auto& choice : report.choices()) {
            if (choice.unified_op == "object-fluents") {
                VERIFY(choice.strategy == "finite-temporal-strict-undefined-single-writer");
                recordedPolicy = true;
            }
        }
        VERIFY(recordedPolicy);
        VERIFY(H::typeCheck(*result.model, diagnostics));
        const bool metric = example.problem.find(":metric") != std::string::npos;
        VERIFY(result.model->objectives.size() == (metric ? 1u : 0u));
        auto parser = SOMTParser::newParser(); L::HirToParser lower(parser);
        VERIFY(lower.lower(*result.model, report, diagnostics));
        const auto objectives = L::emitObjectives(*result.model, L::OmtDialect::Z3, lower, diagnostics);
        VERIFY(!diagnostics.hasErrors());
        // Exercise the executable named-object beta map, not merely its data.
        for (const auto& choice : result.projection.choices) {
            if (choice.source_name.find("::object::") == std::string::npos) { continue; }
            VERIFY(choice.omit_label.empty());
            VERIFY(!choice.alternatives.empty());
            VERIFY(choice.alternatives.front().label == "undefined");
            U::Sem::ModelProjection projection; projection.choices.push_back(choice);
            for (const auto& selected : choice.alternatives) {
                U::Sem::Assignment target, source;
                for (const auto& alternative : choice.alternatives) {
                    target.emplace(alternative.target_name, alternative.target_name == selected.target_name ? "true" : "false");
                }
                VERIFY(projection.project(target, source, diagnostics));
                VERIFY(source.at(choice.source_name) == selected.label);
            }
        }
        if (!output.empty()) {
            translated.writeSmt2((output / (example.name + ".smt2")).string(), L::OmtDialect::Z3);
            std::ofstream internal(output / (example.name + ".internal.smt2"));
            parser->writeSMT2Module(internal);
            internal << objectives << "(check-sat)\n(exit)\n";
            std::ofstream mapping(output / (example.name + ".tsv"));
            for (const auto& entry : result.symbol_map) { mapping << entry.source << '\t' << entry.target << '\n'; }
            std::ofstream choices(output / (example.name + ".choices.tsv"));
            for (const auto& choice : result.projection.choices) {
                for (const auto& alternative : choice.alternatives) {
                    choices << choice.source_name << '\t' << alternative.label << '\t' << alternative.target_name << '\n';
                }
            }
        }
    }
    std::cout << "PDDL temporal object source controls passed: " << cases.size() << '\n';
    return 0;
}
