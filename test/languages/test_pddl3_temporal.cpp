#include "somtparser/languages/pddl_internal.h"
#include "somtparser/hir/typecheck.h"
#include "planning_public_pipeline.h"
#include "test_helpers.h"
#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>
struct Pddl3TemporalCase { std::string name, domain, problem; unsigned horizon; bool accepted; };
#include "pddl3_temporal_cases.inc"
int main(int argc,char** argv) {
    const std::filesystem::path output=argc==2 ? argv[1] : "";
    if(!output.empty()) { std::filesystem::create_directories(output); }
    for(const auto& example:cases) {
        auto translated=SomtPlanningTest::publicTranslation(example.domain,example.problem,example.name,example.horizon,example.accepted);
        if(!output.empty()) {
            std::ofstream(output/(example.name+".domain.pddl"))<<example.domain;
            std::ofstream(output/(example.name+".problem.pddl"))<<example.problem;
            std::ofstream log(output/(example.name+".diagnostics.txt"));
            for(const auto& d:translated.diagnostics().all()) { log<<d.message<<'\n'; }
        }
        if(!example.accepted) { continue; }
        SOMTParser::Uir::Diagnostics diagnostics;SOMTParser::Uir::TranslationReport report;
        auto internal=SOMTParser::Lang::PddlInternal::buildClassicalEncoding(example.domain,example.problem,example.name,example.horizon,diagnostics,report);
        VERIFY(internal.model);VERIFY(SOMTParser::Uir::Hir::typeCheck(*internal.model,diagnostics));
        if(!output.empty()) {
            translated.writeSmt2((output/(example.name+".smt2")).string(),SOMTParser::Lower::OmtDialect::Z3);
            std::ofstream mapping(output/(example.name+".tsv"));
            for(const auto& entry:internal.symbol_map) { mapping<<entry.source<<'\t'<<entry.target<<'\n'; }
        }
    }
    std::cout<<"PDDL3 temporal source controls: "<<cases.size()<<'\n';
    return 0;
}
