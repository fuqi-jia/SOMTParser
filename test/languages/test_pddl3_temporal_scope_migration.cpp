#include "somtparser/languages/pddl_internal.h"
#include "planning_public_pipeline.h"
#include "test_helpers.h"
#include <filesystem>
#include <fstream>
int main(int argc,char** argv) {
    const std::string domain=R"PDDL((define (domain d) (:requirements :durative-actions :preferences)
(:predicates (p)) (:durative-action a :parameters () :duration (= ?duration 1)
:condition (and) :effect (at end (p))))
)PDDL";
    const std::string problem=R"PDDL((define (problem task) (:domain d)  (:init (p)) (:goal (preference pref (p)))  )
)PDDL";
    const auto translated=SomtPlanningTest::publicTranslation(domain,problem,"temporal-scope-migration",1,true);
    SOMTParser::Uir::Diagnostics diagnostics;SOMTParser::Uir::TranslationReport report;
    const auto internal=SOMTParser::Lang::PddlInternal::buildClassicalEncoding(domain,problem,"temporal-scope-migration",1,diagnostics,report);
    VERIFY(internal.model);VERIFY(internal.model->objectives.empty());
    if(argc==2) {
        const std::filesystem::path output(argv[1]);std::filesystem::create_directories(output);
        translated.writeSmt2((output/"original.smt2").string(),SOMTParser::Lower::OmtDialect::Z3);
        std::ofstream(output/"original.domain.pddl")<<domain;std::ofstream(output/"original.problem.pddl")<<problem;
        std::ofstream mapping(output/"original.tsv");for(const auto& entry:internal.symbol_map) { mapping<<entry.source<<'\t'<<entry.target<<'\n'; }
    }
    return 0;
}
