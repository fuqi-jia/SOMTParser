#include "somtparser/frontend/parser.h"
#include "somtparser/languages/pddl_internal.h"
#include "somtparser/lowering/hir_to_parser.h"
#include "somtparser/lowering/omt_emitter.h"
#include "somtparser/hir/typecheck.h"
#include "test_helpers.h"
#include "planning_public_pipeline.h"

#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>

namespace U = SOMTParser::Uir;
namespace H = U::Hir;
namespace L = SOMTParser::Lower;

struct NumericCase {
    std::string name, domain, problem;
    unsigned horizon = 1;
    bool accepted = true;
};

int main(int argc, char** argv) {
    const std::filesystem::path output = argc == 2 ? argv[1] : "";
    if (!output.empty()) { std::filesystem::create_directories(output); }
    const auto domain = [](const std::string& effect, const std::string& precondition = "()") {
        return "(define (domain numeric) (:requirements :adl :fluents) (:predicates (done)) "
            "(:functions (x) (y)) (:action step :parameters () :precondition " + precondition
            + " :effect (and (done) " + effect + ")))";
    };
    const auto problem = [](const std::string& init, const std::string& goal="(done)", const std::string& metric="") {
        return "(define (problem p) (:domain numeric) (:init " + init + ") (:goal " + goal + ") " + metric + ")";
    };
    std::vector<NumericCase> cases{
        {"swap",domain("(assign (x) (y)) (assign (y) (x))"),problem("(= (x) 2) (= (y) 3)","(done)","(:metric maximize (- (x) (y)))")},
        {"initialize",domain("(assign (x) (+ (y) 1.25))"),problem("(= (y) 5)")},
        {"relative_undefined",domain("(increase (x) 2)"),problem("(= (y) 5)")},
        {"undefined_not",domain("", "(not (> (x) 0))"),problem("(= (y) 5)")},
        {"undefined_or",domain("", "(or (= 1 1) (> (x) 0))"),problem("(= (y) 5)")},
        {"undefined_conditional",domain("(when (> (x) 0) (assign (y) 2))"),problem("(= (y) 5)")},
        {"inactive_division",domain("(when (= (y) 1) (assign (x) (/ 10 (y))))"),problem("(= (x) 4) (= (y) 0)")},
        {"active_division",domain("(assign (x) (/ 10 (y)))"),problem("(= (x) 4) (= (y) 0)")},
        {"additive",domain("(increase (x) 1.5) (decrease (x) 0.25)"),problem("(= (x) -2) (= (y) 0)")},
        {"scaling",domain("(scale-up (x) 3) (scale-down (x) 2)"),problem("(= (x) -2) (= (y) 0)")},
        {"conflicting",domain("(assign (x) 1) (increase (x) 2)"),problem("(= (x) 0) (= (y) 0)")},
        {"duplicate",domain("(assign (x) 1) (assign (x) 1)"),problem("(= (x) 0) (= (y) 0)")},
        {"numeric_goal",domain(""),problem("(= (x) 2) (= (y) 3)","(< (+ (x) 0.5) (y))","(:metric minimize (/ (+ (x) (y)) 2))"),0},
        {"undefined_metric",domain(""),problem("(= (y) 3)","()","(:metric minimize (x))"),0},
        {"bad_unreachable_rhs",domain("(when (= 1 2) (assign (x) (abs (y))))"),problem("(= (x) 0) (= (y) 0)"),0,false},
        {"bad_initial_duplicate",domain(""),problem("(= (x) 0) (= (x) 0)"),0,false},
        {"bad_numeric_object",domain("(assign (x) done)"),problem(""),0,false},
        {"bad_arity",domain("(assign (x) (/ 1))"),problem(""),0,false},
    };
    cases.push_back({"quantified",R"((define (domain numeric) (:requirements :adl :numeric-fluents)
        (:types item) (:constants a b - item) (:predicates (done)) (:functions (fuel ?i - item))
        (:action transfer :parameters () :effect (and (done)
            (forall (?i - item) (when (> (fuel ?i) 0) (decrease (fuel ?i) 0.5)))))))",
        problem("(= (fuel a) 2) (= (fuel b) -1)"),1,true});
    for (const auto& example : cases) {
        U::Diagnostics diagnostics;
        U::TranslationReport report;
        auto result = SOMTParser::Lang::PddlInternal::buildClassicalEncoding(
            example.domain,example.problem,example.name,example.horizon,diagnostics,report);
        if (static_cast<bool>(result.model) != example.accepted) {
            for (const auto& d : diagnostics.all()) { std::cerr << d.message << '\n'; }
            std::cerr << "case " << example.name << '\n';
        }
        VERIFY(static_cast<bool>(result.model) == example.accepted);
        auto publicResult = SomtPlanningTest::publicTranslation(
            example.domain, example.problem, example.name, example.horizon, example.accepted);
        if (!example.accepted) { VERIFY(diagnostics.hasErrors()); continue; }
        VERIFY(H::typeCheck(*result.model,diagnostics));
        auto parser=SOMTParser::newParser();L::HirToParser lower(parser);
        VERIFY(lower.lower(*result.model,report,diagnostics));
        auto objectives=L::emitObjectives(*result.model,L::OmtDialect::Z3,lower,diagnostics);
        VERIFY(!diagnostics.hasErrors());
        if (!output.empty()) {
            publicResult.writeSmt2((output / (example.name + ".smt2")).string(), SOMTParser::Lower::OmtDialect::Z3);
            std::ofstream internal(output / (example.name + ".internal.smt2"));
            parser->writeSMT2Module(internal);
            internal << objectives << "(check-sat)\n(exit)\n";
            std::ofstream mapping(output/(example.name+".tsv"));
            for (const auto& entry : result.symbol_map) { mapping << entry.source << '\t' << entry.target << '\n'; }
            std::ofstream(output/(example.name+".domain.pddl")) << example.domain;
            std::ofstream(output/(example.name+".problem.pddl")) << example.problem;
        }
    }
    std::cout << "PDDL numeric frontend construction cases passed: " << cases.size() << '\n';
    return 0;
}
