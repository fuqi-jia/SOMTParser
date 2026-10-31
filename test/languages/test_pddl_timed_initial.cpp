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

namespace U = SOMTParser::Uir;
namespace H = U::Hir;
namespace L = SOMTParser::Lower;

struct TimedCase {
    std::string name, initial, goal = "(g)", action;
    unsigned horizon = 0;
    bool accepted = true, requirement = true, maximize = false;
};

int main(int argc, char** argv) {
    const std::filesystem::path output = argc == 2 ? argv[1] : "";
    if (!output.empty()) { std::filesystem::create_directories(output); }
    const auto action = [](const std::string& condition, const std::string& effects, unsigned duration = 1) {
        return "(:durative-action a :parameters () :duration (= ?duration " + std::to_string(duration)
            + ") :condition " + condition + " :effect " + effects + ")";
    };
    std::vector<TimedCase> cases{
        {"late_irrelevant", "(g) (at 100 (q))"},
        {"wait_useful", "(at 5 (g)) (at 100 (q))"},
        {"restore_goal", "(g) (at 2 (not (g))) (at 7 (g))"},
        {"lose_goal", "(g) (at 7 (not (g)))"},
        {"negative_goal", "(p) (at 2 (not (p)))", "(not (p))"},
        {"same_time", "(at 3 (p)) (at 3 (q))", "(and (p) (q))"},
        {"duplicate", "(at 3 (g)) (at 3 (g))"},
        {"contradiction", "(at 3 (p)) (at 3 (not (p)))", "(and)"},
        {"decimal", "(at +0.125 (g))"},
        {"derived_goal", "(at 5 (p))", "(d)"},
        {"empty", "(g)"},
        {"ordinary_at", "(at a b) (at 5 (g))", "(and (at a b) (g))"},
        {"typed", "(at 2 (typed a))", "(typed a)"},
        {"action_irrelevant", "(at 100 (q))", "(g)", action("()", "(at end (g))"), 1},
        {"action_future_goal", "(at 5 (g))", "(and (g) (done))", action("()", "(at end (done))"), 1},
        {"read_conflict", "(p) (at 1 (p))", "(done)", action("(at start (p))", "(at end (done))"), 1},
        {"derived_read_conflict", "(p) (at 1 (p))", "(done)", action("(at start (d))", "(at end (done))"), 1},
        {"write_conflict", "(at 1 (p))", "(done)", action("()", "(and (at start (not (p))) (at end (done)))"), 1},
        {"interval_broken", "(p) (at 2 (not (p)))", "(done)", action("(over all (p))", "(at end (done))", 2), 1},
        {"interval_end", "(p) (at 3 (not (p)))", "(done)", action("(over all (p))", "(at end (done))", 2), 1},
        {"derived_interval_broken", "(p) (at 2 (not (p)))", "(done)", action("(over all (d))", "(at end (done))", 2), 1},
        {"derived_interval_end", "(p) (at 3 (not (p)))", "(done)", action("(over all (d))", "(at end (done))", 2), 1},
        {"bad_zero", "(at 0 (g))", "(and)", "", 0, false},
        {"bad_negative", "(at -0.5 (g))", "(and)", "", 0, false},
        {"bad_variable", "(at ?time (g))", "(and)", "", 0, false},
        {"bad_negative_literal", "(at 1 (not (g) (p)))", "(and)", "", 0, false},
        {"bad_unknown", "(at 1 (missing))", "(and)", "", 0, false},
        {"bad_arity", "(at 1 (p a))", "(and)", "", 0, false},
        {"bad_type", "(at 1 (typed c))", "(and)", "", 0, false},
        {"bad_derived", "(at 1 (d))", "(and)", "", 0, false},
        {"bad_negative_derived", "(at 1 (not (d)))", "(and)", "", 0, false},
        {"bad_numeric", "(at 1 (= (x) 3))", "(and)", "", 0, false},
        {"bad_conjunction", "(at 1 (and (p) (q)))", "(and)", "", 0, false},
        {"bad_requirement", "(at 1 (g))", "(and)", "", 0, false, false},
    };
    auto maximize = cases[1]; maximize.name = "maximize_wait"; maximize.maximize = true;
    cases.push_back(std::move(maximize));
    std::ofstream ledger;
    if (!output.empty()) { ledger.open(output / "source-controls.tsv"); }
    for (const auto& example : cases) {
        const std::string domain = "(define (domain timed) (:requirements :adl :fluents :durative-actions :derived-predicates "
            + std::string(example.requirement ? ":timed-initial-literals" : "") + ")"
            "(:types item) (:constants a b - item c - object)"
            "(:predicates (p) (q) (g) (done) (d) (at ?x ?y - object) (typed ?x - item))"
            "(:functions (x)) (:derived (d) (p)) " + example.action + ")";
        const std::string problem = "(define (problem p) (:domain timed) (:init " + example.initial
            + ") (:goal " + example.goal + ") (:metric "
            + (example.maximize ? "maximize" : "minimize") + " total-time))";
        if (!output.empty()) {
            const auto directory = example.accepted ? output : output / "rejected";
            std::filesystem::create_directories(directory);
            std::ofstream(directory / (example.name + ".domain.pddl")) << domain;
            std::ofstream(directory / (example.name + ".problem.pddl")) << problem;
        }
        U::Diagnostics diagnostics; U::TranslationReport report;
        auto result = SOMTParser::Lang::PddlInternal::buildClassicalEncoding(
            domain, problem, example.name, example.horizon, diagnostics, report);
        if (static_cast<bool>(result.model) != example.accepted) {
            std::cerr << "case " << example.name << '\n';
            for (const auto& d : diagnostics.all()) { std::cerr << d.message << '\n'; }
        }
        VERIFY(static_cast<bool>(result.model) == example.accepted);
        auto publicResult = SomtPlanningTest::publicTranslation(
            domain, problem, example.name, example.horizon, example.accepted);
        if (ledger) { ledger << example.name << '\t' << example.accepted << '\t'
                             << static_cast<bool>(result.model) << '\n'; }
        if (!example.accepted) {
            VERIFY(diagnostics.hasErrors());
            if (!output.empty()) {
                std::ofstream log(output / "rejected" / (example.name + ".diagnostics.txt"));
                for (const auto& d : diagnostics.all()) { log << d.message << '\n'; }
            }
            continue;
        }
        VERIFY(H::typeCheck(*result.model, diagnostics));
        VERIFY(result.model->objectives.size() == 1);
        auto parser = SOMTParser::newParser(); L::HirToParser lower(parser);
        VERIFY(lower.lower(*result.model, report, diagnostics));
        const auto objectives = L::emitObjectives(*result.model, L::OmtDialect::Z3, lower, diagnostics);
        VERIFY(!diagnostics.hasErrors());
        if (!output.empty()) {
            publicResult.writeSmt2((output / (example.name + ".smt2")).string(), L::OmtDialect::Z3);
            std::ofstream internal(output / (example.name + ".internal.smt2"));
            parser->writeSMT2Module(internal);
            internal << objectives << "(check-sat)\n(exit)\n";
            std::ofstream mapping(output / (example.name + ".tsv"));
            for (const auto& e : result.symbol_map) { mapping << e.source << '\t' << e.target << '\n'; }
        }
    }
    std::cout << "PDDL timed initial source controls passed: " << cases.size() << '\n';
    return 0;
}
