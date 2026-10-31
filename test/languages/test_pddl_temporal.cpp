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

struct TemporalCase {
    std::string name, actions, initial, goal;
    unsigned horizon = 1;
    bool accepted = true;
    std::string metric;
};

int main(int argc, char** argv) {
    const std::filesystem::path output = argc == 2 ? argv[1] : "";
    if (!output.empty()) { std::filesystem::create_directories(output); }
    const auto durative = [](const std::string& name, const std::string& duration,
        const std::string& conditions, const std::string& effects) {
        return "(:durative-action " + name + " :parameters () :duration " + duration
            + " :condition " + conditions + " :effect " + effects + ")";
    };
    std::vector<TemporalCase> cases{
        {"duration_update", durative("a", "(= ?duration 2.5)", "(and (at start (p)) (over all (p)))",
            "(and (at end (done)) (at end (increase (x) ?duration)))"), "(p) (= (x) 1)", "(done)",1,true,"(:metric minimize (x))"},
        {"invariant_broken", durative("a", "(= ?duration 1)", "(over all (p))",
            "(and (at start (not (p))) (at end (done)))"), "(p)", "(done)"},
        {"open_interval", durative("a", "(= ?duration 1)", "(over all (p))",
            "(and (at start (p)) (at end (not (p))) (at end (done)))"), "", "(and (done) (not (p)))"},
        {"history_true", durative("a", "(= ?duration 1)", "()",
            "(and (at start (not (p))) (when (at start (p)) (at end (done))))"), "(p)", "(done)"},
        {"history_false", durative("a", "(= ?duration 1)", "()",
            "(and (at start (p)) (when (at start (p)) (at end (done))))"), "", "(done)"},
        {"conditional_interval", durative("a", "(= ?duration 1)", "()",
            "(and (at start (not (p))) (at end (finished)) (when (over all (p)) (at end (done))))"), "(p)", "(and (finished) (not (done)))"},
        {"overlap", durative("a", "(= ?duration 2)", "(at start (< (x) 2))",
            "(and (at start (increase (x) 1)) (at end (increase (y) 1)))"), "(= (x) 0) (= (y) 0)", "(= (y) 2)",2},
        {"concurrent_add", durative("a", "(= ?duration 1)", "()", "(and (at start (increase (x) 2)) (at end (done)))")
            + durative("b", "(= ?duration 1)", "()", "(and (at start (increase (x) 3)) (at end (finished)))"),
            "(= (x) 0)", "(and (done) (finished) (= (x) 5))",2},
        {"concurrent_assign", durative("a", "(= ?duration 1)", "()", "(and (at start (assign (x) 2)) (at end (done)))")
            + durative("b", "(= ?duration 1)", "()", "(and (at start (assign (x) 3)) (at end (finished)))"),
            "(= (x) 0)", "(and (done) (finished))",2},
        {"inactive_disjunct_read", durative("a", "(= ?duration 1)", "(at start (or (= 1 1) (p)))", "(at end (done))")
            + durative("b", "(= ?duration 1)", "()", "(and (at start (not (p))) (at end (finished)))"),
            "(p)", "(and (done) (finished))",2},
        {"duration_start_state", durative("a", "(= ?duration (x))", "()",
            "(and (at start (assign (x) 2)) (at end (done)))"), "(= (x) 1)", "(done)"},
        {"duration_end_state", durative("a", "(at end (= ?duration (x)))", "()",
            "(and (at start (assign (x) 2)) (at end (done)))"), "(= (x) 1)", "(done)"},
        {"derived_open_interval", durative("a", "(= ?duration 1)", "(over all (reachable))",
            "(and (at start (p)) (at end (not (p))) (at end (done)))"), "", "(done)"},
        {"derived_broken", durative("a", "(= ?duration 1)", "(over all (reachable))",
            "(and (at start (not (p))) (at end (done)))"), "(p)", "(done)"},
        {"derived_mutex", durative("a", "(= ?duration 1)", "(at start (reachable))", "(at end (done))")
            + durative("b", "(= ?duration 1)", "()", "(and (at start (not (p))) (at end (finished)))"),
            "(p)", "(and (done) (finished))",2},
        {"folded_derived_mutex", durative("a", "(= ?duration 1)", "(at start (always-transitive))", "(at end (done))")
            + durative("b", "(= ?duration 1)", "()", "(and (at start (not (p))) (at end (finished)))"),
            "(p)", "(and (done) (finished))",2},
        {"folded_numeric_derived_mutex", durative("a", "(= ?duration 1)", "(at start (always-numeric))", "(at end (done))")
            + durative("b", "(= ?duration 1)", "()", "(and (at start (assign (x) 1)) (at end (finished)))"),
            "(= (x) 1)", "(and (done) (finished))",2},
        {"duration_read_mutex", durative("a", "(= ?duration (x))", "()", "(at end (done))")
            + durative("b", "(= ?duration 1)", "()", "(and (at start (assign (x) 1)) (at end (finished)))"),
            "(= (x) 1)", "(and (done) (finished))",2},
        {"relative_undefined", durative("a", "(= ?duration 1)", "()",
            "(and (at end (increase (x) 1)) (at end (done)))"), "", "(done)"},
        {"zero_horizon", durative("a", "(= ?duration 1)", "()", "(at end (done))"), "(done)", "(done)",0},
        {"zero_duration", durative("a", "(= ?duration 0)", "()", "(at end (done))"), "", "(done)"},
        {"negative_duration", durative("a", "(= ?duration -1)", "()", "(at end (done))"), "", "(done)"},
        {"future_guard_invalid", durative("a", "(= ?duration 1)", "()",
            "(when (at end (p)) (at start (done)))"), "", "()",0,false},
        {"unknown_unused_duration", durative("a", "(= ?duration (unknown))", "()", "()"), "", "()",0,false},
        {"duration_wrong_lhs", durative("a", "(= (x) 1)", "()", "()"), "", "()",0,false},
        {"duration_inequality", durative("a", "(and (>= ?duration 2) (<= ?duration 3))", "()", "(at end (done))"),
            "", "(done)",1,true,"(:metric minimize total-time)"},
    };
    for (const auto& example : cases) {
        const auto domain = "(define (domain temporal) (:requirements :adl :fluents :durative-actions :duration-inequalities :derived-predicates) "
            "(:predicates (p) (done) (finished) (reachable) (always) (always-transitive) (always-numeric)) "
            "(:functions (x) (y)) (:derived (reachable) (p)) (:derived (always) (or (= 1 1) (p))) "
            "(:derived (always-transitive) (always)) (:derived (always-numeric) (or (= 1 1) (> (x) 0))) " + example.actions + ")";
        const auto problem = "(define (problem p) (:domain temporal) (:init " + example.initial + ") (:goal "
            + example.goal + ") " + example.metric + ")";
        U::Diagnostics diagnostics;
        U::TranslationReport report;
        auto result = SOMTParser::Lang::PddlInternal::buildClassicalEncoding(
            domain, problem, example.name, example.horizon, diagnostics, report);
        if (static_cast<bool>(result.model) != example.accepted) {
            std::cerr << "case " << example.name << '\n';
            for (const auto& message : diagnostics.all()) { std::cerr << message.message << '\n'; }
        }
        VERIFY(static_cast<bool>(result.model) == example.accepted);
        auto publicResult = SomtPlanningTest::publicTranslation(
            domain, problem, example.name, example.horizon, example.accepted);
        if (!example.accepted) { VERIFY(diagnostics.hasErrors()); continue; }
        if (!H::typeCheck(*result.model, diagnostics)) {
            std::cerr << "typecheck case " << example.name << '\n';
            for (const auto& message : diagnostics.all()) { std::cerr << message.message << '\n'; }
        }
        VERIFY(!diagnostics.hasErrors());
        auto parser = SOMTParser::newParser();
        L::HirToParser lower(parser);
        VERIFY(lower.lower(*result.model, report, diagnostics));
        const auto objectives = L::emitObjectives(*result.model, L::OmtDialect::Z3, lower, diagnostics);
        VERIFY(!diagnostics.hasErrors());
        if (!output.empty()) {
            publicResult.writeSmt2((output / (example.name + ".smt2")).string(), SOMTParser::Lower::OmtDialect::Z3);
            std::ofstream internal(output / (example.name + ".internal.smt2"));
            parser->writeSMT2Module(internal);
            internal << objectives << "(check-sat)\n(exit)\n";
            std::ofstream mapping(output / (example.name + ".tsv"));
            for (const auto& entry : result.symbol_map) { mapping << entry.source << '\t' << entry.target << '\n'; }
            std::ofstream(output / (example.name + ".domain.pddl")) << domain;
            std::ofstream(output / (example.name + ".problem.pddl")) << problem;
        }
    }
    std::cout << "PDDL temporal frontend cases passed: " << cases.size() << '\n';
    return 0;
}
