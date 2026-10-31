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

struct FlowCase {
    std::string name, actions, initial = "(= (x) 0) (= (y) 0)", goal = "(and)";
    unsigned horizon = 1;
    bool accepted = true, requirement = true;
};

int main(int argc, char** argv) {
    const std::filesystem::path output = argc == 2 ? argv[1] : "";
    if (!output.empty()) { std::filesystem::create_directories(output); }
    const auto action = [](const std::string& name, const std::string& effect,
                           const std::string& condition = "()", const std::string& duration = "2") {
        return "(:durative-action " + name + " :parameters () :duration (= ?duration " + duration
            + ") :condition " + condition + " :effect " + effect + ")";
    };
    const auto rate = "(increase (x) #t)";
    std::vector<FlowCase> cases{
        {"empty", "", "(= (x) 0) (= (y) 0)", "(and)", 0},
        {"linear", action("a", "(and (at start (increase (x) 1)) (increase (x) (* #t 2)) (at end (decrease (x) 1)))")},
        {"overlap", action("a", rate) + action("b", "(increase (x) (* 2 #t))"), "(= (x) 0) (= (y) 0)", "(and)", 2},
        {"coupled", action("a", "(and (increase (x) (* #t (y))) (increase (y) (* #t 2)))"), "(= (x) 0) (= (y) 1)"},
        {"derived_open", action("a", rate, "(over all (d))")},
        {"interior_violation", action("a", "(and (increase (y) #t) (increase (x) (* #t (- 4 (* 8 (y))))))",
                                     "(over all (< (x) 1))", "1")},
        {"undefined_rate", action("a", "(increase (x) (* #t (y)))"), "(= (x) 0)"},
        {"guard_false", action("a", "(when (at start (p)) (increase (x) #t))"), "(= (y) 0)"},
        {"guard_remember", action("a", "(and (at start (not (p))) (when (at start (p)) (increase (x) #t)))"), "(p) (= (x) 0) (= (y) 0)"},
        {"guard_undefined", action("a", "(when (at start (or (p) (> (y) 0))) (increase (x) #t))"), "(p) (= (x) 0)"},
        {"guard_rate_undefined", action("a", "(when (at start (p)) (increase (x) (* #t (/ 1 (y)))))"), "(= (x) 0)"},
        {"history_true", action("a", "(and (increase (x) #t) (when (over all (d)) (at end (done))))"), "(= (x) 0) (= (y) 0)", "(done)"},
        {"history_false", action("a", "(and (increase (y) #t) (increase (x) (* #t (- 4 (* 8 (y))))) (when (over all (< (x) 1)) (at end (done))))", "()", "1")},
        {"internal_jump", action("a", rate) + "(:action b :parameters () :precondition () :effect (assign (x) 5))", "(= (x) 0) (= (y) 0)", "(and)", 2},
        {"endpoint_singular", action("a", "(and (increase (y) #t) (increase (x) (* #t (/ (y) (y)))))")},
        {"zero_duration", action("a", "(increase (x) (* #t (/ 1 (y))))", "()", "0")},
        {"forall_rate", action("a", "(forall (?o - item) (increase (x) #t))")},
        {"nonlinear_equilibrium", action("a", "(increase (x) (* #t (x)))")},
        {"nonlinear_wrong_witness", action("a", "(increase (x) (* #t (x)))"), "(= (x) 1) (= (y) 0)"},
        {"derived_dip", action("a", "(and (increase (y) #t) (increase (x) (* #t (* 2 (y)))))", "(over all (d))"), "(= (x) 1) (= (y) -1)"},
        {"derived_history_dip", action("a", "(and (increase (y) #t) (increase (x) (* #t (* 2 (y)))) (when (over all (d)) (at end (done))))"), "(= (x) 1) (= (y) -1)"},
        {"internal_pre_spike", action("a", rate, "(over all (< (x) 0))") + "(:action b :parameters () :precondition () :effect (assign (x) -1))", "(= (x) -1) (= (y) 0)", "(and)", 2},
        {"internal_post_spike", action("a", "(decrease (x) #t)", "(over all (< (x) 0))") + "(:action b :parameters () :precondition () :effect (assign (x) 0))", "(= (x) -1) (= (y) 0)", "(and)", 2},
        {"lexical_at", action("a", "(when (at start (at end depot)) (increase (x) #t))"), "(at end depot) (= (x) 0) (= (y) 0)"},
        {"lexical_over", action("a", "(when (at start (over all depot)) (increase (x) #t))"), "(over all depot) (= (x) 0) (= (y) 0)"},
        {"bad_nested_elapsed", action("a", "(increase (x) (* #t (+ #t 1)))"), "", "(and)", 0, false},
        {"bad_missing_elapsed", action("a", "(increase (x) 2)"), "", "(and)", 0, false},
        {"bad_assignment", action("a", "(assign (x) #t)"), "", "(and)", 0, false},
        {"bad_duration_rate", action("a", "(increase (x) (* #t ?duration))"), "", "(and)", 0, false},
        {"bad_total_time_rate", action("a", "(increase (x) (* #t total-time))"), "", "(and)", 0, false},
        {"bad_rate_symbol", action("a", "(increase (x) (* #t (missing)))"), "", "(and)", 0, false},
        {"bad_requirement", action("a", rate), "", "(and)", 0, false, false},
        {"unsupported_end_guard", action("a", "(when (at end (p)) (increase (x) #t))"), "", "(and)", 0, false},
        {"unsupported_interval_guard", action("a", "(when (over all (p)) (increase (x) #t))"), "", "(and)", 0, false},
    };
    std::ofstream ledger;
    if (!output.empty()) { ledger.open(output / "source-controls.tsv"); }
    for (const auto& example : cases) {
        const std::string domain = "(define (domain flows) (:requirements :adl :fluents :durative-actions :derived-predicates :duration-inequalities "
            + std::string(example.requirement ? ":continuous-effects" : "") + ")"
            "(:types item place) (:constants i j - item end all depot - place) (:predicates (p) (done) (d) "
            + (example.name == "lexical_at" ? "(at ?x ?y - place)" : example.name == "lexical_over" ? "(over ?x ?y - place)" : "")
            + ") (:functions (x) (y)) (:derived (d) (> (x) 0)) " + example.actions + ")";
        const std::string problem = "(define (problem flow) (:domain flows) (:init " + example.initial
            + ") (:goal " + example.goal + ") (:metric minimize total-time))";
        const auto directory = example.accepted ? output : output / "rejected";
        if (!output.empty()) {
            std::filesystem::create_directories(directory);
            std::ofstream(directory / (example.name + ".domain.pddl")) << domain;
            std::ofstream(directory / (example.name + ".problem.pddl")) << problem;
        }
        U::Diagnostics diagnostics; U::TranslationReport report;
        auto result = SOMTParser::Lang::PddlInternal::buildClassicalEncoding(
            domain, problem, example.name, example.horizon, diagnostics, report);
        if (static_cast<bool>(result.model) != example.accepted) {
            std::cerr << "continuous source case " << example.name << '\n';
            for (const auto& d : diagnostics.all()) { std::cerr << d.message << '\n'; }
        }
        VERIFY(static_cast<bool>(result.model) == example.accepted);
        auto publicResult = SomtPlanningTest::publicTranslation(domain, problem, example.name, example.horizon, example.accepted);
        if (ledger) { ledger << example.name << '\t' << example.accepted << '\t' << static_cast<bool>(result.model) << '\n'; }
        if (!example.accepted) {
            VERIFY(diagnostics.hasErrors());
            if (!output.empty()) {
                std::ofstream log(directory / (example.name + ".diagnostics.txt"));
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
        std::size_t sourceTrajectories = 0;
        for (const auto& function : result.model->funs) {
            if (function.name.find("__pddl_flow_") == 0) {
                VERIFY(!function.auxiliary); VERIFY(!function.body); ++sourceTrajectories;
            }
        }
        VERIFY(sourceTrajectories == (example.horizon == 0 ? 0 : (2 * example.horizon - 1) * 2));
        VERIFY(publicResult.semantics().stages().front().source.assumptions.arithmetic == U::Sem::ArithmeticSemantics::REAL);
        if (!output.empty()) {
            publicResult.writeSmt2((output / (example.name + ".smt2")).string(), L::OmtDialect::Z3);
            std::ofstream internal(output / (example.name + ".internal.smt2"));
            parser->writeSMT2Module(internal);
            internal << objectives << "(check-sat)\n(exit)\n";
            std::ofstream mapping(output / (example.name + ".tsv"));
            for (const auto& entry : result.symbol_map) { mapping << entry.source << '\t' << entry.target << '\n'; }
        }
    }
    std::cout << "PDDL continuous source controls passed: " << cases.size() << '\n';
    return 0;
}
