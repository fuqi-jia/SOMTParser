#include "somtparser/frontend/parser.h"
#include "somtparser/languages/pddl_internal.h"
#include "somtparser/lowering/hir_to_parser.h"
#include "somtparser/hir/typecheck.h"
#include "test_helpers.h"
#include "planning_public_pipeline.h"
#include <filesystem>
#include <fstream>
#include <iostream>

namespace U = SOMTParser::Uir;
namespace H = U::Hir;

struct Case { std::string name, domain, initial; unsigned horizon = 0; bool accepted = true; };

int main(int argc, char** argv) {
    const std::filesystem::path output = argc == 2 ? argv[1] : "";
    if (!output.empty()) { std::filesystem::create_directories(output); }
    const std::string graph = R"((define (domain d) (:requirements :adl :derived-predicates)
      (:types node) (:constants a b - node)
      (:predicates (edge ?x ?y - node) (reach ?x ?y - node) (marked ?x ?y - node))
      (:derived (reach ?x ?y - node)
        (or (edge ?x ?y) (exists (?z - node) (and (edge ?x ?z) (reach ?z ?y)))))))";
    const std::string actions = R"(
      (:action add :parameters (?x ?y - node) :effect (edge ?x ?y))
      (:action del :parameters (?x ?y - node) :effect (not (edge ?x ?y)))
      (:action tag :parameters (?x ?y - node) :precondition (reach ?x ?y)
        :effect (and (not (edge ?x ?y)) (when (reach ?x ?y) (marked ?x ?y))))
      (:action markdel :parameters (?x ?y - node)
        :effect (and (not (edge ?x ?y)) (when (reach ?x ?y) (marked ?x ?y))))))";
    std::vector<Case> cases;
    for (unsigned mask = 0; mask < 16; ++mask) {
        std::string initial;
        for (unsigned i = 0; i < 4; ++i) {
            if ((mask >> i) & 1U) { initial += "(edge " + std::string(1, "ab"[i / 2]) + " " + "ab"[i % 2] + ") "; }
        }
        cases.push_back({"graph" + std::to_string(mask), graph, initial});
        if (mask == 0 || mask == 2 || mask == 4 || mask == 6) {
            cases.push_back({"trace" + std::to_string(mask), graph.substr(0, graph.size() - 1) + actions, initial, 1});
        }
    }
    for (unsigned bits = 0; bits < 4; ++bits) {
        cases.push_back({"mutual" + std::to_string(bits), R"((define (domain d)
          (:requirements :adl :derived-predicates) (:predicates (seed) (blocked) (p) (q))
          (:derived (p) (q)) (:derived (q) (not (not (p))))
          (:derived (p) (and (seed) (not (blocked))))))",
          std::string(bits & 1U ? "(seed) " : "") + (bits & 2U ? "(blocked)" : "")});
    }
    cases.push_back({"typed", R"((define (domain d) (:requirements :typing :derived-predicates)
      (:types small - object) (:constants a - small b - object)
      (:predicates (base ?x) (p ?x)) (:derived (p ?x - small) (base ?x))))", "(base a) (base b)"});
    const std::string empty = R"((define (domain d) (:requirements :adl :derived-predicates)
      (:types node) (:predicates (base ?x - node) (p ?x ?y - node)) ))";
    const std::vector<std::string> invalid_rules{
        "(:derived (p ?x ?x) (base ?x))", "(:derived (p ?x ?y) (base ?x))",
        "(:derived (p ?x ?y) (and (base ?x) (base ?z)))",
        "(:derived (p ?x ?y) (or (and) (not (p ?x ?y))))",
        "(:derived (p ?x ?y) (imply (p ?x ?y) (and (base ?x) (base ?y))))",
        "(:derived (p ?x - object ?y - node) (and (base ?x) (base ?y)))",
        "(:derived (p ?x - missing ?y - node) (and (base ?x) (base ?y)))",
        "(:derived (p ?x ?y) (and (base ?x) (forall (?y - node) (base ?y))))"};
    for (std::size_t i = 0; i < invalid_rules.size(); ++i) {
        cases.push_back({"bad_rule" + std::to_string(i), empty.substr(0, empty.size() - 1) + invalid_rules[i] + ")", "", 0, false});
    }
    cases.push_back({"empty", empty.substr(0, empty.size() - 1)
        + "(:derived (p ?x ?y) (and (base ?x) (base ?y))))", ""});
    for (const auto& effect : {"(p ?x ?x)", "(not (p ?x ?x))", "(when (and) (p ?x ?x))",
                               "(forall (?y - node) (not (p ?x ?y)))"}) {
        cases.push_back({"bad_effect" + std::to_string(cases.size()), empty.substr(0, empty.size() - 1)
            + "(:derived (p ?x ?y) (and (base ?x) (base ?y)))"
              "(:action bad :parameters (?x - node) :effect " + effect + "))", "", 0, false});
    }
    const std::string initial_domain = R"((define (domain d) (:requirements :derived-predicates)
      (:predicates (base) (p)) (:derived (p) (base))))";
    cases.push_back({"bad_init", initial_domain, "(p)", 0, false});
    cases.push_back({"bad_negative_init", initial_domain, "(not (p))", 0, false});
    // These four cases deliberately combine the shared numeric and derived
    // APIs. Strict undefinedness belongs to the whole body, before LFP use.
    for (unsigned i = 0; i < 4; ++i) {
        const auto body = i == 3 ? "(or (= 1 1) (> (x) 0))" : "(not (> (x) 0))";
        const auto initial = i == 0 ? "(= (x) -1)" : i == 1 ? "(= (x) 1)" : "";
        cases.push_back({"numeric" + std::to_string(i),
            std::string("(define (domain d) (:requirements :adl :fluents :derived-predicates) ")
                + "(:predicates (p) (q)) (:functions (x)) (:derived (p) " + body + ") (:derived (q) (p)))", initial});
    }
    for (unsigned i = 0; i < 2; ++i) {
        cases.push_back({"namespace" + std::to_string(i), R"((define (domain d)
          (:requirements :adl :fluents :derived-predicates)
          (:predicates (p) (q)) (:functions (p) (q))
          (:derived (p) (not (> (p) 0))) (:derived (q) (> (q) 0))))",
          i == 0 ? "(= (p) -1) (= (q) 1)" : ""});
    }
    for (const auto& example : cases) {
        const std::string problem = "(define (problem problem) (:domain d) (:init " + example.initial + ") (:goal (and)))";
        U::Diagnostics diagnostics;
        U::TranslationReport report;
        auto result = SOMTParser::Lang::PddlInternal::buildClassicalEncoding(
            example.domain, problem, example.name, example.horizon, diagnostics, report);
        if (static_cast<bool>(result.model) != example.accepted) {
            std::cerr << "case " << example.name << '\n';
            for (const auto& d : diagnostics.all()) { std::cerr << d.message << '\n'; }
        }
        VERIFY(static_cast<bool>(result.model) == example.accepted);
        auto publicResult = SomtPlanningTest::publicTranslation(
            example.domain, problem, example.name, example.horizon, example.accepted);
        if (!example.accepted) { VERIFY(diagnostics.hasErrors()); continue; }
        VERIFY(H::typeCheck(*result.model, diagnostics));
        auto parser = SOMTParser::newParser();
        SOMTParser::Lower::HirToParser lower(parser);
        VERIFY(lower.lower(*result.model, report, diagnostics));
        if (!output.empty()) {
            publicResult.writeSmt2((output / (example.name + ".smt2")).string(), SOMTParser::Lower::OmtDialect::Z3);
            std::ofstream(output / (example.name + ".internal.smt2")) << parser->dumpSMT2();
            std::ofstream(output / (example.name + ".domain.pddl")) << example.domain;
            std::ofstream(output / (example.name + ".problem.pddl")) << problem;
            std::ofstream mapping(output / (example.name + ".tsv"));
            for (const auto& entry : result.symbol_map) { mapping << entry.source << '\t' << entry.target << '\n'; }
        }
    }
    std::cout << "PDDL derived frontend source controls passed: " << cases.size() << '\n';
    return 0;
}
