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
struct UnionCase { std::string name, domain, initial, goal; unsigned horizon=0; bool accepted=true; };

int main(int argc,char** argv) {
    const std::filesystem::path output=argc==2?argv[1]:"";
    if(!output.empty())std::filesystem::create_directories(output);
    const std::string header="(define (domain d) (:requirements :adl) "
        "(:types node place empty) (:constants a b - node p - place) ";
    const std::string pred="(:predicates (marked ?x - (either node place))) ";
    std::vector<UnionCase> cases{
        {"quantified_true",header+pred+")","(marked a) (marked b) (marked p)",
            "(forall (?x - (either place node)) (marked ?x))"},
        {"quantified_false",header+pred+")","(marked a) (marked b)",
            "(forall (?x - (either node place)) (marked ?x))"},
        {"empty_union",header+"(:predicates (p ?x - (either empty))) )","",
            "(forall (?x - (either empty)) (p ?x))"},
        {"overlapping_union",header+"(:predicates (marked ?x - object)))","(marked a) (marked b) (marked p)",
            "(forall (?x - (either node object node)) (marked ?x))"},
        {"dynamic_choice",header+pred+
            "(:action mark :parameters (?x - (either node place)) :effect (marked ?x)))",
            "","(marked p)",1},
        {"derived_union","(define (domain d) (:requirements :adl :derived-predicates) "
            "(:types node place) (:constants a b - node p - place) "
            "(:predicates (base ?x - (either node place)) (marked ?x - (either place node))) "
            "(:derived (marked ?x) (base ?x)))", "(base a) (base p)", "(and)"},
        {"numeric_union","(define (domain d) (:requirements :adl :fluents) "
            "(:types node place) (:constants a b - node p - place) "
            "(:predicates) (:functions (cost ?x - (either node place)) - number))",
            "(= (cost a) 1) (= (cost b) 2) (= (cost p) 3)","(= (+ (+ (cost a) (cost b)) (cost p)) 6)"},
        // VAL c_f_exp permits binary arithmetic here; variadic + belongs
        // to metric expressions, not ordinary numeric goal conditions.
        {"numeric_variadic_goal","(define (domain d) (:requirements :adl :fluents) "
            "(:types node place) (:constants a b - node p - place) "
            "(:predicates) (:functions (cost ?x - (either node place)) - number))",
            "(= (cost a) 1) (= (cost b) 2) (= (cost p) 3)",
            "(= (+ (cost a) (cost b) (cost p)) 6)",0,false},
        {"forall_effect",header+pred+
            "(:action markall :parameters () :effect (forall (?x - (either node place)) (marked ?x))))",
            "","(forall (?x - (either node place)) (marked ?x))",1},
        {"unknown_union",header+"(:predicates (p ?x - (either node missing))))","","(and)",0,false},
        {"empty_syntax",header+"(:predicates (p ?x - (either))))","","(and)",0,false},
        {"nested_type_union",header+"(:predicates (p ?x - (either node (either place)))))","","(and)",0,false},
        {"wrong_union_argument",header+"(:predicates (p ?x - node)) "
            "(:action bad :parameters (?x - (either node place)) :effect (p ?x)))","","(and)",0,false},
        {"unknown_quantified",header+pred+")","","(forall (?x - (either missing)) (and))",0,false},
        {"union_object_declaration","(define (domain d) (:requirements :adl) (:types node place) "
            "(:constants a - (either node place)) (:predicates))","","(and)",0,false},
        {"union_type_parent","(define (domain d) (:requirements :adl) "
            "(:types node place both - (either node place)) (:predicates))","","(and)",0,false},
    };
    std::vector<std::string> refused;
    for(const auto& c:cases) {
        const std::string problem="(define (problem p) (:domain d) (:init "+c.initial+") (:goal "+c.goal+"))";
        U::Diagnostics diagnostics;U::TranslationReport report;
        auto result=SOMTParser::Lang::PddlInternal::buildClassicalEncoding(c.domain,problem,c.name,c.horizon,diagnostics,report);
        if(bool(result.model)!=c.accepted) {
            std::cerr<<c.name<<'\n';for(const auto& d:diagnostics.all())std::cerr<<d.message<<'\n';
        }
        VERIFY(bool(result.model)==c.accepted);
        auto publicResult=SomtPlanningTest::publicTranslation(c.domain,problem,c.name,c.horizon,c.accepted);
        if(!c.accepted) { VERIFY(diagnostics.hasErrors());refused.push_back(c.name);continue; }
        VERIFY(H::typeCheck(*result.model,diagnostics));
        auto parser=SOMTParser::newParser();SOMTParser::Lower::HirToParser lower(parser);
        VERIFY(lower.lower(*result.model,report,diagnostics));
        if(!output.empty()) {
            publicResult.writeSmt2((output/(c.name+".smt2")).string(),SOMTParser::Lower::OmtDialect::Z3);
            std::ofstream(output/(c.name+".internal.smt2"))<<parser->dumpSMT2();
            std::ofstream(output/(c.name+".domain.pddl"))<<c.domain;
            std::ofstream(output/(c.name+".problem.pddl"))<<problem;
            std::ofstream map(output/(c.name+".tsv"));
            for(const auto& x:result.symbol_map)map<<x.source<<'\t'<<x.target<<'\n';
        }
    }
    if(!output.empty()) {
        std::ofstream out(output/"union-refusals.json");out<<"{\"passed\":true,\"cases\":[";
        for(std::size_t i=0;i<refused.size();++i){if(i)out<<',';out<<'"'<<refused[i]<<'"';}out<<"]}\n";
    }
    std::cout<<"PDDL finite union type controls passed: "<<cases.size()<<'\n';
    return 0;
}
