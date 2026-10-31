#include "somtparser/hir/planning_timed_initial.h"
#include "somtparser/hir/typecheck.h"
#include "somtparser/frontend/parser.h"
#include "somtparser/lowering/hir_to_parser.h"
#include "test_helpers.h"
#include <filesystem>
#include <fstream>
#include <iostream>

namespace U = SOMTParser::Uir;
namespace H = U::Hir;
namespace P = H::Planning;

struct Fixture {
    H::ConstraintModel model;
    U::Diagnostics diagnostics;
    std::vector<P::TemporalHappening> happenings;
    H::ExprPtr variable(const std::string& name, H::Sort sort) {
        model.decls.push_back({name, sort}); return H::mkIdent(name, sort);
    }
    void add(H::ExprPtr expression) { H::Constraint c; c.formula = expression; model.constraints.push_back(c); }
    void add(const std::vector<H::ExprPtr>& expressions) { for (const auto& e : expressions) { add(e); } }
    void grid(unsigned count) {
        for (unsigned i = 0; i < count; ++i) {
            happenings.push_back({variable("a" + std::to_string(i), H::Sort::boolean()),
                                 variable("t" + std::to_string(i), H::Sort::real())});
        }
        auto order = P::encodeHappeningOrder(happenings, diagnostics); VERIFY(order); add(*order);
    }
    void fixedSlots() {
        for (std::size_t i = 0; i < happenings.size(); ++i) {
            add(happenings[i].active);
            add(H::mkOp(H::Op::EQ, {happenings[i].time, H::mkReal(i == 0 ? "2" : "5")}));
        }
    }
    void events(const std::vector<P::TimedInitialLiteral>& events,
                std::vector<P::TemporalEndpointAccess> other = {}) {
        const auto encoded = P::encodeTimedInitialLiterals(happenings, events, "fixed:", diagnostics);
        VERIFY(encoded); add(encoded->constraints);
        for (std::size_t i = 0; i < happenings.size(); ++i) {
            std::vector<H::ExprPtr> occupied;
            for (const auto& matches : encoded->matches) { occupied.push_back(matches[i]); }
            const auto disjunction = occupied.empty() ? H::mkBool(false) : occupied.size() == 1
                ? occupied.front() : H::mkOp(H::Op::OR, occupied);
            add(H::mkOp(H::Op::EQ, {happenings[i].active, disjunction}));
        }
        other.insert(other.end(), encoded->accesses.begin(), encoded->accesses.end());
        const auto mutex = P::encodeTemporalInterference(other, diagnostics);
        VERIFY(mutex); add(*mutex);
    }
    void emit(const std::filesystem::path& output, const std::string& name) {
        VERIFY(H::typeCheck(model, diagnostics));
        auto parser = SOMTParser::newParser(); SOMTParser::Lower::HirToParser lower(parser);
        U::TranslationReport report; VERIFY(lower.lower(model, report, diagnostics));
        if (!output.empty()) { std::ofstream(output / (name + ".smt2")) << parser->dumpSMT2(); }
    }
};

int main(int argc, char** argv) {
    const std::filesystem::path output = argc == 2 ? argv[1] : "";
    if (!output.empty()) { std::filesystem::create_directories(output); }
    {
        Fixture f; f.grid(2);
        f.events({{H::mkReal("2"), "p", true}, {H::mkReal("5"), "p", false}});
        f.emit(output, "mandatory");
    }
    {
        Fixture f; f.grid(2);
        f.events({{H::mkReal("2"), "p", true}, {H::mkReal("2"), "p", true}});
        f.emit(output, "duplicate");
    }
    {
        Fixture f; f.grid(2);
        f.events({{H::mkReal("2"), "p", true}, {H::mkReal("2"), "p", false}});
        f.emit(output, "conflict");
    }
    for (const bool simultaneous : {false, true}) {
        Fixture f; f.grid(1);
        P::TemporalEndpointAccess reader;
        reader.active = H::mkBool(true); reader.time = H::mkReal(simultaneous ? "2" : "3");
        reader.propositionReads.insert("p"); reader.owner_id = "action:reader";
        f.events({{H::mkReal("2"), "p", true}}, {reader});
        f.emit(output, simultaneous ? "read_conflict" : "read_separate");
    }
    {
        Fixture f; f.grid(2); f.fixedSlots();
        std::vector<H::ExprPtr> goals;
        for (unsigned i = 0; i < 3; ++i) { goals.push_back(f.variable("g" + std::to_string(i), H::Sort::boolean())); }
        const auto end = f.variable("last", H::Sort::real());
        const auto makespan = f.variable("makespan", H::Sort::real());
        const auto encoded = P::encodeStableGoalMakespan(f.happenings, goals, end, f.diagnostics);
        VERIFY(encoded); f.add(encoded->constraints);
        f.add(H::mkOp(H::Op::EQ, {makespan, encoded->time}));
        f.emit(output, "stable");
    }
    {
        Fixture f;
        const auto goal = f.variable("g0", H::Sort::boolean());
        const auto end = f.variable("last", H::Sort::real());
        const auto makespan = f.variable("makespan", H::Sort::real());
        const auto encoded = P::encodeStableGoalMakespan({}, {goal}, end, f.diagnostics);
        VERIFY(encoded); f.add(encoded->constraints);
        f.add(H::mkOp(H::Op::EQ, {makespan, encoded->time}));
        f.emit(output, "empty");
    }
    {
        U::Diagnostics d;
        VERIFY(!P::encodeStableGoalMakespan({}, {}, H::mkReal("0"), d));
        VERIFY(!P::encodeStableGoalMakespan({}, {H::mkInt(1)}, H::mkReal("0"), d));
        VERIFY(!P::encodeTimedInitialLiterals({}, {{H::mkBool(true), "p", true}}, "fixed", d));
        VERIFY(!P::encodeTimedInitialLiterals({}, {{H::mkReal("1"), "", true}}, "fixed", d));
        VERIFY(!P::encodeTimedInitialLiterals({{H::mkInt(1), H::mkReal("1")}}, {}, "fixed", d));
    }
    std::cout << "planning timed initial and stable-goal makespan constructions passed\n";
    return 0;
}
