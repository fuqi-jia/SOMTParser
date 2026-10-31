#include "somtparser/frontend/parser.h"
#include "somtparser/lowering/hir_to_parser.h"
#include "somtparser/hir/planning_numeric.h"
#include "somtparser/hir/typecheck.h"
#include "test_helpers.h"

#include <filesystem>
#include <fstream>
#include <iostream>

namespace H = SOMTParser::Uir::Hir;
namespace P = H::Planning;
namespace U = SOMTParser::Uir;

struct Fixture {
    H::ConstraintModel model;
    std::vector<P::NumericStateCell> before, after;
    H::ExprPtr a, b;
    U::Diagnostics diagnostics;
    Fixture() {
        for (const auto& name : {"x", "y", "z"}) {
            const auto make = [&](std::string prefix) {
                const std::string value = prefix + name, defined = value + "d";
                model.decls.push_back({value, H::Sort::real(), {}, {}, {}});
                model.decls.push_back({defined, H::Sort::boolean(), {}, {}, {}});
                return P::NumericStateCell{H::mkIdent(value, H::Sort::real()), H::mkIdent(defined, H::Sort::boolean())};
            };
            before.push_back(make(""));
            after.push_back(make("n"));
        }
        for (const auto& name : {"a", "b"}) { model.decls.push_back({name, H::Sort::boolean(), {}, {}, {}}); }
        a = H::mkIdent("a", H::Sort::boolean());
        b = H::mkIdent("b", H::Sort::boolean());
    }
    P::NumericValue read(std::size_t index) { return *P::numericRead(before[index], index, diagnostics); }
    P::NumericValue number(const char* value) {
        auto result = P::numericConstant(value, diagnostics); VERIFY(result); return *result;
    }
    void transition(const std::vector<P::NumericUpdate>& updates) {
        auto result = P::buildNumericTransition(model, before, after, updates, diagnostics);
        VERIFY(result);
        for (const auto& expression : result->constraints) { H::Constraint constraint; constraint.formula = expression; model.constraints.push_back(constraint); }
    }
    void emit(const std::filesystem::path& directory, const std::string& name) {
        VERIFY(H::typeCheck(model, diagnostics));
        auto parser = SOMTParser::newParser();
        SOMTParser::Lower::HirToParser lower(parser);
        U::TranslationReport report;
        VERIFY(lower.lower(model, report, diagnostics));
        const auto smt = parser->dumpSMT2();
        VERIFY(!smt.empty());
        if (!directory.empty()) { std::ofstream(directory/(name+".smt2")) << smt; }
    }
};

int main(int argc, char** argv) {
    const std::filesystem::path directory = argc == 2 ? argv[1] : "";
    if (!directory.empty()) { std::filesystem::create_directories(directory); }
    using K = P::NumericUpdateKind;
    {
        Fixture f; f.transition({{0,K::ASSIGN,f.number("1/3"),f.a,"A"}}); f.emit(directory,"initialize");
    }
    {
        Fixture f; f.transition({{0,K::ASSIGN,f.read(1),f.a,"A"},{1,K::ASSIGN,f.read(0),f.a,"A"}}); f.emit(directory,"swap");
    }
    {
        Fixture f; f.transition({{0,K::INCREASE,f.number("-3/2"),f.a,"A"},{0,K::DECREASE,f.number("2/3"),f.b,"B"}}); f.emit(directory,"additive");
    }
    {
        Fixture f; f.transition({{0,K::SCALE_UP,f.read(1),f.a,"A"},{0,K::SCALE_DOWN,f.read(2),f.b,"A"}}); f.emit(directory,"scaling");
    }
    {
        Fixture f; f.transition({{0,K::SCALE_UP,f.number("2"),f.a,"A"},{0,K::SCALE_UP,f.number("3"),f.b,"B"}}); f.emit(directory,"scaling_conflict");
    }
    {
        Fixture f; f.transition({{0,K::ASSIGN,f.number("2"),f.a,"A"},{0,K::ASSIGN,f.number("2"),f.b,"A"}}); f.emit(directory,"duplicate_assignment");
    }
    {
        Fixture f; f.transition({{0,K::ASSIGN,f.number("2"),f.a,"A"},{0,K::INCREASE,f.number("3"),f.b,"A"}}); f.emit(directory,"mixed_conflict");
    }
    {
        Fixture f; auto rhs = P::numericArithmetic(H::Op::DIV_REAL,{f.number("10"),f.read(1)},f.diagnostics); VERIFY(rhs);
        f.transition({{0,K::ASSIGN,*rhs,f.a,"A"}}); f.emit(directory,"division");
    }
    {
        Fixture f; auto cmp = P::numericCompare(H::Op::GT,f.read(0),f.number("0"),f.diagnostics); VERIFY(cmp);
        auto neg = P::numericLogical(H::Op::NOT,{*cmp},f.diagnostics); VERIFY(neg);
        auto disj = P::numericLogical(H::Op::OR,{*P::numericPredicate(H::mkBool(true),f.diagnostics),*cmp},f.diagnostics); VERIFY(disj);
        f.transition({});
        H::Constraint ca; ca.formula=H::mkOp(H::Op::EQ,{f.a,P::numericSatisfied(*neg)});f.model.constraints.push_back(ca);
        ca.formula=H::mkOp(H::Op::EQ,{f.b,P::numericSatisfied(*disj)});f.model.constraints.push_back(ca);
        f.emit(directory,"undefined_logic");
    }
    {
        Fixture f; P::NumericValue future{f.after[1].value,f.after[1].defined,{1}};
        VERIFY(!P::buildNumericTransition(f.model,f.before,f.after,{{0,K::ASSIGN,future,f.a,"A"}},f.diagnostics));
    }
    {
        Fixture f; P::NumericValue bad{H::mkInt(1),H::mkBool(true),{}};
        VERIFY(!P::buildNumericTransition(f.model,f.before,f.after,{{0,K::ASSIGN,bad,H::mkBool(false),"A"}},f.diagnostics));
    }
    {
        Fixture f; auto bad=std::make_shared<H::Expr>();bad->kind=H::ExprKind::OP;bad->op=H::Op::ADD;bad->sort=H::Sort::real();bad->args={H::mkBool(true),H::mkReal("2")};
        VERIFY(!P::buildNumericTransition(f.model,f.before,f.after,{{0,K::ASSIGN,{bad,H::mkBool(true),{}},H::mkBool(false),"A"}},f.diagnostics));
    }
    {
        Fixture f; VERIFY(!P::numericConstant("NaN",f.diagnostics));
    }
    // Append helper-dependency controls without changing the original cases.
    std::vector<std::string> helper_refusals;
    const auto helper = [](Fixture& f, const std::string& name, H::ExprPtr body) {
        H::FunDecl declaration{name, {}, body->sort, {}};
        declaration.body = body;
        declaration.auxiliary = true;
        f.model.funs.push_back(std::move(declaration));
        return H::mkApply(name, body->sort, {});
    };
    const auto expectRefusal = [](Fixture& f, const P::NumericValue& rhs,
                                   const H::ExprPtr& guard, const std::string& expected) {
        // The helper definitions themselves are valid typed HIR. Failure
        // must arise from the transition's state-dependency contract.
        VERIFY(H::typeCheck(f.model, f.diagnostics));
        const auto declarations = f.model.decls.size();
        const auto functions = f.model.funs.size();
        const auto constraints = f.model.constraints.size();
        VERIFY(!P::buildNumericTransition(f.model, f.before, f.after,
            {{0, K::ASSIGN, rhs, guard, "A"}}, f.diagnostics));
        bool diagnosed = false;
        for (const auto& diagnostic : f.diagnostics.all()) {
            diagnosed |= diagnostic.message.find(expected) != std::string::npos;
        }
        VERIFY(diagnosed);
        VERIFY(f.model.decls.size() == declarations && f.model.funs.size() == functions
            && f.model.constraints.size() == constraints);
    };
    for (const bool selected : {false, true}) {
        for (unsigned placement = 0; placement < 3; ++placement) {
            Fixture f;
            const auto leaf = placement == 0 ? f.after[0].value : f.after[0].defined;
            const auto inner = helper(f, "future_inner", leaf);
            const auto outer = helper(f, "future_outer", inner);
            auto rhs = f.number("1");
            auto guard = H::mkBool(selected);
            if (placement == 0) { rhs.value = outer; }
            else if (placement == 1) { rhs.defined = outer; }
            else { guard = H::mkOp(H::Op::AND, {guard, outer}); }
            expectRefusal(f, rhs, guard, "old state only");
            const std::string position = placement == 0 ? "value" : placement == 1 ? "definedness" : "guard";
            helper_refusals.push_back("transitive_future_" + position + (selected ? "_enabled" : "_disabled"));
        }
    }
    for (const bool in_definedness : {false, true}) {
        Fixture f;
        auto rhs = f.number("3");
        const auto captured = helper(f, "captured_old",
            in_definedness ? f.before[1].defined : f.before[1].value);
        if (in_definedness) { rhs.defined = captured; }
        else { rhs.value = captured; }
        // Empty metadata must not hide the old y coordinate in a body.
        expectRefusal(f, rhs, f.a, "read metadata");
        helper_refusals.push_back(in_definedness ? "old_metadata_definedness" : "old_metadata_value");
    }
    {
        Fixture f;
        const auto value = helper(f, "captured_y", f.before[1].value);
        const auto defined = helper(f, "captured_yd", f.before[1].defined);
        P::NumericValue old_y{value, defined, {1}};
        const auto rhs = P::numericArithmetic(H::Op::ADD, {old_y, f.number("1")}, f.diagnostics);
        VERIFY(rhs);
        // An unused exact definition may mention a future coordinate;
        // scanning every context definition would reject this valid update.
        helper(f, "unused_future", f.after[0].value);
        f.transition({{0, K::ASSIGN, *rhs, f.a, "A"}});
        f.emit(directory, "helper_old_state");
    }
    {
        Fixture f;
        const auto real = H::Sort::real();
        H::FunDecl declaration{"lexical_identity", {real}, real, {}};
        declaration.binders.push_back({"formal", real});
        declaration.body = H::mkBoundVar("formal", real);
        declaration.auxiliary = true;
        f.model.funs.push_back(std::move(declaration));
        P::NumericValue rhs{H::mkApply("lexical_identity", real, {f.before[0].value}),
            f.before[0].defined, {0}};
        f.transition({{0, K::ASSIGN, rhs, f.a, "A"}});
        f.emit(directory, "helper_lexical_argument");
    }
    if (!directory.empty()) {
        std::ofstream evidence(directory / "numeric-helper-dependency-controls.json");
        evidence << "{\"passed\":true,\"refusal_checks\":[";
        for (std::size_t i = 0; i < helper_refusals.size(); ++i) {
            if (i) { evidence << ','; }
            evidence << '"' << helper_refusals[i] << '"';
        }
        evidence << "],\"emitted_models\":[\"helper_old_state\",\"helper_lexical_argument\"]}\n";
    }
    std::cout << "planning numeric constructions and refusals passed\n";
    return 0;
}
