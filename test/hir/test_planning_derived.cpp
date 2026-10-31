#include "somtparser/hir/planning_derived.h"
#include "somtparser/hir/typecheck.h"
#include "somtparser/frontend/parser.h"
#include "somtparser/lowering/hir_to_parser.h"
#include "test_helpers.h"
#include <filesystem>
#include <fstream>
#include <iostream>
#include <iomanip>
#include <functional>
#include <map>
#include <stdexcept>

using namespace SOMTParser::Uir;
namespace H = SOMTParser::Uir::Hir;
namespace P = H::Planning;
using Assignment = std::map<std::string, bool>;
std::filesystem::path outputDirectory;

void emit(H::ConstraintModel model, const P::DerivedClosure& closure,
          const std::vector<H::ExprPtr>& atoms, const std::string& name) {
    model.decls.insert(model.decls.end(), closure.declarations.begin(), closure.declarations.end());
    model.constraints.insert(model.constraints.end(), closure.constraints.begin(), closure.constraints.end());
    for (std::size_t i = 0; i < atoms.size(); ++i) {
        H::Constraint constraint;
        constraint.formula = H::mkOp(H::Op::EQ, {atoms[i], closure.values[i]});
        model.constraints.push_back(constraint);
    }
    Diagnostics diagnostics;
    VERIFY(H::typeCheck(model, diagnostics));
    auto parser = SOMTParser::newParser();
    SOMTParser::Lower::HirToParser lower(parser);
    TranslationReport report;
    VERIFY(lower.lower(model, report, diagnostics));
    const auto text = parser->dumpSMT2();
    VERIFY(!text.empty());
    if (!outputDirectory.empty()) {
        std::ofstream(outputDirectory / (name + ".smt2")) << text;
        // The independent oracle must use the exact alpha-renaming selected by
        // this lowering call. Neither guess reserved-name suffixes nor infer
        // a correspondence from a satisfying assignment.
        std::ofstream symbols(outputDirectory / (name + ".symbols.json"));
        symbols << "[\n";
        bool first = true;
        for (const auto& declaration : model.decls) {
            const auto& target = lower.emittedSymbolName(declaration.name, diagnostics);
            VERIFY(!diagnostics.hasErrors());
            // Test fixture identifiers contain no JSON control characters.
            for (unsigned char c : declaration.name) { VERIFY(c >= 0x20); }
            for (unsigned char c : target) { VERIFY(c >= 0x20); }
            if (!first) { symbols << ",\n"; }
            first = false;
            symbols << "  {\"source\":" << std::quoted(declaration.name)
                    << ",\"target\":" << std::quoted(target)
                    << ",\"sort\":" << std::quoted(H::toString(declaration.sort))
                    << ",\"auxiliary\":" << (declaration.auxiliary ? "true" : "false") << "}";
        }
        symbols << "\n]\n";
        VERIFY(symbols.good());
    }
}

// An independent Boolean interpreter, deliberately not the HIR lowerer or a
// replay of the closure construction. Exhaustively check the entire auxiliary
// relation, including uniqueness, rather than one satisfying assignment.
bool value(const H::ExprPtr& term, const Assignment& state) {
    if (term->kind == H::ExprKind::LIT_BOOL) { return term->bool_value; }
    if (term->kind == H::ExprKind::IDENT) { return state.at(term->name); }
    if (term->kind != H::ExprKind::OP) { throw std::runtime_error("unexpected test term"); }
    const auto child = [&](std::size_t i) { return value(term->args.at(i), state); };
    switch (term->op) {
    case H::Op::NOT: return !child(0);
    case H::Op::AND:
        for (const auto& arg : term->args) { if (!value(arg, state)) { return false; } }
        return true;
    case H::Op::OR:
        for (const auto& arg : term->args) { if (value(arg, state)) { return true; } }
        return false;
    case H::Op::IMPLIES: return !child(0) || child(1);
    case H::Op::EQ: return child(0) == child(1);
    case H::Op::ITE: return child(0) ? child(1) : child(2);
    default: throw std::runtime_error("unexpected test operator");
    }
}

H::ExprPtr variable(H::ConstraintModel& model, const std::string& name) {
    model.decls.push_back({name, H::Sort::boolean()});
    return H::mkIdent(name, H::Sort::boolean());
}

void exactRelation(const H::ConstraintModel& model, const std::vector<H::ExprPtr>& atoms,
                   const std::vector<P::DerivedRule>& rules,
                   const std::vector<std::string>& basic,
                   const std::function<std::vector<bool>(const Assignment&)>& oracle) {
    Diagnostics diagnostic;
    auto closure = P::buildDerivedClosure(model, atoms, rules, "layer", diagnostic);
    VERIFY(closure.has_value());
    VERIFY(closure->rounds == atoms.size());
    static unsigned caseNumber = 0;
    emit(model, *closure, atoms, "relation" + std::to_string(caseNumber++));
    VERIFY(closure->declarations.size() < 16); // Size of these test fixtures only.
    H::ConstraintModel complete = model;
    complete.decls.insert(complete.decls.end(), closure->declarations.begin(), closure->declarations.end());
    complete.constraints.insert(complete.constraints.end(), closure->constraints.begin(), closure->constraints.end());
    Diagnostics check;
    VERIFY(H::typeCheck(complete, check));
    for (unsigned b = 0; b < (1U << basic.size()); ++b) {
        Assignment state;
        for (std::size_t i = 0; i < basic.size(); ++i) { state[basic[i]] = (b >> i) & 1U; }
        const auto expected = oracle(state);
        // Original placeholders must never supply support for their own LFP.
        for (unsigned placeholders = 0; placeholders < (1U << atoms.size()); ++placeholders) {
            for (std::size_t i = 0; i < atoms.size(); ++i) { state[atoms[i]->name] = (placeholders >> i) & 1U; }
            unsigned witnesses = 0;
            for (unsigned a = 0; a < (1U << closure->declarations.size()); ++a) {
                for (std::size_t i = 0; i < closure->declarations.size(); ++i) {
                    state[closure->declarations[i].name] = (a >> i) & 1U;
                }
                bool satisfied = true;
                for (const auto& constraint : closure->constraints) { satisfied &= value(constraint.formula, state); }
                if (!satisfied) { continue; }
                ++witnesses;
                for (std::size_t i = 0; i < atoms.size(); ++i) { VERIFY(value(closure->values[i], state) == expected[i]); }
            }
            VERIFY(witnesses == 1);
        }
    }
}

int main(int argc, char** argv) {
    if (argc == 2) {
        outputDirectory = argv[1];
        std::filesystem::create_directories(outputDirectory);
    }
    H::ConstraintModel model;
    const auto seed = variable(model, "seed"), block = variable(model, "block");
    const auto d = variable(model, "d"), e = variable(model, "e"), f = variable(model, "f");
    const auto alwaysFalse = [](const Assignment&) { return std::vector<bool>{false, false}; };
    exactRelation(model, {d, e}, {{0, d}, {1, e}}, {}, alwaysFalse);
    exactRelation(model, {d, e}, {{0, e}, {1, d}}, {}, alwaysFalse);
    exactRelation(model, {d, e}, {{0, e}, {1, d}, {0, seed}}, {"seed"},
        [](const Assignment& a) { return std::vector<bool>{a.at("seed"), a.at("seed")}; });
    exactRelation(model, {d, e, f}, {{0, seed}, {1, d}, {2, e}}, {"seed"},
        [](const Assignment& a) { return std::vector<bool>(3, a.at("seed")); });
    exactRelation(model, {d, e}, {{0, H::mkOp(H::Op::AND, {seed, H::mkOp(H::Op::NOT, {block})})},
        {1, d}, {0, e}}, {"seed", "block"}, [](const Assignment& a) {
            return std::vector<bool>(2, a.at("seed") && !a.at("block")); });
    exactRelation(model, {d}, {{0, seed}, {0, block}}, {"seed", "block"},
        [](const Assignment& a) { return std::vector<bool>{a.at("seed") || a.at("block")}; });
    exactRelation(model, {d, e}, {{0, seed}, {1, H::mkOp(H::Op::NOT, {H::mkOp(H::Op::NOT, {d})})}},
        {"seed"}, [](const Assignment& a) { return std::vector<bool>(2, a.at("seed")); });
    exactRelation(model, {d, e}, {{0, seed}, {1, H::mkOp(H::Op::ITE, {block, d, H::mkBool(false)})}},
        {"seed", "block"}, [](const Assignment& a) { return std::vector<bool>{a.at("seed"), a.at("seed") && a.at("block")}; });
    {
        // Existing user names occupy the common suffixes. The source atom e
        // must still be compared through the actual emitted map, not e!0.
        H::ConstraintModel collision = model;
        variable(collision, "e!0");
        variable(collision, "e!1");
        Diagnostics diagnostic;
        const auto closure = P::buildDerivedClosure(collision, {d, e},
            {{0, seed}, {1, d}}, "collision", diagnostic);
        VERIFY(closure);
        emit(collision, *closure, {d, e}, "symbol_collision");
    }
    for (const auto& bad : {H::mkOp(H::Op::NOT, {d}), H::mkOp(H::Op::IMPLIES, {d, seed}),
                           H::mkOp(H::Op::EQ, {d, seed}), H::mkOp(H::Op::ITE, {d, seed, block})}) {
        Diagnostics diagnostics;
        VERIFY(!P::buildDerivedClosure(model, {d}, {{0, bad}}, "bad", diagnostics));
        VERIFY(diagnostics.hasErrors());
    }
    for (const auto& bad : {H::ExprPtr{}, H::mkInt(1), H::mkIdent("missing", H::Sort::boolean()),
                           H::mkBoundVar("free", H::Sort::boolean())}) {
        Diagnostics diagnostics;
        VERIFY(!P::buildDerivedClosure(model, {d}, {{0, bad}}, "bad", diagnostics));
    }
    {
        Diagnostics a, b, c, empty;
        VERIFY(!P::buildDerivedClosure(model, {d, d}, {}, "bad", a));
        VERIFY(!P::buildDerivedClosure(model, {seed}, {{1, seed}}, "bad", b));
        VERIFY(!P::buildDerivedClosure(model, {H::mkBool(true)}, {}, "bad", c));
        const auto result = P::buildDerivedClosure(model, {}, {}, "empty", empty);
        VERIFY(result && result->values.empty() && result->declarations.empty() && result->rounds == 0);
    }
    {
        Diagnostics diagnostics;
        const auto result = P::buildDerivedClosure(model, {d, e},
            {{0, H::mkOp(H::Op::AND, {seed, H::mkOp(H::Op::NOT, {block})})}, {1, d}, {0, e}},
            "deps", diagnostics);
        VERIFY(result);
        VERIFY(result->base_dependencies[0] == std::set<std::string>({"seed", "block"}));
        VERIFY(result->base_dependencies[1] == result->base_dependencies[0]);
        VERIFY(result->base_function_dependencies[0].empty());
    }
    {
        H::ConstraintModel functions = model;
        H::FunDecl g; g.name = "g"; g.result = H::Sort::boolean(); g.body = seed;
        H::FunDecl h; h.name = "h"; h.result = H::Sort::boolean(); h.body = H::mkApply("g", H::Sort::boolean(), {});
        functions.funs = {g, h};
        Diagnostics diagnostics;
        const auto result = P::buildDerivedClosure(functions, {d, e},
            {{0, H::mkApply("h", H::Sort::boolean(), {})}, {1, d}}, "deps", diagnostics);
        VERIFY(result && result->base_dependencies[1] == std::set<std::string>({"seed"}));
        VERIFY(result->base_function_dependencies[1] == std::set<std::string>({"g", "h"}));
        functions.funs[0].body = d;
        Diagnostics hidden;
        VERIFY(!P::buildDerivedClosure(functions, {d}, {{0, seed}}, "bad", hidden));
    }
    {
        H::ConstraintModel numeric = model;
        numeric.decls.push_back({"x", H::Sort::real()});
        const auto defined = variable(numeric, "x_defined");
        const auto comparison = H::mkOp(H::Op::GE, {H::mkIdent("x", H::Sort::real()), H::mkReal("1/3")});
        Diagnostics diagnostics;
        const auto result = P::buildDerivedClosure(numeric, {d, e},
            {{0, H::mkOp(H::Op::AND, {defined, comparison})}, {1, d}}, "numeric", diagnostics);
        VERIFY(result && result->base_dependencies[1] == std::set<std::string>({"x", "x_defined"}));
        emit(numeric, *result, {d, e}, "numeric_guard");
    }
    {
        H::ConstraintModel hygiene = model;
        hygiene.bool_var_ranges.push_back({"fresh_", 1, 1000000000000ULL});
        variable(hygiene, "fresh_0");
        variable(hygiene, "fresh_0_fresh");
        H::Objective objective; objective.name = "fresh_0_fresh_fresh";
        objective.term = H::mkInt(0); hygiene.objectives.push_back(objective);
        Diagnostics diagnostics;
        const auto result = P::buildDerivedClosure(hygiene, {d, e}, {{0, seed}, {1, seed}}, "fresh", diagnostics);
        VERIFY(result && result->declarations.size() >= 2);
        VERIFY(result->declarations[0].name == "fresh_0_fresh_fresh_fresh");
        // The second declaration collides with the large packed interval.
        // The first instead checks ordinary declaration/objective hygiene.
        VERIFY(result->declarations[1].name == "fresh_1_fresh");
        H::ConstraintModel invalid = model;
        invalid.bool_var_ranges.push_back({"zero_", 0, 1});
        Diagnostics malformed;
        VERIFY(!P::buildDerivedClosure(invalid, {d}, {{0, seed}}, "bad", malformed));
        VERIFY(malformed.hasErrors());
        const auto shadow = H::mkForall({{"d", H::Sort::boolean()}}, H::mkBoundVar("d", H::Sort::boolean()));
        Diagnostics bad;
        VERIFY(!P::buildDerivedClosure(model, {d}, {{0, shadow}}, "bad", bad));
    }
    {
        // Seventy ground atoms require the last seed to propagate seventy
        // rounds. No fixed unrolling depth can satisfy this source contract.
        H::ConstraintModel chain;
        std::vector<H::ExprPtr> atoms;
        for (unsigned i = 0; i < 70; ++i) { atoms.push_back(variable(chain, "d" + std::to_string(i))); }
        std::vector<P::DerivedRule> rules{{69, H::mkBool(true)}};
        for (unsigned i = 0; i < 69; ++i) { rules.push_back({i, atoms[i + 1]}); }
        Diagnostics diagnostics;
        const auto result = P::buildDerivedClosure(chain, atoms, rules, "deep", diagnostics);
        VERIFY(result && result->rounds == 70);
        Assignment state;
        for (const auto& constraint : result->constraints) {
            state[constraint.formula->args[0]->name] = value(constraint.formula->args[1], state);
        }
        for (const auto& atom : result->values) { VERIFY(value(atom, state)); }
    }
    std::cout << "planning derived exhaustive relations, dependency metadata and refusals passed\n";
    return 0;
}
