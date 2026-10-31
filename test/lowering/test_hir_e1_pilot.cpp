#include "somtparser/lowering/parser_to_hir.h"
#include "somtparser/lowering/hir_to_parser.h"
#include "somtparser/hir/typecheck.h"
#include "somtparser/translation/translate.h"
#include "somtparser/languages/register_all.h"
#include "test_helpers.h"

#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <unordered_set>
#include <vector>

using namespace SOMTParser;
namespace H = SOMTParser::Uir::Hir;
namespace U = SOMTParser::Uir;

struct CheckedLift {
    H::ConstraintModel model;
    ParserPtr parser;
};

static CheckedLift checkedLift(const ParserPtr& source, bool definitions = true) {
    CheckedLift result;
    U::Diagnostics diagnostics;
    Lower::ParserToHir lifter(source);
    VERIFY(lifter.lift(result.model, diagnostics, definitions));
    if (!H::typeCheck(result.model, diagnostics)) {
        for (const auto& d : diagnostics.all()) { std::cerr << d.message << '\n'; }
        VERIFY(false);
    }
    result.parser = newParser();
    Lower::HirToParser lowerer(result.parser);
    U::TranslationReport report;
    VERIFY(lowerer.lower(result.model, report, diagnostics));
    VERIFY(!diagnostics.hasErrors());
    return result;
}

static std::size_t nodeCount(const H::ConstraintModel& model) {
    std::vector<H::ExprPtr> pending;
    for (const auto& constraint : model.constraints) { pending.push_back(constraint.formula); }
    for (const auto& function : model.funs) { pending.push_back(function.body); }
    std::unordered_set<const H::Expr*> seen;
    while (!pending.empty()) {
        const auto node = pending.back();
        pending.pop_back();
        if (!node || !seen.insert(node.get()).second) { continue; }
        pending.insert(pending.end(), node->args.begin(), node->args.end());
    }
    return seen.size();
}

static std::string roundTrip(const std::string& text) {
    const auto source = newParser();
    VERIFY(source->parseStr(text));
    for (const bool definitions : {false, true}) {
        const auto lifted = checkedLift(source, definitions);
        const auto reader = newParser();
        VERIFY(reader->parseStr(lifted.parser->dumpSMT2()));
    }
    Lang::SourceUnit unit;
    unit.inline_source = text;
    TranslateOptions options;
    options.language_id = "smtlib2";
    const auto translated = translate(unit, options);
    if (translated.exitCode() != 0) { std::cerr << translated.diagnosticText(); }
    VERIFY(translated.exitCode() == 0 && translated.ok());
    VERIFY(newParser()->parseStr(translated.smt2()));
    return translated.smt2();
}

static void checkPilotInputs() {
    for (const std::string name : {"shadow", "shadow2", "shadow3", "fpterm",
                                   "realnum", "realnum2", "realnum3"}) {
        std::ifstream input("test/instances/hir_e1/" + name + ".smt2");
        VERIFY(input.good());
        std::ostringstream text;
        text << input.rdbuf();
        const auto output = roundTrip(text.str());
        // Optional local evidence for independent solver equivalence checks;
        // ordinary CTest runs create no files.
        if (const char* destination = std::getenv("SOMTPARSER_HIR_E1_DUMP_DIR")) {
            std::filesystem::create_directories(destination);
            std::ofstream file(std::filesystem::path(destination) / (name + ".smt2"),
                               std::ios::binary);
            file << output;
            VERIFY(file.good());
        }
    }
}

static void checkCaptureAvoidance() {
    // HIR already permits a binder shadowing a non-nullary function. Keep
    // this previously successful input byte-identical, while reserving such
    // function names when minting NEW binder names for other collisions.
    VERIFY(roundTrip("(declare-fun j (Int) Int)(declare-fun p (Int) Bool)"
                     "(assert (forall ((j Int)) (p j)))(check-sat)") ==
        "(set-logic ALL)\n(declare-fun j (Int) Int)\n(declare-fun p (Int) Bool)\n"
        "(assert (forall ((j Int)) (p j)))\n(check-sat)\n(exit)\n");
    // A generated name must skip pre-existing globals, including quoted aliases.
    const std::string declarations =
        "(declare-const j Int)(declare-const |j!1| Int)"
        "(declare-const p!1!i Int)(declare-fun p (Int Int) Bool)";
    roundTrip(declarations +
        "(assert (forall ((j Int)) (and (p j j!1)"
        " (exists ((j!2 Int)) (p j j!2)) (p j j!1))))(check-sat)");
    roundTrip(declarations +
        "(define-fun q ((i Int)) Bool (forall ((j Int)) (p i j)))"
        "(assert (q j))(check-sat)");
    roundTrip("(declare-const |j space| Int)(declare-fun p (Int) Bool)"
        "(assert (forall ((|j space| Int)) (p |j space|)))(check-sat)");
    // Different source scopes may share a DAG leaf; the free global after a
    // quantifier and the next bound scope must each resolve in their own scope.
    roundTrip("(declare-const j Int)(declare-fun p (Int) Bool)"
        "(assert (and (p j) (forall ((j Int)) (p j))"
        " (p j) (exists ((j Int)) (p j))))(check-sat)");
}

static void checkDeepShadowBody() {
    constexpr int depth = 12000;
    const auto source = newParser();
    VERIFY(source->parseStr("(declare-const j Int)(declare-fun p (Int) Bool)"
                           "(assert (forall ((j Int)) (p j)))"));
    const auto quantifier = source->getAssertions()[0];
    const auto bound = quantifier->getQuantVars()[0];
    auto term = bound;
    const auto one = source->mkConstInt(std::string("1"));
    for (int i = 0; i < depth; ++i) {
        term = source->getNodeManager()->createNode(bound->getSort(),
            i % 2 ? NODE_KIND::NT_SUB : NODE_KIND::NT_ADD,
            i % 2 ? "-" : "+", {term, one});
    }
    const auto predicate = source->getNodeManager()->createNode(source->mkBoolSort(),
        NODE_KIND::NT_UF_APPLY, "p", {term});
    source->assert(source->mkForall({predicate, bound}));
    const auto lifted = checkedLift(source);
    VERIFY(nodeCount(lifted.model) < 2 * depth + 30);
}

static void checkDeepSharedFpFields() {
    constexpr int depth = 12000;
    const auto source = newParser();
    VERIFY(source->parseStr("(declare-const v (_ BitVec 64))"
        "(declare-const y (_ FloatingPoint 11 53))"
        "(declare-const z (_ FloatingPoint 11 53))"));
    const auto v = source->getSymbolManager()->getVar("v");
    auto term = v;
    for (int i = 0; i < depth; ++i) {
        term = source->getNodeManager()->createNode(v->getSort(),
            i % 2 ? NODE_KIND::NT_BV_MUL : NODE_KIND::NT_BV_ADD,
            i % 2 ? "bvmul" : "bvadd", {term, v});
    }
    const auto index = [&](const char* number) { return source->mkConstInt(std::string(number)); };
    const auto fp = source->mkFpConst(
        source->mkBvExtract(term, index("63"), index("63")),
        source->mkBvExtract(term, index("62"), index("52")),
        source->mkBvExtract(term, index("51"), index("0")));
    source->assert(source->mkAnd(
        source->mkFpEq(source->getSymbolManager()->getVar("y"), fp),
        source->mkFpEq(source->getSymbolManager()->getVar("z"), fp)));
    const auto lifted = checkedLift(source);
    // All three BV fields and both comparisons retain the one shared DAG.
    VERIFY(nodeCount(lifted.model) < depth + 30);
}

static void checkDeepSharedRoundingModes() {
    constexpr int depth = 12000;
    const auto source = newParser();
    VERIFY(source->parseStr("(declare-const rm RoundingMode)(declare-const c Bool)"
                           "(declare-const y (_ FloatingPoint 11 53))"));
    const auto rm = source->getSymbolManager()->getVar("rm");
    const auto condition = source->getSymbolManager()->getVar("c");
    auto mode = rm;
    const auto nearest = source->mkRoundingMode("RNE");
    for (int i = 0; i < depth; ++i) {
        mode = source->getNodeManager()->createNode(rm->getSort(), NODE_KIND::NT_ITE,
            "ite", {condition, mode, nearest});
    }
    const auto conversion = [&](const char* number) {
        return source->mkToFp(source->mkConstInt(std::string("11")), source->mkConstInt(std::string("53")),
                              mode, source->mkConstInt(std::string(number)));
    };
    const auto y = source->getSymbolManager()->getVar("y");
    source->assert(source->mkAnd(source->mkFpEq(y, conversion("2")),
                                source->mkFpEq(y, conversion("3"))));
    const auto lifted = checkedLift(source);
    VERIFY(nodeCount(lifted.model) < depth + 30);
}

static void checkExplicitIntIsStillRejected() {
    H::ConstraintModel context;
    context.decls.push_back({"rm", H::Sort::roundingMode()});
    context.decls.push_back({"x", H::Sort::integer()});
    const auto conversion = H::mkToFp(H::Op::TO_FP,
        H::mkIdent("rm", H::Sort::roundingMode()),
        H::mkIdent("x", H::Sort::integer()), 11, 53);
    U::Diagnostics diagnostics;
    VERIFY(!H::typeCheckTerms(context, {{conversion, {}}}, diagnostics));
    VERIFY(diagnostics.firstErrorCode() == U::ErrorCode::E_TYPE);
}

int main() {
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());
    checkPilotInputs();
    checkCaptureAvoidance();
    checkDeepShadowBody();
    checkDeepSharedFpFields();
    checkDeepSharedRoundingModes();
    checkExplicitIntIsStillRejected();
    std::cout << "E1 HIR pilot regressions passed\n";
}
