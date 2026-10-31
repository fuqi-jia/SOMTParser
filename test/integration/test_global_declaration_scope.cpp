#include "somtparser/frontend/parser.h"
#include "test_helpers.h"

using namespace SOMTParser;

static const char* declarations =
    "(declare-sort S 0)"
    "(define-sort Alias () S)"
    "(declare-const x Int)"
    "(declare-fun zero () Int)"
    "(declare-fun f (Int) Int)"
    "(define-fun twice ((n Int)) Int (+ n n))"
    "(define-funs-rec ((r1 ((n Int)) Int) (r2 ((m Int)) Int))"
    " ((ite (= n 0) 0 (r2 (- n 1))) (ite (= m 0) 1 (r1 (- m 1)))))"
    "(declare-datatype Box ((box (field Int))))";

static void verifyDeclarations(const Parser& parser, bool present) {
    auto symbols = parser.getSymbolManager();
    VERIFY(parser.isDeclaredVariable("x") == present);
    VERIFY(parser.isDeclaredVariable("zero") == present);
    for (const char* name : {"f", "twice", "r1", "r2", "box", "field", "is-box"}) {
        VERIFY(parser.isDeclaredFunction(name) == present);
    }
    for (const char* name : {"S", "Alias", "Box"}) {
        VERIFY((symbols->resolveSort(name) != nullptr) == present);
    }
    VERIFY((symbols->getRecFunGroup("r1") != nullptr) == present);
    VERIFY((symbols->getRecFunGroup("r2") != nullptr) == present);
}

static void testPop(bool global) {
    Parser parser;
    VERIFY(!parser.getOptions()->getGlobalDeclarations());
    if (global) VERIFY(parser.parseStr("(set-option :global-declarations true)"));
    VERIFY(parser.parseStr("(declare-const base Int) (push 2)"));
    VERIFY(parser.parseStr(declarations));
    verifyDeclarations(parser, true);
    VERIFY(parser.parseStr("(assert (= (f x) (twice zero))) (pop 2)"));
    VERIFY(parser.getScopeDepth() == 0);
    VERIFY(parser.getAssertions().empty());
    VERIFY(parser.isDeclaredVariable("base"));
    verifyDeclarations(parser, global);
    if (global) {
        // Using the retained symbols catches a lookup failure, not just stale
        // declaration-order entries that happen to survive in a side table.
        VERIFY(parser.parseStr("(declare-const s Alias) (assert (= (f x) (twice zero)))"));
    } else {
        VERIFY(parser.parseStr(declarations));
        verifyDeclarations(parser, true);
    }
}

static void testResetAssertions(bool global, bool command) {
    Parser parser;
    parser.setOption("global-declarations", global);
    VERIFY(parser.parseStr(
        "(set-logic QF_UFLIA)"
        "(set-option :produce-models true)"
        "(declare-sort S 0)"
        "(define-sort Alias () S)"
        "(declare-fun f (Int) Int)"
        "(define-fun twice ((n Int)) Int (+ n n))"
        "(declare-const base Int)"
        "(assert (! (> base 0) :named base_positive))"
        "(minimize base)"
        "(push 1)"
        "(declare-const inner Int)"
        "(assert-soft (> inner 1) :id preference)"
        "(push 1)"
        "(assert false)"));
    VERIFY(parser.getScopeDepth() == 2);
    if (command) VERIFY(parser.parseStr("(reset-assertions)"));
    else VERIFY(parser.resetAssertions());
    VERIFY(parser.getScopeDepth() == 0);
    VERIFY(!parser.pop(1));
    VERIFY(parser.getAssertions().empty());
    VERIFY(parser.getNamedAssertions().empty());
    VERIFY(parser.getSoftAssertions().empty());
    VERIFY(parser.getSoftWeights().empty());
    VERIFY(parser.getGroupedSoftAssertions().empty());
    VERIFY(parser.getObjectives().empty());
    VERIFY(parser.isDeclaredVariable("base") == global);
    VERIFY(parser.isDeclaredVariable("inner") == global);
    VERIFY(parser.isDeclaredFunction("f") == global);
    VERIFY(parser.isDeclaredFunction("twice") == global);
    VERIFY((parser.getSymbolManager()->resolveSort("S") != nullptr) == global);
    VERIFY((parser.getSymbolManager()->resolveSort("Alias") != nullptr) == global);
    VERIFY(parser.getOptions()->getGlobalDeclarations() == global);
    VERIFY(parser.getOptions()->getLogic() == "QF_UFLIA");
    VERIFY(parser.getOptions()->options.at("produce-models") == "true");
    if (!global) VERIFY(parser.parseStr("(declare-const base Int)"));
    VERIFY(parser.parseStr("(push 1) (assert (> base 2)) (pop 1)"));
    VERIFY(parser.getAssertions().empty());
    VERIFY(parser.getScopeDepth() == 0);
}

static void testReset(bool command) {
    Parser parser;
    auto options = parser.getOptions();
    VERIFY(parser.parseStr("(set-option :global-declarations true) (set-option :keep_let false)"));
    VERIFY(parser.parseStr("(push 1)"));
    VERIFY(parser.parseStr(declarations));
    VERIFY(parser.parseStr("(assert (> x 0)) (minimize x)"));
    if (command) VERIFY(parser.parseStr("(reset)"));
    else VERIFY(parser.reset());
    verifyDeclarations(parser, false);
    VERIFY(parser.getScopeDepth() == 0);
    VERIFY(parser.getAssertions().empty());
    VERIFY(parser.getObjectives().empty());
    VERIFY(parser.getOptions() == options);
    VERIFY(options->options.empty());
    VERIFY(options->getLogic() == "ALL");
    VERIFY(options->getKeepLet());
    VERIFY(!options->getGlobalDeclarations());
    VERIFY(parser.parseStr("(push 1) (declare-const x Int) (pop 1)"));
    VERIFY(!parser.isDeclaredVariable("x"));
    VERIFY(parser.parseStr("(set-logic QF_LIA) (declare-const y Int)"));
    VERIFY(options->getLogic() == "QF_LIA");
    if (command) VERIFY(parser.parseStr("(reset)"));
    else VERIFY(parser.reset());
    VERIFY(options->getLogic() == "ALL");
    VERIFY(!parser.isDeclaredVariable("y"));

    options->setKeepLet(false);
    options->setExpandFunctions(true);
    options->setExpandRecursiveFunctions(true);
    options->setStrictSmtlib(true);
    if (command) VERIFY(parser.parseStr("(reset)"));
    else VERIFY(parser.reset());
    VERIFY(parser.getOptions() == options);
    VERIFY(!options->getKeepLet());
    VERIFY(options->getExpandFunctions());
    VERIFY(options->getExpandRecursiveFunctions());
    VERIFY(options->getStrictSmtlib());
}

static void testContextResetAndSoftPositions() {
    // The context contract also applies to clients that do not use Parser's
    // reset wrapper to replace its managers.
    ParserContext context;
    auto symbols = std::make_shared<SymbolManager>();
    auto options = std::make_shared<GlobalOptions>();
    options->setOption("global-declarations", "true");
    context.setSymbolManager(symbols);
    context.setOptions(options);
    symbols->registerSort("Alias", SortManager::INT_SORT);
    context.soft_assertions.push_back(nullptr);
    context.soft_weights.push_back(nullptr);
    context.soft_objective_positions.push_back(2);
    context.pushScope();
    context.soft_assertions.push_back(nullptr);
    context.soft_weights.push_back(nullptr);
    context.soft_objective_positions.push_back(3);
    context.popScope();
    VERIFY(context.soft_objective_positions == std::vector<size_t>{2});
    context.pushScope();
    context.resetAssertions();
    VERIFY(context.soft_objective_positions.empty());
    VERIFY(context.scope_stack_.empty());
    VERIFY(symbols->hasSort("Alias"));
    context.resetAll();
    VERIFY(!symbols->hasSort("Alias"));
    VERIFY(symbols->getSortOrder().empty());
    VERIFY(!options->getGlobalDeclarations());
}

int main() {
    testPop(false);
    testPop(true);
    for (bool command : {false, true}) {
        testResetAssertions(false, command);
        testResetAssertions(true, command);
        testReset(command);
    }
    testContextResetAndSoftPositions();
    return 0;
}
