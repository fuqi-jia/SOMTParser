#include "somtparser/frontend/parser.h"
#include "somtparser/lowering/omt_emitter.h"
#include "test_helpers.h"

#include <string>

using namespace SOMTParser;

static const char* definitions =
    "(declare-const x Int)(declare-const y Int)(declare-const p Bool)"
    "(define-objective low OBJECTIVE_MIN x)"
    "(define-objective high OBJECTIVE_MAX y)"
    "(define-maxsmt-objective soft)"
    "(assert-soft p :weight 7 :objective soft)";

static void testDefinitionsAndSelection() {
    Parser parser;
    VERIFY(parser.parseStr(definitions));
    auto manager = parser.getObjectiveManager();
    VERIFY(parser.getObjectives().empty());
    VERIFY(parser.getSoftAssertions().empty());
    VERIFY(!manager->getSelectedGomtObjective());
    VERIFY(manager->getGomtSoftAssertions("soft").size() == 1);
    VERIFY(parser.parseStr("(optimize-sat high)"));
    VERIFY(parser.getObjectives().size() == 1);
    VERIFY(parser.getObjectives()[0]->isMaximize());
    VERIFY(parser.getObjectives()[0]->getObjectiveTerm()->getName() == "y");
    VERIFY(parser.getSoftAssertions().empty());
    VERIFY(parser.parseStr("(optimize-sat soft)"));
    VERIFY(parser.getObjectives().size() == 1);
    VERIFY(parser.getObjectives()[0]->isMaxSAT());
    VERIFY(parser.getSoftAssertions().size() == 1);
    VERIFY(parser.parseStr("(assert-soft (not p) :weight 4 :objective soft)"));
    VERIFY(parser.getSoftAssertions().size() == 2);
    VERIFY(manager->getGomtSoftAssertions("soft").size() == 2);
    VERIFY(parser.parseStr("(optimize-sat low)"));
    VERIFY(parser.getObjectives()[0]->isMinimize());
    VERIFY(parser.getSoftAssertions().empty());
    VERIFY(parser.parseStr("(assert-soft p :weight 1 :objective soft)"));
    VERIFY(parser.getSoftAssertions().empty());
    VERIFY(parser.parseStr("(optimize-sat soft)"));
    VERIFY(parser.getSoftAssertions().size() == 3);
}

static void testCombinationKinds() {
    struct Example { const char* name; OPT_KIND kind; };
    const Example examples[] = {
        {"OBJECTIVE_LEX", OPT_KIND::OPT_LEX_OPTIMIZE},
        {"OBJECTIVE_PARETO", OPT_KIND::OPT_PARETO_OPTIMIZE},
        {"OBJECTIVE_BOX", OPT_KIND::OPT_BOX_OPTIMIZE},
        {"OBJECTIVE_MINMAX", OPT_KIND::OPT_MINMAX},
        {"OBJECTIVE_MAXMIN", OPT_KIND::OPT_MAXMIN},
    };
    for (const auto& example : examples) {
        Parser parser;
        VERIFY(parser.parseStr(definitions));
        VERIFY(parser.parseStr(std::string("(define-multi-objective combined ")
                              + example.name + " high soft low)"));
        VERIFY(parser.getObjectives().empty());
        VERIFY(parser.parseStr("(optimize-sat combined)"));
        const auto selected = parser.getObjectiveManager()->getSelectedGomtObjective();
        VERIFY(selected->getObjectiveKind() == example.kind);
        VERIFY(selected->getObjectiveSize() == 3);
        VERIFY(selected->getObjective(0)->isMaximize());
        VERIFY(selected->getObjective(1)->isMaxSAT());
        VERIFY(selected->getObjective(2)->isMinimize());
        VERIFY(parser.getSoftAssertions().size() == 1);
    }
}

static void testValueTermsAndAssumptions() {
    Parser parser;
    VERIFY(parser.parseStr(definitions));
    VERIFY(parser.parseStr("(optimize-sat low :assumption p :assumption (> x 0))"
                           "(get-value (low high soft x))"));
    const auto assumptions = parser.getAssumptions();
    VERIFY(assumptions.size() == 1);
    VERIFY(assumptions[0].size() == 2);
    const auto& script = parser.getScript();
    VERIFY(script[script.size() - 2].type == CMD_TYPE::CT_CHECK_SAT_ASSUMING);
    const auto& query = script[script.size() - 1];
    VERIFY(query.type == CMD_TYPE::CT_GET_VALUE);
    VERIFY(query.value_terms.size() == 4);
    VERIFY(query.value_terms[0]->getName() == "x");
    VERIFY(query.value_terms[1]->getName() == "y");
    const auto cost = parser.mkExpr("(ite p 0 7)");
    VERIFY(query.value_terms[2] == cost);
    VERIFY(query.value_terms[3] == query.value_terms[0]);
    VERIFY(parser.parseStr("(define-objective |quoted cost| OBJECTIVE_MIN x)"
                           "(get-value (|quoted cost|))"));
    VERIFY(parser.getScript()[parser.getScript().size() - 1].value_terms[0]->getName() == "x");
}

static void testResetAndRejectedExtensions() {
    Parser parser;
    VERIFY(parser.parseStr(definitions));
    VERIFY(parser.parseStr("(optimize-sat soft)(push 1)(assert p)(pop 1)"));
    VERIFY(parser.getObjectiveManager()->getSelectedGomtObjective());
    VERIFY(parser.parseStr("(reset-assertions)"));
    VERIFY(!parser.getObjectiveManager()->hasGomtObjectives());
    VERIFY(!parser.getObjectiveManager()->getSelectedGomtObjective());
    VERIFY(parser.getSoftAssertions().empty());
    VERIFY(parser.parseStr(definitions));
    VERIFY(parser.parseStr("(optimize-sat low)(reset)"));
    VERIFY(!parser.getObjectiveManager()->hasGomtObjectives());
    for (const char* bad : {
            "(define-objective bad OBJECTIVE_MIN x :order custom)",
            "(define-multi-objective bad OBJECTIVE_LEX low :strategy STRATEGY_LINEAR)",
            "(define-maxsmt-objective bad :strategy STRATEGY_LINEAR)",
            "(assert-soft p :objective missing)",
            "(assert-soft p :objective soft :objective soft)",
            "(assert-soft p :objective soft :weight 1 :weight 2)",
            "(optimize-sat missing)",
            "(optimize-sat low :unsupported true)",
            "(optimize-sat low :assumption x)",
            "(push 1)(define-objective bad OBJECTIVE_MIN x)",
            "(push 1)(optimize-sat low)",
            "(minimize x)",
            "(define-multi-objective bad OBJECTIVE_LEX low high)(get-value (bad))"}) {
        Parser rejected;
        VERIFY(rejected.parseStr(definitions));
        VERIFY(!rejected.parseStr(bad));
    }
}

static void testBvFpDefaultOrderRoundTrip() {
    for (const char* script : {
            "(set-logic QF_BV)(declare-const x (_ BitVec 8))(minimize x)",
            "(set-logic QF_BV)(declare-const x (_ BitVec 8))(maximize x)",
            "(set-logic QF_FP)(declare-const x (_ FloatingPoint 8 24))(minimize x)",
            "(set-logic QF_FP)(declare-const x (_ FloatingPoint 8 24))(maximize x)"}) {
        Parser parser;
        VERIFY(parser.parseStr(script));
        VERIFY(parser.getObjectives().size() == 1);
        const auto original = parser.getObjectives()[0];
        const auto original_term = original->getObjectiveTerm();
        const auto original_sort = original_term->getSort();
        const auto expected_comparison = original_sort->isBv()
            ? (original->isMinimize() ? COMP_KIND::COMP_BV_ULT : COMP_KIND::COMP_BV_UGT)
            : (original->isMinimize() ? COMP_KIND::COMP_FP_LT : COMP_KIND::COMP_FP_GT);
        VERIFY(original->getCompareOperator() == expected_comparison);
        std::string output = parser.dumpSMT2(Lower::OmtDialect::Gomt);
        for (size_t generation = 0; generation < 2; ++generation) {
            Parser reader;
            VERIFY(reader.parseStr(output));
            VERIFY(reader.getObjectives().size() == 1);
            const auto objective = reader.getObjectives()[0];
            VERIFY(objective->getObjectiveKind() == original->getObjectiveKind());
            VERIFY(objective->getCompareOperator() == expected_comparison);
            VERIFY(objective->getObjectiveTerm()->getName() == original_term->getName());
            VERIFY(objective->getObjectiveTerm()->getKind() == original_term->getKind());
            VERIFY(objective->getObjectiveTerm()->getSort()->toString() == original_sort->toString());
            output = reader.dumpSMT2(Lower::OmtDialect::Gomt);
        }
    }
}

int main() {
    testDefinitionsAndSelection();
    testCombinationKinds();
    testValueTermsAndAssumptions();
    testResetAndRejectedExtensions();
    testBvFpDefaultOrderRoundTrip();
    return 0;
}
