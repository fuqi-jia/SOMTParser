#include "somtparser/frontend/parser.h"
#include "test_helpers.h"

#include <string>

using namespace SOMTParser;

static size_t count(const std::string& text, const std::string& token) {
    size_t result = 0, at = 0;
    while ((at = text.find(token, at)) != std::string::npos) {
        ++result;
        at += token.size();
    }
    return result;
}

static void testActivationOrderAndRoundTrip() {
    Parser parser;
    VERIFY(parser.parseStr(
        "(declare-const x Int)(declare-const p Bool)(declare-const q Bool)"
        "(assert-soft p :weight 9 :id preferred)"
        "(minimize x)(minimize preferred)"
        "(assert-soft q :weight 2 :id preferred)(check-sat)"));
    const auto objectives = parser.getObjectives();
    VERIFY(objectives.size() == 2);
    VERIFY(objectives[0]->isMinimize());
    VERIFY(objectives[1]->isMaxSAT());
    VERIFY(objectives[1]->getGroupID() == "preferred");
    const auto z3 = parser.dumpSMT2();
    VERIFY(count(z3, "(minimize ") == 1);
    VERIFY(count(z3, "(assert-soft ") == 2);
    VERIFY(z3.find("(minimize x") < z3.find("(assert-soft p"));
    Parser reader;
    VERIFY(reader.parseStr(z3));
    VERIFY(reader.getSoftAssertions().size() == 2);
    VERIFY(reader.dumpSMT2() == z3);
}

static void testDefaultAndQuotedGroups() {
    Parser parser;
    VERIFY(parser.parseStr("(declare-const p Bool)(assert-soft p)(minimize I)"));
    VERIFY(parser.getObjectives().size() == 1);
    VERIFY(parser.getObjectives()[0]->isMaxSAT());
    VERIFY(parser.getObjectives()[0]->getGroupID().empty());
    const auto output = parser.dumpSMT2();
    VERIFY(count(output, "(assert-soft ") == 1);
    Parser reader;
    VERIFY(reader.parseStr(output));
    VERIFY(reader.getSoftAssertions().size() == 1);
    Parser quoted;
    VERIFY(quoted.parseStr("(declare-const p Bool)(assert-soft p :id |soft cost|)(minimize |soft cost|)"));
    VERIFY(quoted.getObjectives()[0]->isMaxSAT());
    VERIFY(quoted.getObjectives()[0]->getGroupID() == "|soft cost|");
}

static void testDeclaredSymbolsWinAndAttributesFail() {
    Parser variable;
    VERIFY(variable.parseStr(
        "(declare-const p Bool)(declare-const cost Int)"
        "(assert-soft p :id cost)(minimize cost)"));
    VERIFY(variable.getObjectives()[0]->isMinimize());
    VERIFY(variable.getObjectives()[0]->getObjectiveTerm()->getName() == "cost");
    Parser function;
    VERIFY(function.parseStr(
        "(declare-const p Bool)(define-fun cost () Int 3)"
        "(assert-soft p :id cost)(minimize cost)"));
    VERIFY(function.getObjectives()[0]->isMinimize());
    Parser rejected;
    VERIFY(rejected.parseStr("(declare-const p Bool)(assert-soft p :id cost)"));
    VERIFY(!rejected.parseStr("(minimize cost :epsilon 1)"));
    VERIFY(rejected.parseStr("(minimize cost)"));
    VERIFY(!rejected.parseStr("(minimize cost)"));
    VERIFY(rejected.getObjectives().size() == 1);
    VERIFY(count(rejected.dumpSMT2(), "(assert-soft ") == 1);
}

int main() {
    testActivationOrderAndRoundTrip();
    testDefaultAndQuotedGroups();
    testDeclaredSymbolsWinAndAttributesFail();
    return 0;
}
