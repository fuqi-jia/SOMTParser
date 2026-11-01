#include "somtparser/frontend/parser.h"
#include "test_helpers.h"

using namespace SOMTParser;

int main() {
    Parser parser;
    parser.setCommandLogging(true);
    VERIFY(parser.parseStr(
        "(declare-const a Bool) (push 2)"
        "(check-sat-assuming (a (not a))) (pop 2)"
        "(check-sat-assuming ()) (reset) (check-sat)"));
    const auto& commands = parser.getScript();
    VERIFY(commands.size() == 7);
    VERIFY(commands[1].push_pop_level == 2);
    VERIFY(commands[3].push_pop_level == 2);
    VERIFY(commands[2].type == CMD_TYPE::CT_CHECK_SAT_ASSUMING);
    VERIFY(commands[2].assumptions.size() == 2);
    VERIFY(dumpSMTLIB2(commands[2].assumptions[0]) == "a");
    VERIFY(dumpSMTLIB2(commands[2].assumptions[1]) == "(not a)");
    VERIFY(commands[4].assumptions.empty());
    VERIFY(commands[6].assumptions.empty());
    VERIFY(parser.getAssumptions().empty());

    Parser sequential;
    VERIFY(sequential.loadStr(
        "(push 0) (push 3) (declare-const b Bool)"
        "(check-sat-assuming (b)) (pop 3) (check-sat)"));
    VERIFY(sequential.nextCommand().push_pop_level == 0);
    VERIFY(sequential.nextCommand().push_pop_level == 3);
    VERIFY(sequential.nextCommand().type == CMD_TYPE::CT_DECLARE_CONST);
    const auto query = sequential.nextCommand();
    VERIFY(query.assumptions.size() == 1);
    VERIFY(sequential.nextCommand().push_pop_level == 3);
    VERIFY(sequential.nextCommand().assumptions.empty());
    VERIFY(dumpSMTLIB2(query.assumptions[0]) == "b");
    VERIFY(!sequential.isDeclaredVariable("b"));
    return 0;
}
