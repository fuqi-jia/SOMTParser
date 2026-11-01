#include <sstream>
#include <string>

#include "somtparser/frontend/parser.h"
#include "test_helpers.h"

using namespace SOMTParser;

int main() {
    auto parser = newParser();
    VERIFY(parser->parseStr("(set-logic QF_LIA)"));
    // An n-element maximum has O(n) DAG nodes, but inlining each shared
    // prefix at both its comparison and selected value takes O(2^n) text.
    auto maximum = parser->mkVarInt("|__somt_dag_0|");
    for (unsigned i = 1; i < 40; ++i) {
        const auto item = parser->mkVarInt("x" + std::to_string(i));
        maximum = parser->mkIte(parser->mkGe(maximum, item), maximum, item);
    }
    const auto result = parser->mkVarInt("result");
    VERIFY(parser->assert(parser->mkEq(maximum, result)));
    std::ostringstream output;
    parser->writeSMT2Module(output);
    const auto text = output.str();
    VERIFY(text.size() < 20000);
    VERIFY(text.find("(let (") != std::string::npos);
    // Quoted and unquoted names denote the same symbol; never capture a
    // user's variable with a generated sharing name.
    VERIFY(text.find("(let ((__somt_dag_0 ") == std::string::npos);
    auto roundtrip = newParser();
    VERIFY(roundtrip->parseStr(text));
    VERIFY(roundtrip->getAssertions().size() == 1);

    // Binders retain their own scope through the conservative fallback.
    const auto quantified = parser->mkExpr(
        "(forall ((q Int)) (= (+ q 1) (+ q 1)))");
    VERIFY(quantified != nullptr);
    std::ostringstream scoped;
    dumpSMTLIB2Shared(quantified, scoped);
    VERIFY(scoped.str() == dumpSMTLIB2(quantified));
    return 0;
}
