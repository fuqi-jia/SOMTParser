#include "somtparser/frontend/parser.h"
#include "test_helpers.h"
#include <string>

using namespace SOMTParser;

int main() {
    // Finite-set output is represented by total Boolean arrays. Keep map as
    // a typed DAG operation through native parser round trips.
    const std::string source =
        "(set-logic ALL)"
        "(declare-const A (Array Int Bool))"
        "(declare-const B (Array Int Bool))"
        "(declare-const C (Array Int Bool))"
        "(assert (select ((_ map and) A B C) 2))"
        "(assert (select ((_ map or) A B) 3))"
        "(assert (select ((_ map not) A) 4))"
        "(assert (forall ((Q (Array Int Bool))) (= ((_ map or) Q Q) Q)))"
        "(check-sat)";
    auto parser = newParser();
    VERIFY(parser->parseStr(source));
    const auto dumped = parser->dumpSMT2();
    auto reader = newParser();
    VERIFY(reader->parseStr(dumped));
    VERIFY(reader->dumpSMT2() == dumped);
    for (const auto* invalid : {
            "((_ map not) A B)", "((_ map and) A)",
            "((_ map or) A 1)", "((_ map and) A I)",
            "((_ map and) A J)", "((_ map missing_function) A B)"}) {
        auto bad = newParser();
        VERIFY(!bad->parseStr(
            "(declare-const A (Array Int Bool))"
            "(declare-const B (Array Int Bool))"
            "(declare-const I (Array Int Int))"
            "(declare-const J (Array Bool Bool))"
            "(assert (= " + std::string(invalid) + " A))"));
    }

    // Deep map nesting must use the common iterative expression machine and
    // printer; a repeated binary map also tests shared children at each level.
    constexpr std::size_t depth = 12000;
    std::string deep = "(declare-const A (Array Int Bool))(assert (= ";
    for (std::size_t i = 0; i < depth; ++i) deep += "((_ map or) A ";
    deep += "A";
    deep.append(depth, ')');
    deep += " A))";
    auto deepParser = newParser();
    VERIFY(deepParser->parseStr(deep));
    auto deepReader = newParser();
    VERIFY(deepReader->parseStr(deepParser->dumpSMT2()));
    return 0;
}
