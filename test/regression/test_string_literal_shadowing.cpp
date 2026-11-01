// String literals and quoted SMT-LIB identifiers occupy distinct lexical
// classes. In particular, the String literal "g" must not resolve to the
// quoted identifier |"g"| when both are visible in a term scope.

#include "somtparser/frontend/parser.h"

#include <iostream>
#include <string>

#include "test_helpers.h"

using namespace SOMTParser;

namespace {

bool has(const std::string& text, const std::string& needle) {
    return text.find(needle) != std::string::npos;
}

} // namespace

int main() {
    std::cout << "======= String literal / quoted identifier distinction =======\n";

    ParserPtr parser = newParser();
    const std::string source =
        "(set-logic SLIA)\n"
        "(declare-const |\"g\"| String)\n"
        "(declare-fun probe (String) Bool)\n"
        "(define-fun use-param ((|\"g\"| String)) Bool (probe |\"g\"|))\n"
        // This reproduces the bad lowering: the literal's length is exactly
        // one, irrespective of the quantified variable with the colliding
        // quoted spelling.
        "(assert (forall ((|\"g\"| String)) (= (str.len \"g\") 1)))\n"
        // A genuine quoted-identifier reference must still bind in the same
        // quantifier scope; the String literal in `probe` must remain literal.
        "(assert (forall ((|\"g\"| String)) (probe \"g\")))\n"
        // A let-bound identifier with the colliding spelling still resolves
        // to its bound value when used as an identifier.
        "(assert (let ((|\"g\"| \"x\")) (and (probe |\"g\"|) (probe \"g\"))))\n"
        "(assert (= |\"g\"| \"other\"))\n"
        "(check-sat)\n";
    VERIFY(parser->parseStr(source));

    const std::string output = parser->dumpSMT2();
    const auto assertions = parser->getAssertions();
    VERIFY(assertions.size() == 4);
    // The bad parser emitted (str.len |"g"|) under the binder. A correctly
    // parsed literal is constant-folded (and may therefore disappear), but it
    // must never become that bound variable.
    const std::string quantifiedLength = parser->toString(assertions[0]);
    VERIFY(!has(quantifiedLength, "(str.len |\"g\"|)"));
    auto lengthBody = assertions[0];
    if (lengthBody->getKind() == NODE_KIND::NT_FORALL) {
        VERIFY(!lengthBody->getChildren().empty());
        lengthBody = lengthBody->getChildren()[0];
    }
    VERIFY(parser->toString(lengthBody) == "true");

    // The separate probe assertion prevents a false pass caused by dropping
    // the colliding identifier altogether: its real use remains bound, while
    // the application argument stays a string literal.
    VERIFY(has(output, "|\"g\"| String"));
    const std::string quantifiedProbe = parser->toString(assertions[1]);
    VERIFY(has(quantifiedProbe, "(probe \"g\")"));
    VERIFY(!has(quantifiedProbe, "(probe |\"g\"|)"));
    // Formal parameter references remain identifiers in function definitions.
    VERIFY(has(output, "(probe |\"g\"|)"));
    // The retained let binds its identifier; the separate literal stays literal.
    const std::string letProbe = parser->toString(assertions[2]);
    VERIFY(has(letProbe, "(let ("));
    VERIFY(has(letProbe, "\"x\""));
    VERIFY(has(letProbe, "(probe \"g\")"));
    VERIFY(has(letProbe, "(probe |\"g\"|)"));

    // At top level too, the quoted symbol and the String literal remain
    // distinct terms in a single equality.
    const std::string globalEquality = parser->toString(assertions[3]);
    VERIFY(has(globalEquality, "|\"g\"|"));
    VERIFY(has(globalEquality, "\"other\""));

    std::cout << "String literal shadowing regression passed." << std::endl;
    return 0;
}
