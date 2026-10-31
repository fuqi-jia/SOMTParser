// `(str.<= a b c)` is legal SMT-LIB and this parser could not read it.
//
// The SMT-LIB theory of strings declares
//
//     (str.<  String String String :chainable)
//     (str.<= String String String :chainable)
//
// -- an application with three or more arguments means the conjunction of
// ADJACENT pairs, so
//
//     (str.<= a b c)   is   (and (str.<= a b) (str.<= b c))
//
// -- exactly what the theory of Ints and Reals declares for `<` and `<=`
// (fixed for those in 17b6c44). This parser asserted exactly two parameters
// for all four string orderings, so a conforming script was a PARSE FAILURE
// with no message at all: condAssert throws, parseStr catches, and the caller
// sees `false`.
//
// `str.>` and `str.>=` are not in the standard at all -- the strings theory
// defines only the two above. They are kept as input leniency and given the
// same chainable shape, so whichever of the four the parser accepts has the
// documented semantics.
//
// The chain is expanded at parse time into a conjunction of binary nodes, so
// the DAG's NT_STR_LT/LE/GT/GE nodes stay binary -- the evaluator's binary
// handling of those kinds (eval_parser.cpp) is untouched by this change.

#include "somtparser/parser.h"

#include <initializer_list>
#include <iostream>
#include <string>

#include "test_helpers.h"

using namespace SOMTParser;

namespace {

bool has(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

// The engine hash-conses an `and` with its children in a canonical order, so
// the chain's pairs may not print in source order. What the expansion must
// guarantee is the SET of adjacent pairs, not their print order.
void expectChain(const std::string& dumped,
                 std::initializer_list<const char*> pairs) {
    VERIFY(has(dumped, "(and"));
    for (const char* p : pairs) {
        VERIFY(has(dumped, p));
    }
}

const char* kDecl = "(set-logic ALL)\n(declare-const a String)\n(declare-const b String)\n"
                    "(declare-const c String)\n(declare-const d String)\n";

std::string dump(const std::string& assertion, const char* what) {
    ParserPtr p = newParser();
    const std::string s = std::string(kDecl) + "(assert " + assertion + ")\n(check-sat)\n";
    if (!p->parseStr(s)) {
        std::cout << "  failed to parse (" << what << "): " << assertion << "\n";
        VERIFY(false);
    }
    return p->dumpSMT2();
}

} // namespace

int main() {
    std::cout << "======= chainable string comparisons =======\n";

    // ---- Three and four arguments, all four accepted orderings. ------------
    expectChain(dump("(str.<= a b c)", "str.<="), {"(str.<= a b)", "(str.<= b c)"});
    expectChain(dump("(str.< a b c)", "str.<"), {"(str.< a b)", "(str.< b c)"});
    expectChain(dump("(str.>= a b c)", "str.>="), {"(str.>= a b)", "(str.>= b c)"});
    expectChain(dump("(str.> a b c)", "str.>"), {"(str.> a b)", "(str.> b c)"});
    expectChain(dump("(str.< a b c d)", "str.< four"),
                {"(str.< a b)", "(str.< b c)", "(str.< c d)"});

    // ---- The order of the operands is preserved. ---------------------------
    {
        // Lexicographic order is not commutative: `(str.< a b c)` and
        // `(str.< c b a)` are different constraints, and a chain built from a
        // canonicalised operand list would confuse them.
        const std::string up = dump("(str.< a b c)", "ascending");
        const std::string down = dump("(str.< c b a)", "descending");
        VERIFY(has(up, "(str.< a b)") && has(up, "(str.< b c)"));
        VERIFY(has(down, "(str.< c b)") && has(down, "(str.< b a)"));
        VERIFY(up != down);
    }

    // ---- String literals and mixed operands expand too. --------------------
    {
        const std::string s = dump("(str.<= \"a\" b \"zz\")", "literals");
        VERIFY(has(s, "(str.<= \"a\" b)") && has(s, "(str.<= b \"zz\")"));
    }

    // ---- Two arguments are unchanged. --------------------------------------
    {
        // The binary case must not grow an `and` around it: every existing
        // script is this case, and a wrapper would change the shape of every
        // term in the corpus.
        const std::string s = dump("(str.<= a b)", "binary");
        VERIFY(has(s, "(assert (str.<= a b))"));
    }

    // ---- One argument is still an error. ------------------------------------
    {
        ParserPtr p = newParser();
        VERIFY(!p->parseStr(std::string(kDecl) + "(assert (str.<= a))\n(check-sat)\n"));
    }

    // ---- A type error is still a type error. --------------------------------
    {
        // The chain expansion must not swallow the operand type checks: an Int
        // in the middle of the chain is the same ERR_TYPE_MIS it was before.
        ParserPtr p = newParser();
        VERIFY(!p->parseStr("(set-logic ALL)\n(declare-const a String)\n"
                            "(declare-const i Int)\n"
                            "(assert (str.< a i a))\n(check-sat)\n"));
    }

    // ---- What it emits, it reads back. -------------------------------------
    {
        const std::string out = dump("(str.< a b c d)", "round trip");
        ParserPtr again = newParser();
        VERIFY(again->parseStr(out));
        VERIFY(again->dumpSMT2() == out);
    }

    std::cout << "All chainable string-comparison tests passed." << std::endl;
    return 0;
}
