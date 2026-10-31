// A symbol the API accepts must be one SMT-LIB can spell.
//
// SMT-LIB 2.6 §3.1 gives a symbol two spellings. A SIMPLE symbol is made of
// letters, digits and `~!@$%^&*_-+=<>.?/` and may not begin with a digit; a
// QUOTED one, `|...|`, may contain anything except `|` and `\`. The two denote
// the same symbol, so which to write is a decision made when printing.
//
// It was not being made. A name that arrived quoted stayed quoted, because the
// bars were part of the stored name; a name built through the API was printed
// exactly as given. A variable created as `x(1)` -- which mkVar accepts, and
// which is an ordinary identifier in several input languages -- was therefore
// emitted as
//
//     (declare-fun x(1) () Int)
//
// which is not a well-formed command. No other solver reads it, and this
// library reads it back only because getSymbol() scans leniently, so a round
// trip through this parser alone did not reveal it.
//
// The assertions below are on the emitted TEXT and on its re-parse, because
// that is where the defect lived: every stage before printing was content with
// the name.

#include "somtparser/frontend/parser.h"

#include <iostream>
#include <sstream>
#include <string>

#include "test_helpers.h"

using namespace SOMTParser;

namespace {

bool has(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

/** Declare a variable of the given name through the API and dump the script. */
std::string dumpWithVar(const std::string& name) {
    ParserPtr p = newParser();
    std::shared_ptr<DAGNode> v = p->mkVar(p->mkIntSort(), name);
    // `Parser::assert` is a member function, so parser.h undefines the macro;
    // <cassert> must be included after it, and this file does not need it.
    p->assert(p->mkGt(v, p->mkConstInt(0)));
    return p->dumpSMT2();
}

} // namespace

int main() {
    std::cout << "======= symbol quoting when printing =======\n";

    // ---- A name needing quotes gets them, and the script re-parses. --------
    {
        const std::string smt = dumpWithVar("x(1)");
        VERIFY(has(smt, "|x(1)|"));
        // The unquoted form must not appear anywhere -- not in the declaration
        // and not in the assertion, which is a separate print site.
        VERIFY(!has(smt, "(declare-fun x(1) "));
        ParserPtr r = newParser();
        VERIFY(r->parseStr(smt));
    }
    {
        // A leading digit is the other way a simple symbol can be invalid.
        const std::string smt = dumpWithVar("1st");
        VERIFY(has(smt, "|1st|"));
        ParserPtr r = newParser();
        VERIFY(r->parseStr(smt));
    }
    {
        // Whitespace, which cannot appear in a simple symbol at all.
        const std::string smt = dumpWithVar("a b");
        VERIFY(has(smt, "|a b|"));
        ParserPtr r = newParser();
        VERIFY(r->parseStr(smt));
    }

    // ---- An ordinary name is left ALONE. -----------------------------------
    //
    // The fix must not quote everything: `|x|` and `x` are the same symbol, so
    // quoting unnecessarily would be correct and unreadable, and it would churn
    // the output of every existing script.
    {
        const std::string smt = dumpWithVar("x");
        VERIFY(has(smt, "(declare-fun x () Int)"));
        VERIFY(!has(smt, "|x|"));
    }
    {
        // The punctuation SMT-LIB does allow in a simple symbol stays bare.
        const std::string smt = dumpWithVar("a-b_c.d?e");
        VERIFY(has(smt, "(declare-fun a-b_c.d?e () Int)"));
        VERIFY(!has(smt, "|a-b_c.d?e|"));
    }

    // ---- A name that arrives quoted is not quoted twice. -------------------
    {
        ParserPtr p = newParser();
        VERIFY(p->parseStr("(declare-fun |y z| () Int)\n(assert (> |y z| 0))\n"));
        const std::string smt = p->dumpSMT2();
        VERIFY(has(smt, "|y z|"));
        VERIFY(!has(smt, "||y z||"));
        ParserPtr r = newParser();
        VERIFY(r->parseStr(smt));
    }

    // Function declarations, applications, definitions and binders must use
    // the same legal spelling. Check text as well as reparsing: the reader
    // accepts some bare names that a conforming SMT-LIB reader rejects.
    for (const std::string name : {"f(x)", "f x", "1fun", "plain", "|f x|"}) {
        ParserPtr p = newParser();
        const auto integer = p->mkIntSort();
        const std::string printed = smtSymbol(name);
        const auto f = p->mkFuncDec(name, {integer}, integer);
        VERIFY(has(dumpFuncDec(f), "(declare-fun " + printed + " (Int) Int)"));
        std::ostringstream streamed;
        dumpFuncDec(f, streamed);
        VERIFY(streamed.str() == dumpFuncDec(f));
        const auto application = p->mkApplyUF(integer, name, {p->mkConstInt(3)});
        // DAGNode::toString is the raw node-name accessor; Parser::toString
        // and dumpSMTLIB2 are the complete SMT expression serialization APIs.
        VERIFY(application->getName() == name);
        VERIFY(p->toString(application) == "(" + printed + " 3)");
        VERIFY(dumpSMTLIB2(application) == "(" + printed + " 3)");
        VERIFY(p->assert(p->mkEq(application, p->mkConstInt(4))));
        VERIFY(newParser()->parseStr(p->dumpSMT2()));
    }
    {
        // Nullary calls have no application parentheses, but their symbol
        // spelling must still match the declaration/definition.
        ParserPtr p = newParser();
        const auto integer = p->mkIntSort();
        const auto declared = p->mkFuncDec("zero args", {}, integer);
        const auto defined = p->mkFuncDef("zero(def)", {}, integer, p->mkConstInt(1));
        const auto recursive = p->mkFuncRec("zero rec", {}, integer, p->mkConstInt(2));
        VERIFY(dumpFuncDec(declared) == "(declare-fun |zero args| () Int)");
        VERIFY(p->toString(p->mkApplyUF(integer, "zero args", {})) == "|zero args|");
        VERIFY(p->toString(p->mkApplyFunc(defined, {})) == "|zero(def)|");
        VERIFY(p->toString(p->mkApplyRecFunc(recursive, {})) == "|zero rec|");
        VERIFY(newParser()->parseStr(p->dumpSMT2()));
    }
    {
        ParserPtr p = newParser();
        const auto integer = p->mkIntSort();
        const auto x = p->mkFunParamVar(integer, "arg one");
        const auto y = p->mkFunParamVar(integer, "arg(two)");
        const auto f = p->mkFuncDef("fun name", {x, y}, integer, p->mkAdd(x, y));
        const std::string definition = dumpFuncDef(f);
        VERIFY(has(definition, "(define-fun |fun name| ((|arg one| Int) (|arg(two)| Int)) Int"));
        VERIFY(has(definition, "|arg one|"));
        VERIFY(p->toString(p->mkApplyFunc(f, {p->mkConstInt(1), p->mkConstInt(2)}))
               == "(|fun name| 1 2)");
        VERIFY(newParser()->parseStr(definition));
        const auto rec = p->mkFuncRec("rec name", {x}, integer, x);
        VERIFY(has(dumpFuncRec(rec), "(define-fun-rec |rec name| ((|arg one| Int)) Int |arg one|)"));
        VERIFY(p->toString(p->mkApplyRecFunc(rec, {p->mkConstInt(2)})) == "(|rec name| 2)");
        VERIFY(newParser()->parseStr(dumpFuncRec(rec)));
        VERIFY(newParser()->parseStr(dumpFuncsRec({rec})));
    }
    {
        ParserPtr p = newParser();
        const auto x = p->mkQuantVar("bound x", p->mkIntSort());
        const auto y = p->mkQuantVar("bound(y)", p->mkIntSort());
        const auto relation = p->mkLt(x, y);
        // The C++ builders take the body first, followed by bound variables;
        // this differs from the surface syntax and the Python convenience API.
        for (const auto term : {p->mkForall({relation, x, y}), p->mkExists({relation, x, y})}) {
            VERIFY(term->getChild(0) == relation);
            VERIFY(term->getChild(1) == x && term->getChild(2) == y);
            const std::string text = p->toString(term);
            VERIFY(has(text, "((|bound x| Int) (|bound(y)| Int))"));
            VERIFY(has(text, "(< |bound x| |bound(y)|)"));
            VERIFY(newParser()->parseStr("(assert " + text + ")"));
        }
    }

    std::cout << "All symbol-quoting tests passed." << std::endl;
    return 0;
}
