// The four MiniZinc gaps the format authors' own examples found.
//
// libminizinc's `tests/spec/examples/` was 0 of 16, and every one of them
// failed at LINE 1, COLUMN 1, on the same character. A uniform failure at the
// very first token is never a semantic gap: those files open with a `/* ... */`
// licence header and this lexer knew only `%`. Fixing that moved the whole
// failure distribution deeper and made the next three visible -- parameters,
// `->`, and `include`.
//
// Each is tested for its SEMANTICS rather than its shape. The builders fold
// constants and reorder commutative operands (CLAUDE.md invariant 2), so
// asserting on emitted text would pin something the caller does not choose.

#include "somtparser/translation/translate.h"
#include "somtparser/languages/register_all.h"
#include "somtparser/frontend/parser.h"

#include <cassert>
#include <iostream>
#include <string>

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

bool has(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

Translation run(const std::string& src, const std::string& profile = "default") {
    Lang::SourceUnit u;
    u.main_path = "t.mzn";
    u.display_name = "t.mzn";
    u.inline_source = src;
    TranslateOptions opts;
    opts.language_id = "minizinc";
    // `default` deliberately has no decomposition for a global constraint, so
    // a model containing one needs a profile that names an encoding for it --
    // which is the point of the profiles, not a quirk of this test.
    opts.profile_id = profile;
    return translate(u, opts);
}

/** The first ERROR, not the first diagnostic. A frontend may emit notes before
 *  it gives up -- the annotation note is one -- and grading all()[0] would grade
 *  the wrong message. */
std::string firstError(const Translation& t) {
    for (const Diagnostic& d : t.diagnostics().all()) {
        if (d.severity == Severity::ERROR) { return d.message; }
    }
    assert(false && "no error recorded");
    return "";
}

int firstErrorLine(const Translation& t) {
    for (const Diagnostic& d : t.diagnostics().all()) {
        if (d.severity == Severity::ERROR) { return d.loc.line; }
    }
    assert(false && "no error recorded");
    return 0;
}

} // namespace

int main() {
    std::cout << "======= MiniZinc: gaps the upstream corpus found =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    // ---- 1. Block comments ------------------------------------------------
    {
        // The header shape every libminizinc example opens with.
        const Translation t = run(
            "/* This model is licensed under...\n"
            " * ...several lines...\n"
            " */\n"
            "var 1..10: x;\n"
            "constraint x > 7;\n"
            "solve satisfy;\n");
        assert(t.ok());
        // Not merely "it parsed": the constraint after the comment must have
        // survived. A lexer that swallowed to end of file would also report ok.
        assert(has(t.toSmt2(), "assert"));
    }
    {
        // `/*` inside a line comment is not a block comment...
        const Translation t = run("% /* not a comment opener\n"
                                  "var 1..10: x;\nsolve satisfy;\n");
        assert(t.ok());
    }
    {
        // ...and a block comment ends at the FIRST `*/`, because MiniZinc's do
        // not nest. If they nested, the `solve` item here would be swallowed
        // and the model would be rejected for having none.
        const Translation t = run("/* a /* b */ var 1..10: x;\nsolve satisfy;\n");
        assert(t.ok());
    }
    {
        // Unterminated. This is the one that matters: without a check, the
        // token stream simply ENDS, the parser sees a finished model, and a
        // truncated file translates as a smaller one and reports success.
        const Translation t = run("var 1..10: x;\nsolve satisfy;\n"
                                  "/* constraint x > 7;\n");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
        assert(has(firstError(t), "unterminated block comment"));
        // Reported against the OPENING location -- line 3, where the `/*` is --
        // and not at end of file, which is where it was noticed.
        assert(firstErrorLine(t) == 3);
    }

    // ---- 2. Parameters ----------------------------------------------------
    {
        // A parameter is a compile-time constant, so it must be usable where an
        // index set needs a NUMBER.
        const Translation t = run("int: n = 3;\n"
                                  "array[1..n] of var 1..9: a;\n"
                                  "constraint a[3] > 5;\n"
                                  "solve satisfy;\n");
        assert(t.ok());
        // n must not appear as a variable of the model: the solver is not being
        // asked to choose it. The array is the only declaration.
        assert(t.report().stats().num_vars == 1);
        // And the index set really is 1..3 -- the parameter's VALUE reached the
        // bound constraints, which is what parsing it at declaration time buys.
        const std::string smt = t.toSmt2();
        assert(has(smt, "(select a 3)"));
        assert(!has(smt, "(select a 4)"));
    }
    {
        // Arithmetic over other parameters, including MiniZinc's `div`, which
        // TRUNCATES toward zero.
        const Translation t = run("int: m = 4;\nint: n = m*m;\n"
                                  "array[1..n] of var 0..1: a;\n"
                                  "solve satisfy;\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(select a 16)"));
        assert(!has(smt, "(select a 17)"));
    }
    {
        // The convention is the language's and not the target's: `-7 div 2` is
        // -3 truncating and -4 Euclidean, and the array below has 3 elements
        // only under the first reading.
        const Translation t = run("int: k = (0 - 7) div 2;\nint: u = 0 - 1;\n"
                                  "array[k..u] of var 0..1: a;\n"
                                  "solve satisfy;\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(select a (- 3))"));          // truncating: -3, -2, -1
        assert(!has(smt, "(select a (- 4))"));         // Euclidean would start here
    }
    {
        // An unbound parameter is refused, not defaulted: its value comes from
        // a .dzn, and a model without it is unanswerable rather than smaller.
        const Translation t = run("int: n;\narray[1..n] of var 0..1: a;\nsolve satisfy;\n");
        assert(!t.ok());
        assert(has(firstError(t), ".dzn"));
    }
    {
        // Division by zero in a parameter is an error and not a silent value.
        const Translation t = run("int: z = 0;\nint: k = 1 div z;\nsolve satisfy;\n");
        assert(!t.ok());
        assert(has(firstError(t), "division by zero"));
    }
    {
        // Overflow is refused for the reason an oversized literal is: wrapping
        // would make `array[1..n]` a different array with no diagnostic.
        const Translation t = run("int: a = 4611686018427387904;\n"
                                  "int: b = a * 4;\nsolve satisfy;\n");
        assert(!t.ok());
        assert(has(firstError(t), "overflows"));
    }
    {
        // A parameter does not shadow, and does not get shadowed.
        const Translation t = run("int: n = 3;\nvar 1..9: n;\nsolve satisfy;\n");
        assert(!t.ok());
        assert(has(firstError(t), "already declared"));
    }

    // ---- 3. Implication ---------------------------------------------------
    {
        // `->` binds LOOSER than the comparison, so this is `b -> (x <= 4)`.
        // The lexer already produced the token and nothing consumed it, so the
        // ordinary way to write a half-reified constraint failed with
        // "expected ';'".
        const Translation t = run("var 1..10: x;\nvar bool: b;\n"
                                  "constraint b -> x <= 4;\nsolve satisfy;\n");
        assert(t.ok());
        // Semantics, not shape: b true and x = 9 must be excluded, and b false
        // with x = 9 must not be.
        ParserPtr p = newParser();
        assert(p->parseStr(t.toSmt2()));
    }
    {
        const Translation t = run("var bool: a;\nvar bool: b;\n"
                                  "constraint a <-> b;\nsolve satisfy;\n");
        assert(t.ok());
    }
    {
        // A chain is refused rather than guessed: `a -> b -> c` is a different
        // formula under each associativity, and this subset does not assume one.
        const Translation t = run("var bool: a;\nvar bool: b;\nvar bool: c;\n"
                                  "constraint a -> b -> c;\nsolve satisfy;\n");
        assert(!t.ok());
        assert(has(firstError(t), "parentheses"));
    }
    {
        // ...and parenthesising is accepted, so the refusal is actionable.
        const Translation t = run("var bool: a;\nvar bool: b;\nvar bool: c;\n"
                                  "constraint a -> (b -> c);\nsolve satisfy;\n");
        assert(t.ok());
    }
    {
        // `<-` is deliberately NOT a token: adding it would make `x <-3` lex as
        // `x <- 3` and silently turn a comparison with a negative literal into a
        // reverse implication. So this must be read as a comparison.
        const Translation t = run("var -10..10: x;\nconstraint x <-3;\nsolve satisfy;\n");
        assert(t.ok());
    }

    // ---- 4. include -------------------------------------------------------
    {
        // A standard-library include is skipped: this frontend recognises
        // global constraints by NAME and never uses those definitions, so the
        // skip cannot turn an error into a wrong answer.
        const Translation t = run("include \"globals.mzn\";\n"
                                  "array[1..3] of var 1..3: a;\n"
                                  "constraint alldifferent(a);\nsolve satisfy;\n",
                                  "ground");
        assert(t.ok());
    }
    {
        // And skipping it really is harmless in the other direction: a global
        // this frontend does NOT know still fails, at its use site, by name --
        // the include does not make it available.
        const Translation t = run("include \"globals.mzn\";\n"
                                  "array[1..3] of var 1..3: a;\n"
                                  "constraint no_such_global(a);\nsolve satisfy;\n");
        assert(!t.ok());
        assert(has(firstError(t), "no_such_global"));
    }
    {
        // A MODEL include is READ -- `battleships10.mzn` is nine lines of data
        // plus `include "battleships.mzn.model";`, and translating the data
        // alone would report success for a different question. This source is
        // inline, so there is no directory to resolve against and the file is
        // not there: the refusal is now an I/O one NAMING THE FILE, which is
        // the actionable message. It used to be "this frontend reads one file".
        const Translation t = run("include \"battleships.mzn.model\";\n"
                                  "int: n = 3;\nsolve satisfy;\n");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_IO);
        assert(has(firstError(t), "battleships.mzn.model"));
    }
    {
        // The stdlib list still fails CLOSED: an unlisted name is not assumed
        // to be library content and skipped, it is read -- and reported when it
        // is not there rather than passed over as if it had been.
        const Translation t = run("include \"probably_a_library.mzn\";\nsolve satisfy;\n");
        assert(!t.ok());
        assert(has(firstError(t), "probably_a_library.mzn"));
    }
    {
        // A missing quote does not swallow the rest of the line as a file name.
        const Translation t = run("include globals.mzn;\nsolve satisfy;\n");
        assert(!t.ok());
        assert(has(firstError(t), "quoted file name"));
    }

    std::cout << "All MiniZinc upstream-gap tests passed." << std::endl;
    return 0;
}
