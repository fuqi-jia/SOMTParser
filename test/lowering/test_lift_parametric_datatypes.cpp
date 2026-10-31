// Parametric datatypes, through the WHOLE pipeline.
//
// `test/regression/test_datatype_groups.cpp` covers the engine: `par` parses,
// applies and prints. This file covers the layer above it --
// `text -> Parser -> HIR -> Parser -> text` -- because the engine being right
// bought nothing while the lift dropped what it had read.
//
// It dropped two things, and each produced a different wrong answer:
//
//   * A datatype's ARITY and its parameter NAMES were not carried, so a
//     parametric declaration lifted and lowered as an arity-0 one: `(L 1)` came
//     back `(L 0)` with no `par`, which is a different declaration.
//   * An APPLIED datatype sort lost its arguments, so `(L Int)` became `L` and
//     every instance was the same sort. The selector's declared result then no
//     longer matched what the expression recorded, and the script failed as
//     `E_INTERNAL` -- a broken invariant, for a file that is correct.
//
// Four sites in the HIR layer had to learn that a datatype with a non-zero
// arity is a sort CONSTRUCTOR: `sameSort` compared by name, `toString` printed
// the name (so a diagnostic read "applied to L, not L"), the lift dropped the
// arguments, and the lowering resolved the constructor instead of instantiating
// it. That is the same fact D18 established for declared sorts, learned again.
//
// The property asserted here is TEXT EQUALITY of the round trip, which is the
// standing instrument for this layer -- a declaration that comes back with a
// different arity is a different declaration, and only comparing the text
// catches it.

#include "somtparser/translation/translate.h"
#include "somtparser/languages/register_all.h"
#include "somtparser/frontend/parser.h"

#include <iostream>
#include <string>

#include "test_helpers.h"

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

bool has(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

Translation lift(const std::string& script) {
    Lang::SourceUnit u;
    u.inline_source = script;
    u.display_name = "<test>";
    TranslateOptions opts;
    opts.language_id = "smtlib2";
    return translate(u, opts);
}

std::string firstError(const Translation& t) {
    for (const Diagnostic& d : t.diagnostics().all()) {
        if (d.severity == Severity::ERROR) { return d.message; }
    }
    return "<no error>";
}

} // namespace

int main() {
    std::cout << "======= parametric datatypes through the lift =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    const std::string kList =
        "(declare-datatypes ((L 1))"
        " ((par (X) ((nil) (cons (hd X) (tl (L X)))))))\n";

    // ---- The declaration survives the round trip. ---------------------------
    {
        const Translation t = lift(kList + "(declare-fun l () (L Int))\n"
                                           "(assert (> (hd l) 0))\n");
        if (!t.ok()) { std::cout << "  refused: " << firstError(t) << "\n"; VERIFY(false); }
        const std::string smt = t.toSmt2();
        // The arity, the `par`, and the parameter's own name.
        VERIFY(has(smt, "(L 1)"));
        VERIFY(has(smt, "par (X)"));
        VERIFY(has(smt, "(tl (L X))"));
        // The INSTANCE survives too. `(L Int)` coming back as `L` is what made
        // every instantiation the same sort.
        VERIFY(has(smt, "(declare-fun l () (L Int))"));
        // And the parameter is not ALSO declared globally. It is bound by the
        // `par`, so a `(declare-sort X 0)` beside it would be a name both
        // declared and bound -- not a conforming script, and the lowering
        // emitted exactly that until it knew which names were parameters.
        VERIFY(!has(smt, "declare-sort X"));
        ParserPtr p = newParser();
        VERIFY(p->parseStr(smt));
    }

    // ---- The selector's result is the INSTANCE's argument. ------------------
    {
        // `hd` is declared `L -> X`. Over an `(L Int)` it must yield Int, and
        // the typechecker has to substitute to know that: comparing the
        // declared `X` against the recorded `Int` reported E_INTERNAL, which is
        // the bucket for a broken invariant rather than for a gap.
        const Translation t = lift(kList + "(declare-fun l () (L Int))\n"
                                           "(assert (> (hd l) 0))\n");
        VERIFY(t.ok());
        for (const Diagnostic& d : t.diagnostics().all()) {
            VERIFY(d.code != ErrorCode::E_INTERNAL);
        }
    }
    {
        // A selector whose result is the datatype itself: `tl` of an `(L Int)`
        // is an `(L Int)`, so it can be selected from again.
        const Translation t = lift(kList + "(declare-fun l () (L Int))\n"
                                           "(assert (> (hd (tl l)) 0))\n");
        if (!t.ok()) { std::cout << "  refused: " << firstError(t) << "\n"; VERIFY(false); }
        ParserPtr p = newParser();
        VERIFY(p->parseStr(t.toSmt2()));
    }

    // ---- Two instances are two sorts. --------------------------------------
    {
        // The assertion that fails if the arguments are dropped anywhere in the
        // pipeline: with `(L Int)` and `(L Bool)` collapsed to `L`, this
        // translates, and it is a script the standard forbids.
        const Translation t = lift(kList + "(declare-fun a () (L Int))\n"
                                           "(declare-fun b () (L Bool))\n"
                                           "(assert (= a b))\n");
        VERIFY(!t.ok());
    }
    {
        // ...and both instances may coexist, each keeping its own argument.
        const Translation t = lift(kList + "(declare-fun a () (L Int))\n"
                                           "(declare-fun b () (L Bool))\n"
                                           "(assert (> (hd a) 0))\n"
                                           "(assert (hd b))\n");
        if (!t.ok()) { std::cout << "  refused: " << firstError(t) << "\n"; VERIFY(false); }
        const std::string smt = t.toSmt2();
        VERIFY(has(smt, "(L Int)"));
        VERIFY(has(smt, "(L Bool)"));
    }

    // ---- A non-parametric datatype is unchanged. ---------------------------
    {
        // No `par` for an arity-0 datatype, so every existing model's output is
        // byte-for-byte what it was.
        const Translation t = lift(
            "(declare-datatypes ((C 0)) (((r) (g) (b))))\n"
            "(declare-fun c () C)\n(assert (is-r c))\n");
        VERIFY(t.ok());
        const std::string smt = t.toSmt2();
        VERIFY(!has(smt, "par"));
        VERIFY(has(smt, "(C 0)"));
    }

    std::cout << "All parametric-datatype lift tests passed." << std::endl;
    return 0;
}
