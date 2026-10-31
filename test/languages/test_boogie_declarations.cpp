// What Boogie's own Test/textbook needed, and this frontend did not have.
//
// The first run over that corpus was 0 of 6, and the failures were not the ones
// the coverage table predicted. Four of them are here; the fifth -- block
// comments -- is the same shape as MiniZinc's and is checked alongside.
//
// The order-independence case is the one that matters most: a frontend that
// requires declare-before-use REJECTS A LEGAL PROGRAM, which is a different
// class of wrong from declining a construct.

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

Translation run(const std::string& src) {
    Lang::SourceUnit u;
    u.main_path = "t.bpl";
    u.display_name = "t.bpl";
    u.inline_source = src;
    TranslateOptions opts;
    opts.language_id = "boogie";
    return translate(u, opts);
}

std::string firstError(const Translation& t) {
    for (const Diagnostic& d : t.diagnostics().all()) {
        if (d.severity == Severity::ERROR) { return d.message; }
    }
    assert(false && "no error recorded");
    return "";
}

/** A minimal procedure, so the model has something to verify. */
const char* kProc = "procedure P(n: int) returns (u: int)\n"
                    "  ensures u >= 0;\n{\n  u := 1;\n}\n";

} // namespace

int main() {
    std::cout << "======= Boogie: declarations, quantifiers, grouping =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    // ---- 1. Declarations are NOT ordered ----------------------------------
    {
        // `Factorial` used on line 2, declared on line 6. This is what
        // TuringFactorial.bpl does, and it is legal Boogie -- refusing it is
        // rejecting a correct program, not declining a construct.
        const Translation t = run(
            "procedure P(n: int) returns (u: int)\n"
            "  ensures u == Factorial(n);\n{\n  u := Factorial(n);\n}\n"
            "function Factorial(int): int;\n");
        assert(t.ok());
        assert(has(t.toSmt2(), "Factorial"));
    }
    {
        // ...and a genuinely undeclared symbol is still refused, so the two
        // passes did not turn the check off.
        const Translation t = run(
            "procedure P(n: int) returns (u: int)\n"
            "  ensures u == NoSuch(n);\n{\n  u := 1;\n}\n");
        assert(!t.ok());
        assert(has(firstError(t), "NoSuch"));
    }

    {
        // A `uses { ... }` block whose axioms name a function declared LATER.
        // This is TuringFactorial.bpl's shape -- `Factorial`'s block calls
        // `Factorial_Aux`, five lines further down -- and it is why the blocks
        // are recorded during the declaration pass and read after it rather
        // than parsed where they appear.
        //
        // The axioms are read, not skipped: Boogie includes them when the
        // symbol is used, which is a performance device, so including them
        // unconditionally cannot change the answer while dropping them would.
        const Translation t = run(
            std::string("function F(int): int uses {\n"
                        "  axiom F(0) == 1;\n"
                        "  axiom (forall n: int :: 1 <= n ==> F(n) == n * G(n-1));\n"
                        "}\n"
                        "function G(int): int uses { axiom G(0) == 1; }\n")
            + kProc);
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // Both defining axioms landed, and the forward reference resolved.
        assert(has(smt, "(declare-fun F (Int) Int)"));
        assert(has(smt, "(declare-fun G (Int) Int)"));
        assert(has(smt, "forall"));
        ParserPtr p = newParser();
        assert(p->parseStr(smt));
    }
    {
        // A `uses` block ends the declaration -- there is no trailing `;` --
        // and the item after it must still be read.
        const Translation t = run(
            std::string("const N: int uses {\n  axiom 0 <= N;\n}\n")
            + "const M: int;\n" + kProc);
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(declare-fun N () Int)"));
        assert(has(smt, "(declare-fun M () Int)"));
    }

    // ---- 2. const ----------------------------------------------------------
    {
        const Translation t = run(std::string("const K: int;\n") + kProc
                                  + "axiom K > 0;\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(declare-fun K () Int)"));
        // A constant is never assigned, so it must NOT be versioned: an `@2`
        // here would mean the axioms refer to a version nothing declares.
        assert(!has(smt, "K@"));
    }
    {
        // `unique` is a distinctness constraint, and dropping it would admit
        // models the source excludes.
        const Translation t = run(std::string("const unique a, b, c: int;\n") + kProc);
        assert(t.ok());
        assert(has(t.toSmt2(), "distinct"));
    }
    {
        // Boogie's uniqueness is over ALL unique constants of a type, not over
        // one declaration. The accumulated relation must therefore include
        // both groups rather than enforcing distinctness only within each one.
        const Translation t = run(std::string("const unique a, b: int;\n")
                                  + "const unique c, d: int;\n" + kProc);
        assert(t.ok());
        assert(has(t.toSmt2(), "(distinct a b c d)"));
    }

    // ---- 3. function, declared and defined ---------------------------------
    {
        // Both spellings of an uninterpreted function.
        const Translation t = run(std::string("function f(int, int) returns (int);\n")
                                  + "function g(x: int): int;\n" + kProc
                                  + "axiom f(1, 2) == g(3);\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(declare-fun f (Int Int) Int)"));
        assert(has(smt, "(declare-fun g (Int) Int)"));
    }
    {
        // A BODY becomes a declaration plus a defining axiom, not an inlining.
        // Both are exact; the axiom form survives a recursive definition, which
        // Boogie allows and an inliner cannot.
        const Translation t = run(
            std::string("function abs(x: int): int { if 0 <= x then x else -x }\n")
            + kProc + "axiom abs(-3) == 3;\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "forall"));
        assert(has(smt, "ite"));
        // `abs` is a reserved SMT-LIB name, so the lowering renames it -- and
        // the declaration and the axiom must agree on the new name.
        ParserPtr p = newParser();
        assert(p->parseStr(smt));
    }
    {
        // A recursive definition is fine, because it is an axiom.
        const Translation t = run(
            std::string("function fact(n: int): int { if n <= 0 then 1 else n * fact(n-1) }\n")
            + kProc);
        assert(t.ok());
    }
    {
        // A body needs named parameters to refer to.
        const Translation t = run(std::string("function h(int): int { 1 }\n") + kProc);
        assert(!t.ok());
        assert(has(firstError(t), "unnamed"));
    }
    {
        const Translation t = run(std::string("function f(int): int;\n") + kProc
                                  + "axiom f(1, 2) == 0;\n");
        assert(!t.ok());
        assert(has(firstError(t), "takes 1 argument"));
    }

    // ---- 4. Quantifiers, triggers and attributes ---------------------------
    {
        const Translation t = run(std::string("function f(int): int;\n") + kProc
                                  + "axiom (forall j: int :: f(j) >= 0);\n"
                                  + "axiom (exists k: int :: f(k) == 1);\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "forall") && has(smt, "exists"));
    }
    {
        // A TRIGGER is `{ f(j) }` -- braces with no colon -- and an attribute is
        // `{: ... }`. Neither constrains the model: a trigger says when to
        // instantiate, which changes proof time and not which models exist.
        const Translation t = run(
            std::string("function f(int): int;\n") + kProc
            + "axiom {:include_dep} (forall j: int :: {f(j)} f(j) >= 0);\n");
        assert(t.ok());
        assert(has(t.toSmt2(), "forall"));
    }
    {
        // **The binder is alpha-renamed even with nothing visible to collide
        // with.** DivMod.bpl puts its axioms BEFORE the procedure that declares
        // `a` and `b`, so at the moment the binder is built there is no clash;
        // it appears only when typeCheck sees the finished model. Renaming on
        // collision would have to depend on declarations not yet read.
        const Translation t = run(
            std::string("function f(int, int): int;\n")
            + "axiom (forall a, b: int :: f(a, b) >= 0);\n"
            + "procedure T(a, b: int) returns (q: int)\n  ensures q >= 0;\n"
              "{\n  q := f(a, b);\n}\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        ParserPtr p = newParser();
        assert(p->parseStr(smt));
        // The source name survives as a suffix, so the script still reads like
        // the input.
        assert(has(smt, "!a") && has(smt, "!b"));
    }

    // ---- 5. Grouped names --------------------------------------------------
    {
        // `var qq, rr: int`, `procedure T(a,b: int) returns (q,r: int)`, and
        // `function mode(a, b: int): int` all group names that share a type.
        // Reading one name per type failed with "expected ':', found ','" on
        // nearly every real file.
        const Translation t = run(
            "function mode(a, b: int): int;\n"
            "procedure T(a, b: int) returns (q, r: int)\n"
            "  ensures q >= 0;\n"
            "{\n  var qq, rr: int;\n  qq := mode(a, b);\n  q := qq;\n  r := 0;\n}\n");
        assert(t.ok());
    }
    {
        // `function f(int, int): int` is bare types, not a name group -- the
        // difference is whether a `:` or the `)` comes first, and only real
        // lookahead can tell.
        const Translation t = run(std::string("function f(int, int): int;\n") + kProc
                                  + "axiom f(1, 2) == 0;\n");
        assert(t.ok());
        assert(has(t.toSmt2(), "(declare-fun f (Int Int) Int)"));
    }
    {
        // Parallel assignment reads EVERY right-hand side before updating any
        // target, which is what makes `r, u := u, r` a swap.
        const Translation t = run(
            "procedure P() returns (r: int, u: int)\n  ensures true;\n"
            "{\n  r := 1;\n  u := 2;\n  r, u := u, r;\n}\n");
        assert(t.ok());
        ParserPtr p = newParser();
        assert(p->parseStr(t.toSmt2()));
    }
    {
        const Translation t = run(
            "procedure P() returns (r: int, u: int)\n  ensures true;\n"
            "{\n  r, u := 1;\n}\n");
        assert(!t.ok());
        assert(has(firstError(t), "target(s)"));
    }

    // ---- 6. Block comments, and the refusals that stayed refusals ----------
    {
        // Boogie has both comment syntaxes and this lexer knew only `//` --
        // the same shape as MiniZinc's missing `/* */`.
        const Translation t = run(std::string("/* a header\n * comment\n */\n") + kProc);
        assert(t.ok());
    }
    {
        // A label used to be refused BY NAME; labels are supported with the
        // CFG work (2026-09-20) -- a label with no goto into it is a plain
        // one-edge join, and the flow splits and continues.
        const Translation t = run(
            "procedure P() returns (u: int)\n  ensures true;\n"
            "{\n  u := 1;\nTOP:\n  u := 2;\n}\n");
        assert(t.ok());
        ParserPtr reader = newParser();
        assert(reader->parseStr(t.toSmt2()));
    }
    {
        // A one-index map type is supported now -- it is an SMT-LIB array, and
        // this case used to assert the refusal. What still refuses is the
        // MULTI-index form, which is a currying-or-tupling choice rather than
        // a missing feature.
        const Translation t = run(std::string("var a: [int]int;\n") + kProc);
        assert(t.ok());
        assert(has(t.toSmt2(), "(Array Int Int)"));

        const Translation m = run(std::string("var a: [int, int]int;\n") + kProc);
        assert(!m.ok());
        assert(has(firstError(m), "multi-index map"));
    }

    std::cout << "All Boogie declaration tests passed." << std::endl;
    return 0;
}
