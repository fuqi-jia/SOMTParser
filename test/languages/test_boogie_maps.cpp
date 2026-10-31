// Boogie maps, and `old`.
//
// A Boogie map is a TOTAL function from its index type to its value type, and
// so is an SMT-LIB array. `[int]int` therefore crosses as `(Array Int Int)`
// with nothing lost -- both are defined at every index, `m[i]` is `select` and
// `m[i] := v` is `store`. It records no fidelity loss because there is none.
//
// `old(e)` is e in the pre-state, and under this frontend's SSA versioning that
// is a name it already has: assignments mint `x@2`, `x@3`, ... and the
// unversioned `x` never stops meaning the entry value. What it cannot do is
// emit `x`, because finalise() rewrites every program variable to its FINAL
// version -- that is what makes an `ensures` mean the post-state. So `old(x)`
// gets an entry alias tied to the unversioned name, and the tie is
// timing-independent for the same reason it is correct. Which identifiers get
// an alias is This is Boogie 2 §4.3's rule: old is the identity on every leaf
// that is not a global variable, so a local or an out-parameter keeps its
// current version, and only a mutable global mints an alias.
//
// Together these were the whole of the "map types are Boogie's heap" objection.
// What remains in the upstream corpus after them is CONTROL FLOW -- `while`,
// `goto`, `if`, labels -- which is one decision (docs/languages/boogie.md
// §4.3), not five separate gaps.

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

} // namespace

int main() {
    std::cout << "======= Boogie: maps and old =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    // ---- A one-index map is an array. --------------------------------------
    {
        const Translation t = run(
            "procedure P(i: int) returns (r: int)\n  ensures r >= 0;\n"
            "{\n  var a: [int]int;\n  a[i] := 5;\n  r := a[i];\n}\n");
        if (!t.ok()) {
            std::cout << "  map refused: " << firstError(t) << "\n";
            assert(false);
        }
        const std::string smt = t.toSmt2();
        assert(has(smt, "(Array Int Int)"));
        // A write is a store of the WHOLE map, which is what keeps the SSA
        // versioning meaningful: `a[i] := 5` produces a new map, not a mutated
        // cell that nothing records.
        assert(has(smt, "store"));
        assert(has(smt, "select"));
        ParserPtr p = newParser();
        assert(p->parseStr(smt));
    }
    {
        // Bool values and a Bool-indexed map, so the two positions are not
        // silently assumed to be Int.
        const Translation t = run(
            "procedure P() returns (r: bool)\n  ensures true;\n"
            "{\n  var m: [bool]bool;\n  m[true] := false;\n  r := m[true];\n}\n");
        assert(t.ok());
        assert(has(t.toSmt2(), "(Array Bool Bool)"));
    }
    {
        // A map of maps: `m[i][j]` is two selects, and `m[i][j] := v` rebuilds
        // the inner map and stores THAT back -- an assignment to a cell of a
        // nested map is an assignment to the outer map.
        const Translation t = run(
            "procedure P(i: int, j: int) returns (r: int)\n  ensures true;\n"
            "{\n  var m: [int][int]int;\n  m[i][j] := 7;\n  r := m[i][j];\n}\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(Array Int (Array Int Int))"));
        ParserPtr p = newParser();
        assert(p->parseStr(smt));
    }
    {
        // A map as a procedure parameter and in a quantifier, which is what
        // every real specification does.
        const Translation t = run(
            "procedure P(a: [int]int, n: int) returns (r: int)\n"
            "  requires (forall k: int :: 0 <= k && k < n ==> a[k] >= 0);\n"
            "  ensures r >= 0;\n{\n  r := 0;\n}\n");
        assert(t.ok());
        assert(has(t.toSmt2(), "forall"));
    }

    // ---- Multi-index maps stay refused, by name. ---------------------------
    {
        // Expressible -- curry it, or index by a tuple -- and the two choices
        // say different things about what the map IS, so neither is taken
        // silently.
        const Translation t = run(
            "procedure P() returns (r: int)\n  ensures true;\n"
            "{\n  var m: [int, int]int;\n  r := 0;\n}\n");
        assert(!t.ok());
        assert(has(firstError(t), "multi-index map"));
    }
    {
        // ...and the expression grammar must not let one in after the type
        // grammar declined it.
        const Translation t = run(
            "procedure P(i: int) returns (r: int)\n  ensures true;\n"
            "{\n  var m: [int]int;\n  r := m[i, i];\n}\n");
        assert(!t.ok());
        assert(has(firstError(t), "multi-index map"));
    }
    {
        // Indexing something that is not a map is a sort error naming it, not
        // a parse error about a bracket.
        const Translation t = run(
            "procedure P(i: int) returns (r: int)\n  ensures true;\n"
            "{\n  var x: int;\n  x := 1;\n  r := x[i];\n}\n");
        assert(!t.ok());
        assert(has(firstError(t), "not a map"));
    }

    // ---- old ---------------------------------------------------------------
    {
        // The case the whole alias exists for: an `ensures` mentioning both
        // states of a GLOBAL. Without the alias the postcondition would talk
        // about the final `g` twice and be trivially true. old() is the
        // identity on non-globals (This is Boogie 2 §4.3), so only a mutable
        // global gets an entry alias.
        const Translation t = run(
            "var g: int;\n"
            "procedure P() returns (r: int)\n  modifies g;\n"
            "  ensures g == old(g) + 1;\n{\n  g := g + 1;\n  r := 0;\n}\n");
        if (!t.ok()) {
            std::cout << "  old refused: " << firstError(t) << "\n";
            assert(false);
        }
        const std::string smt = t.toSmt2();
        assert(has(smt, "g@old"));
        ParserPtr p = newParser();
        assert(p->parseStr(smt));
    }
    {
        // `old` of a global MAP, and an index applied to the RESULT --
        // `old(a)[i]`, which is the shape Bubble.bpl's permutation
        // postcondition uses. The index is a suffix on an expression, not
        // part of a name.
        const Translation t = run(
            "var a: [int]int;\n"
            "procedure P(n: int) returns (r: int)\n  modifies a;\n"
            "  ensures true;\n"
            "{\n  var p: [int]int;\n"
            "  a[0] := 1;\n  assert a[0] == old(a)[0] || true;\n  r := 0;\n}\n");
        assert(t.ok());
        assert(has(t.toSmt2(), "a@old"));
    }
    {
        // old() is the IDENTITY on a non-global (This is Boogie 2 §4.3): for
        // an out-parameter or a local there is no entry alias at all, because
        // the pre-state value of `y` is just `y`.
        const Translation t = run(
            "procedure P() returns (y: int)\n"
            "  ensures y == old(y);\n{\n  y := 42;\n}\n");
        assert(t.ok());
        assert(!has(t.toSmt2(), "y@old"));
    }
    {
        // A constant has one value in both states, so `old(c)` is `c` and must
        // not mint an alias -- an alias here would be a second symbol nothing
        // ties to the first.
        const Translation t = run(
            "const K: int;\nprocedure P() returns (r: int)\n"
            "  ensures r == old(K);\n{\n  r := K;\n}\n");
        assert(t.ok());
        assert(!has(t.toSmt2(), "K@old"));
    }
    {
        // The alias is declared ONCE however many times `old(g)` appears.
        const Translation t = run(
            "var g: int;\n"
            "procedure P() returns (x: int)\n  modifies g;\n"
            "  ensures g == old(g) + 1;\n  ensures old(g) <= g;\n"
            "{\n  g := g + 1;\n  x := 0;\n}\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        std::size_t decls = 0;
        for (std::size_t i = smt.find("(declare-fun g@old"); i != std::string::npos;
             i = smt.find("(declare-fun g@old", i + 1)) {
            ++decls;
        }
        assert(decls == 1);
    }

    std::cout << "All Boogie map tests passed." << std::endl;
    return 0;
}
