// Essence' comprehension GUARDS, and `catchUndef`.
//
// Conjure writes a comprehension's `|` list as generators and conditions mixed
// freely -- `| q123 : int(1..2), q124 : int(1..2), q123 < q124`, and also
// `| 2 = q124`, a list with no generator in it at all. Every item was read as
// a generator, so both came out as `expected ':'`: a message naming
// punctuation for a construct the language defines, which files a missing
// feature under malformed input.
//
// The guard is evaluated at PARSE TIME and filters the tuple before the body
// is elaborated. That ordering is the whole correctness content of this
// feature, and it is what the third case below pins. A guard exists to exclude
// tuples, and the body need not be meaningful for the ones it excludes -- an
// index may leave its matrix's range there. Lowering the guard instead, as
// `guard -> body`, would elaborate the body for every tuple and refuse a file
// on a tuple the comprehension does not denote. Both readings agree on the
// models that translate either way, which is exactly why an example test
// cannot tell them apart and the out-of-range case can.
//
// `catchUndef(e, v)` totalizes numeric values using their local definition
// condition; partiality elsewhere closes at the nearest source Boolean node.

#include "distinct_scope.h"
#include "somtparser/translation/translate.h"
#include "somtparser/languages/register_all.h"

#include <iostream>
#include <string>

#include "test_helpers.h"

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

Translation run(const std::string& src) {
    Lang::SourceUnit u;
    u.main_path = "t.eprime";
    u.display_name = "t.eprime";
    u.inline_source = src;
    TranslateOptions opts;
    opts.language_id = "essence";
    return translate(u, opts);
}

bool has(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

std::size_t count(const std::string& hay, const std::string& needle) {
    std::size_t n = 0, p = 0;
    while ((p = hay.find(needle, p)) != std::string::npos) { ++n; p += needle.size(); }
    return n;
}

/** `=` is commutative and the builders canonicalize operand order -- the
 *  emitted form is `(= 1 (select m 1))`, constant first. */
bool hasEq(const std::string& text, const std::string& x, const std::string& y) {
    return has(text, "(= " + x + " " + y + ")") || has(text, "(= " + y + " " + x + ")");
}

std::string firstError(const Translation& t) {
    for (const Diagnostic& d : t.diagnostics().all()) {
        if (d.severity == Severity::ERROR) { return d.message; }
    }
    return "";
}

} // namespace

/** How many times `needle` occurs in `hay`. The matrix-generator cases assert a
 *  COUNT of conjuncts, because the failure they are written against -- missing
 *  part of the quantified space -- produces a script that is well formed,
 *  translates, and is satisfiable. Only the count distinguishes it. */
std::size_t countOf(const std::string& hay, const std::string& needle) {
    std::size_t n = 0;
    for (std::size_t at = hay.find(needle); at != std::string::npos;
         at = hay.find(needle, at + needle.size())) {
        ++n;
    }
    return n;
}

int main() {
    std::cout << "======= Essence' comprehension guards =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    {
        // A guard among the generators. Of the four tuples of
        // `q1, q2 : int(1..2)` only `q1 < q2` -- that is (1,2) -- survives, so
        // the fold has ONE conjunct and not four.
        const Translation t = run(
            "language ESSENCE' 1.0\n"
            "find m: matrix indexed by [int(1..2)] of int(0..9)\n"
            "such that\n"
            "    and([m[q1] < m[q2] | q1 : int(1..2), q2 : int(1..2), q1 < q2])\n");
        VERIFY(t.ok());
        const std::string smt = t.toSmt2();
        // `and` over one element is that element, so the surviving tuple's
        // comparison is emitted bare. `<` is not commutative, so its operand
        // order is the source's.
        VERIFY(count(smt, "(< (select m 1) (select m 2))") == 1);
        VERIFY(!has(smt, "(< (select m 2) (select m 1))"));
    }
    {
        // A list with NO generator -- every item is a guard. The names it
        // mentions are bound by the ENCLOSING comprehension, which is how
        // Conjure writes a conditional inside a fold.
        //
        // `or` on the outside on purpose: with `and` there, q=1 contributes
        // `false` and the whole model collapses to false -- correct, and it
        // would pin nothing about the guard.
        const Translation t = run(
            "language ESSENCE' 1.0\n"
            "find m: matrix indexed by [int(1..2)] of int(0..9)\n"
            "such that\n"
            "    or([or([m[q] = 7 | 2 = q]) | q : int(1..2)])\n");
        VERIFY(t.ok());
        // q=1 makes the inner list empty, and `or` over nothing is false;
        // q=2 keeps `m[2] = 7`. So exactly one equality reaches the script.
        const std::string smt = t.toSmt2();
        VERIFY(hasEq(smt, "7", "(select m 2)"));
        VERIFY(!hasEq(smt, "7", "(select m 1)"));
    }
    {
        // THE ORDERING CASE. `q : int(1..4)` ranges outside the matrix's
        // index domain, and the guard is what keeps the read inside it. The
        // body must never be elaborated for q = 3 or 4: doing so reads `m[3]`,
        // whose undefined comparisons would otherwise become false.
        //
        // A breakage probe belongs here rather than in prose: moving the guard
        // check after `expr(d)` makes this case, and only this case, fail.
        const Translation t = run(
            "language ESSENCE' 1.0\n"
            "find m: matrix indexed by [int(1..2)] of int(0..9)\n"
            "such that\n"
            "    and([m[q] = 1 | q : int(1..4), q <= 2])\n");
        VERIFY(t.ok());
        const std::string smt = t.toSmt2();
        VERIFY(hasEq(smt, "1", "(select m 1)"));
        VERIFY(hasEq(smt, "1", "(select m 2)"));
        // The point of the case. A declared element emits its own domain
        // bounds, so `select` alone appears either way -- these two indices
        // exist in NO form, which only holds if the body was never elaborated
        // for them.
        VERIFY(!has(smt, "(select m 3)"));
        VERIFY(!has(smt, "(select m 4)"));
    }
    {
        // Every tuple filtered out. `and` over nothing is true, so the model
        // is well-formed and says nothing -- not an error and not a dropped
        // constraint.
        const Translation t = run(
            "language ESSENCE' 1.0\n"
            "find m: matrix indexed by [int(1..2)] of int(0..9)\n"
            "such that\n"
            "    and([m[q] = 1 | q : int(1..2), q > 5])\n");
        VERIFY(t.ok());
        // The declared domain bounds remain; the BODY does not appear.
        const std::string smt = t.toSmt2();
        VERIFY(!hasEq(smt, "1", "(select m 1)"));
        VERIFY(!hasEq(smt, "1", "(select m 2)"));
    }
    {
        // A guard that is not a parse-time comparison is refused BY NAME, not
        // silently ignored -- ignoring it would admit tuples the source
        // excludes, which is a strictly larger solution set.
        const Translation t = run(
            "language ESSENCE' 1.0\n"
            "find m: matrix indexed by [int(1..2)] of int(0..9)\n"
            "find b: bool\n"
            "such that\n"
            "    and([m[q] = 1 | q : int(1..2), b])\n");
        VERIFY(!t.ok());
        VERIFY(has(firstError(t), "guard"));
    }

    std::cout << "======= catchUndef =======\n";
    {
        // Over a TOTAL expression it is the expression. The subscript is a
        // comprehension variable ranging inside the matrix's own index
        // domain, so nothing can be undefined and nothing is ever caught.
        const Translation t = run(
            "language ESSENCE' 1.0\n"
            "find m: matrix indexed by [int(1..2)] of int(0..9)\n"
            "such that\n"
            "    and([catchUndef(m[q], 0) = 1 | q : int(1..2)])\n");
        VERIFY(t.ok());
        const Translation plain = run(
            "language ESSENCE' 1.0\n"
            "find m: matrix indexed by [int(1..2)] of int(0..9)\n"
            "such that\n"
            "    and([m[q] = 1 | q : int(1..2)])\n");
        VERIFY(plain.ok());
        // Identity asserted as TEXT EQUALITY against the unwrapped model:
        // "is the expression" is a stronger claim than "mentions it", and only
        // this form rules out a fallback term surviving into the script.
        VERIFY(t.toSmt2() == plain.toSmt2());
    }
    {
        // Numeric undefinedness can be caught before it reaches a relation.
        const Translation t = run(
            "language ESSENCE' 1.0\n"
            "find x: int(0..9)\n"
            "find y: int(0..9)\n"
            "such that\n"
            "    catchUndef(x div y, 0) = 1\n");
        VERIFY(t.ok());
        VERIFY(has(t.toSmt2(), "ite"));
    }

    std::cout << "======= the matrix-literal fold =======\n";
    {
        // `and([e1, e2, e3; int(1..3)])` is a fold over a MATRIX LITERAL, not
        // a comprehension. Conjure writes both; they are told apart by which
        // separator is reached first at depth 0. Before this, the `,` was read
        // as the end of a one-element list and reported `expected ']'` -- a
        // message naming punctuation for a construct the language defines.
        const Translation t = run(
            "language ESSENCE' 1.0\n"
            "find m: matrix indexed by [int(1..3)] of int(0..9)\n"
            "such that\n"
            "    and([m[1] = 1, m[2] = 2, m[3] = 3; int(1..3)])\n");
        VERIFY(t.ok());
        const std::string smt = t.toSmt2();
        VERIFY(hasEq(smt, "1", "(select m 1)"));
        VERIFY(hasEq(smt, "2", "(select m 2)"));
        VERIFY(hasEq(smt, "3", "(select m 3)"));
    }
    {
        // The index domain is optional; the elements alone are a literal.
        const Translation t = run(
            "language ESSENCE' 1.0\n"
            "find m: matrix indexed by [int(1..2)] of int(0..9)\n"
            "such that\n"
            "    or([m[1] = 5, m[2] = 6])\n");
        VERIFY(t.ok());
        VERIFY(hasEq(t.toSmt2(), "5", "(select m 1)"));
        VERIFY(hasEq(t.toSmt2(), "6", "(select m 2)"));
    }
    {
        // A domain whose size disagrees with the element count describes a
        // DIFFERENT matrix. Refused, because folding the list anyway would be
        // a wrong answer rather than a parse error -- the shape is checked for
        // the same reason MiniZinc's `array2d` checks its own.
        const Translation t = run(
            "language ESSENCE' 1.0\n"
            "find m: matrix indexed by [int(1..3)] of int(0..9)\n"
            "such that\n"
            "    and([m[1] = 1, m[2] = 2, m[3] = 3; int(1..2)])\n");
        VERIFY(!t.ok());
        VERIFY(has(firstError(t), "indexed by a domain of size"));
    }
    {
        // A single element keeps working -- the path this branch generalises.
        const Translation t = run(
            "language ESSENCE' 1.0\n"
            "find m: matrix indexed by [int(1..2)] of int(0..9)\n"
            "such that\n"
            "    and([m[1] = 4])\n");
        VERIFY(t.ok());
        VERIFY(hasEq(t.toSmt2(), "4", "(select m 1)"));
    }

    std::cout << "======= alldifferent_except, <lex, flatten =======\n";
    {
        // `alldifferent_except(L, v)`: every element distinct EXCEPT those
        // equal to `v`, which may repeat. Emitted pairwise as
        // `a_i = v \/ a_j = v \/ a_i != a_j` -- the implication written
        // without negations. Pairwise rather than n-ary `distinct` because
        // the exemption is per-pair, and which elements are `v` is exactly
        // what the model leaves to the solver.
        const Translation t = run(
            "language ESSENCE' 1.0\n"
            "find m: matrix indexed by [int(1..3)] of int(0..9)\n"
            "such that\n"
            "    alldifferent_except([m[1], m[2], m[3]; int(1..3)], 0)\n");
        VERIFY(t.ok());
        const std::string smt = t.toSmt2();
        // Three pairs from three elements, and the exemption present in each.
        VERIFY(count(smt, "distinct") + count(smt, "(not (=") >= 3);
        VERIFY(hasEq(smt, "0", "(select m 1)"));
        VERIFY(hasEq(smt, "0", "(select m 3)"));
    }
    {
        // A one-element list has no pair, so it constrains nothing -- the
        // answer, not an error.
        const Translation t = run(
            "language ESSENCE' 1.0\n"
            "find m: matrix indexed by [int(1..3)] of int(0..9)\n"
            "such that\n"
            "    alldifferent_except([m[1]; int(1)], 0)\n");
        VERIFY(t.ok());
    }
    {
        // `<lex` over DECISION-VARIABLE elements, built as a term:
        // `a1 < b1 \/ (a1 = b1 /\ a2 < b2)`.
        const Translation t = run(
            "language ESSENCE' 1.0\n"
            "find m: matrix indexed by [int(1..4)] of int(0..9)\n"
            "such that\n"
            "    [m[1], m[2]; int(1..2)] <lex [m[3], m[4]; int(1..2)]\n");
        VERIFY(t.ok());
        const std::string smt = t.toSmt2();
        VERIFY(has(smt, "(< (select m 1) (select m 3))"));
        VERIFY(has(smt, "(< (select m 2) (select m 4))"));
        VERIFY(hasEq(smt, "(select m 1)", "(select m 3)"));
    }
    {
        // `<=lex` differs from `<lex` only on EQUAL lists, so the difference
        // shows at the last position and nowhere else.
        const Translation strict = run(
            "language ESSENCE' 1.0\n"
            "find m: matrix indexed by [int(1..2)] of int(0..9)\n"
            "such that [m[1]; int(1)] <lex [m[2]; int(1)]\n");
        const Translation loose = run(
            "language ESSENCE' 1.0\n"
            "find m: matrix indexed by [int(1..2)] of int(0..9)\n"
            "such that [m[1]; int(1)] <=lex [m[2]; int(1)]\n");
        VERIFY(strict.ok());
        VERIFY(loose.ok());
        VERIFY(has(strict.toSmt2(), "(< (select m 1) (select m 2))"));
        VERIFY(has(loose.toSmt2(), "(<= (select m 1) (select m 2))"));
    }
    {
        // `flatten` CONCATENATES its inner lists, and the inner lists need not
        // have the same length -- which is the whole reason Conjure reaches
        // for it. Two lists of 1 and 2 give a three-element operand, so the
        // comparison reaches `m[4]` on the right.
        const Translation t = run(
            "language ESSENCE' 1.0\n"
            "find m: matrix indexed by [int(1..8)] of int(0..9)\n"
            "such that\n"
            "    flatten([[m[1]; int(1)], [m[2], m[3]; int(1..2)]; int(1..2)])\n"
            "    <lex\n"
            "    flatten([[m[4]; int(1)], [m[5], m[6]; int(1..2)]; int(1..2)])\n");
        VERIFY(t.ok());
        const std::string smt = t.toSmt2();
        VERIFY(has(smt, "(< (select m 1) (select m 4))"));
        VERIFY(has(smt, "(< (select m 3) (select m 6))"));
    }
    {
        // Lists of different lengths are refused by name. Essence' orders a
        // shorter list before a longer one extending it; guessing that
        // tie-break would be a silent choice between two orderings, and no
        // file here writes one.
        const Translation t = run(
            "language ESSENCE' 1.0\n"
            "find m: matrix indexed by [int(1..3)] of int(0..9)\n"
            "such that [m[1], m[2]; int(1..2)] <lex [m[3]; int(1)]\n");
        VERIFY(!t.ok());
        VERIFY(has(firstError(t), "different lengths"));
    }
    {
        // `flatten` over something that is not a list of lists is refused:
        // flattening a scalar would silently change the result's length, and
        // the length is what the comparison walks.
        const Translation t = run(
            "language ESSENCE' 1.0\n"
            "find m: matrix indexed by [int(1..2)] of int(0..9)\n"
            "such that flatten([m[1], m[2]; int(1..2)]) <lex [m[1]; int(1)]\n");
        VERIFY(!t.ok());
        VERIFY(has(firstError(t), "list OF LISTS"));
    }

    std::cout << "======= allDiff over a list, / and %, min/max =======\n";
    {
        // `allDiff([...])` with the terms given explicitly. Emitted as the
        // LIST shape of `Hir::Global`, which `decompose-globals` tells apart
        // from the indexed shape by the first argument's SORT and encodes
        // as native distinct under both styles -- a list has no index set to quantify
        // over, so there is no second point on that axis to report.
        const Translation t = run(
            "language ESSENCE' 1.0\n"
            "find m: matrix indexed by [int(1..3)] of int(0..9)\n"
            "such that\n"
            "    allDiff([m[1], m[2], m[3]; int(1..3)])\n");
        VERIFY(t.ok());
        const std::string smt = t.toSmt2();
        VERIFY(SomtTest::hasDistinctArguments(t.parser(), {"(select m 1)", "(select m 2)", "(select m 3)"}));
    }
    {
        // A one-element list has no pair, which is the same answer the
        // indexed form gives for a one-cell matrix.
        const Translation t = run(
            "language ESSENCE' 1.0\n"
            "find m: matrix indexed by [int(1..2)] of int(0..9)\n"
            "such that allDiff([m[1]; int(1)])\n");
        VERIFY(t.ok());
    }
    {
        // `/` and `%` are the symbolic spellings of `div` and `mod`, and both
        // carry the same local definedness condition `r != 0`.
        const Translation slash = run(
            "language ESSENCE' 1.0\n"
            "find x: int(0..9)\n"
            "find y: int(1..9)\n"
            "such that x / y = 2\n");
        const Translation worded = run(
            "language ESSENCE' 1.0\n"
            "find x: int(0..9)\n"
            "find y: int(1..9)\n"
            "such that x div y = 2\n");
        VERIFY(slash.ok());
        VERIFY(worded.ok());
        // The spellings are the SAME operator, asserted as text equality
        // rather than by looking for a `div` in the output.
        VERIFY(slash.toSmt2() == worded.toSmt2());

        const Translation pct = run(
            "language ESSENCE' 1.0\n"
            "find x: int(0..9)\n"
            "find y: int(1..9)\n"
            "such that x % y = 2\n");
        const Translation modw = run(
            "language ESSENCE' 1.0\n"
            "find x: int(0..9)\n"
            "find y: int(1..9)\n"
            "such that x mod y = 2\n");
        VERIFY(pct.ok());
        VERIFY(modw.ok());
        VERIFY(pct.toSmt2() == modw.toSmt2());
        // ...and they are NOT each other, which is what rules out both
        // spellings having collapsed onto one operator.
        VERIFY(slash.toSmt2() != pct.toSmt2());
    }
    {
        // `/\` is one token, so a conjunction is not read as a division.
        const Translation t = run(
            "language ESSENCE' 1.0\n"
            "find a: bool\n"
            "find b: bool\n"
            "such that a /\\ b\n");
        VERIFY(t.ok());
        VERIFY(has(t.toSmt2(), "(and a b)") || has(t.toSmt2(), "(and b a)"));
    }
    {
        // `min`/`max` over a list are an ITE fold -- the operator itself, since
        // the HIR has no integer MIN or MAX. Nothing is approximated, so
        // nothing is recorded.
        const Translation t = run(
            "language ESSENCE' 1.0\n"
            "find m: matrix indexed by [int(1..3)] of int(0..9)\n"
            "such that\n"
            "    min([m[1], m[2], m[3]; int(1..3)]) = 4\n");
        VERIFY(t.ok());
        VERIFY(has(t.toSmt2(), "ite"));
        const Translation mx = run(
            "language ESSENCE' 1.0\n"
            "find m: matrix indexed by [int(1..3)] of int(0..9)\n"
            "such that\n"
            "    max([m[1], m[2], m[3]; int(1..3)]) = 4\n");
        VERIFY(mx.ok());
        // min and max differ, which an ITE fold with the wrong comparison
        // would not.
        VERIFY(t.toSmt2() != mx.toSmt2());
    }
    {
        // A single element is itself -- no ITE at all.
        const Translation t = run(
            "language ESSENCE' 1.0\n"
            "find m: matrix indexed by [int(1..2)] of int(0..9)\n"
            "such that min([m[1]; int(1)]) = 4\n");
        VERIFY(t.ok());
        VERIFY(hasEq(t.toSmt2(), "4", "(select m 1)"));
    }
    {
        // A named finite matrix supplies every declared cell to min, in
        // the same order as its explicit list form.
        const Translation t = run(
            "language ESSENCE' 1.0\n"
            "find m: matrix indexed by [int(1..3)] of int(0..9)\n"
            "such that min(m) = 4\n");
        const Translation expanded = run(
            "language ESSENCE' 1.0\n"
            "find m: matrix indexed by [int(1..3)] of int(0..9)\n"
            "such that min([m[1], m[2], m[3]]) = 4\n");
        VERIFY(t.ok());
        VERIFY(expanded.ok());
        VERIFY(t.toSmt2() == expanded.toSmt2());
    }

    std::cout << "======= a multi-dimensional read at a non-constant subscript =======\n";
    {
        // The flattened offset of a non-constant subscript is an arithmetic
        // TERM, built with the same Horner recurrence `Matrix::offsetOf`
        // folds. The two paths must agree about the layout, and the strongest
        // way to say that is to make them produce the same script.
        //
        // `q + 1` is deliberately not just `q`: a comprehension variable is
        // substituted as a literal, so a bare `q` takes the all-constant path
        // and would exercise nothing. `q + 1` is an HIR `ADD` of two literals
        // -- the HIR does not fold -- so it reaches the term path, and the
        // ENGINE folds the offset back at lowering.
        const Translation viaterm = run(
            "language ESSENCE' 1.0\n"
            "find m: matrix indexed by [int(1..2), int(1..3)] of int(0..9)\n"
            "such that\n"
            "    and([m[q + 1, 2] = 7 | q : int(1..1)])\n");
        const Translation viaconst = run(
            "language ESSENCE' 1.0\n"
            "find m: matrix indexed by [int(1..2), int(1..3)] of int(0..9)\n"
            "such that\n"
            "    m[2, 2] = 7\n");
        VERIFY(viaterm.ok());
        VERIFY(viaconst.ok());
        // Row-major: offset of [2,2] is (2-1)*3 + (2-1) = 4.
        VERIFY(hasEq(viaconst.toSmt2(), "7", "(select m 4)"));
        VERIFY(hasEq(viaterm.toSmt2(), "7", "(select m 4)"));
        // ...and nothing unfolded survives, which is what rules out the term
        // path having built a DIFFERENT offset that merely contains a 4.
        VERIFY(!has(viaterm.toSmt2(), "(* "));
    }
    {
        // The same property on a matrix whose dimensions start SOMEWHERE ELSE,
        // and with a different `lo` in each. The case above indexes from 1 in
        // both dimensions, so `lo_0 == lo_1` and an implementation that
        // subtracted the wrong dimension's `lo` -- or one `lo` for all of them
        // -- would agree with the right one and pass. Here it cannot: dropping
        // the `- lo_k` gives 6, using `lo_0` throughout gives 6, using `lo_1`
        // throughout gives -2, and only the per-dimension recurrence gives 4.
        //
        // `offsetOf` is the oracle rather than a number written out by hand:
        // it is the path 20 corpus files already take, so asserting that the
        // built term folds to what it produces is the statement that the two
        // paths share one layout.
        const Translation viaterm = run(
            "language ESSENCE' 1.0\n"
            "find m: matrix indexed by [int(0..1), int(2..4)] of int(0..9)\n"
            "such that\n"
            "    and([m[q + 1, 3] = 7 | q : int(0..0)])\n");
        const Translation viaconst = run(
            "language ESSENCE' 1.0\n"
            "find m: matrix indexed by [int(0..1), int(2..4)] of int(0..9)\n"
            "such that\n"
            "    m[1, 3] = 7\n");
        VERIFY(viaterm.ok());
        VERIFY(viaconst.ok());
        // ((0*2) + (1-0))*3 + (3-2) = 4.
        VERIFY(hasEq(viaconst.toSmt2(), "7", "(select m 4)"));
        VERIFY(hasEq(viaterm.toSmt2(), "7", "(select m 4)"));
        VERIFY(!has(viaterm.toSmt2(), "(* "));
    }

    {
        // A subscript that is genuinely variable at solve time keeps its
        // per-dimension guards at the surrounding Boolean comparison.
        const Translation t = run(
            "language ESSENCE' 1.0\n"
            "find m: matrix indexed by [int(1..2), int(1..3)] of int(0..9)\n"
            "find i: int(1..2)\n"
            "such that m[i, 2] = 7\n");
        VERIFY(t.ok());
        const std::string smt = t.toSmt2();
        // The offset is a real term now, not a literal.
        VERIFY(has(smt, "(select m ("));
        // and `i` is pinned to its declared dimension.
        VERIFY(has(smt, "(>= i 1)") || has(smt, "(<= 1 i)"));
        VERIFY(has(smt, "(<= i 2)") || has(smt, "(>= 2 i)"));
    }

    std::cout << "======= an inner comprehension does not destroy an outer binding =======\n";
    {
        // Every expansion site used to ERASE its variables on the way out
        // rather than restore what they shadowed. An inner comprehension
        // reusing an outer's name therefore deleted the outer binding, and
        // every later reference refused with "parameter has no value".
        //
        // It fails SAFE -- a refusal, never a wrong answer -- and Conjure
        // generates unique names (`q1`, `q15`), so nothing in the corpus
        // reaches it. That is exactly why it needs a test: no corpus file will
        // ever notice if it comes back.
        //
        // The outer `q` is 2 and the inner is 1, so the two reads are
        // distinguishable in the output. Reusing one value would let an
        // implementation that never restored anything pass.
        const Translation t = run(
            "language ESSENCE' 1.0\n"
            "find m: matrix indexed by [int(1..3)] of int(0..9)\n"
            "such that\n"
            "    and([and([m[q] = 1 | q : int(1..1)]) /\\ m[q] = 2 | q : int(2..2)])\n");
        VERIFY(t.ok());
        const std::string smt = t.toSmt2();
        VERIFY(hasEq(smt, "1", "(select m 1)"));   // the INNER q
        VERIFY(hasEq(smt, "2", "(select m 2)"));   // the OUTER q, still bound
    }

    std::cout << "======= a generator over a matrix domain =======\n";
    {
        // A quantifier over a FUNCTION SPACE: `t` ranges over every matrix of
        // the shape. Expanded, like every other generator in this frontend.
        //
        // The assertions are chosen so that an OVER-approximation cannot pass.
        // "It translated" and "cvc5 said sat" are both satisfied by dropping
        // the quantifier entirely -- the failure mode this whole project is
        // organised against -- so each case below is one where the quantifier
        // is the only thing doing work, and the answer changes if any single
        // matrix in the space is missed.
        //
        // `t` ranges over the three 1-cell matrices [1], [2], [3], so
        // `x != t[1]` for all of them rules out every value x can take.
        const Translation t = run(
            "language ESSENCE' 1.0\n"
            "find x: int(1..3)\n"
            "such that\n"
            "    and([x != t[1] | t : matrix indexed by [int(1..1)] of int(1..3)])\n");
        VERIFY(t.ok());
        const std::string smt = t.toSmt2();
        // All three exclusions, and nothing left for x.
        VERIFY(has(smt, "1") && has(smt, "2") && has(smt, "3"));
        VERIFY(countOf(smt, "distinct") + countOf(smt, "not (=") >= 3);
    }
    {
        // The control: one value fewer in the ELEMENT domain leaves exactly
        // one value for x. An implementation that enumerated the wrong space
        // -- or the same space in both cases -- fails one of the two.
        const Translation t = run(
            "language ESSENCE' 1.0\n"
            "find x: int(1..3)\n"
            "such that\n"
            "    and([x != t[1] | t : matrix indexed by [int(1..1)] of int(1..2)])\n");
        VERIFY(t.ok());
        VERIFY(countOf(t.toSmt2(), "distinct") + countOf(t.toSmt2(), "not (=") == 2);
    }
    {
        // TWO cells, which is where a decoder that walked one radix wrongly
        // stops producing the whole space. The four matrices are [1,1] [1,2]
        // [2,1] [2,2], so four conjuncts -- not two, and not three.
        const Translation t = run(
            "language ESSENCE' 1.0\n"
            "find x: int(1..9)\n"
            "such that\n"
            "    and([x != t[1] + t[2] | t : matrix indexed by [int(1..2)] of int(1..2)])\n");
        VERIFY(t.ok());
        VERIFY(countOf(t.toSmt2(), "distinct") + countOf(t.toSmt2(), "not (=") == 4);
    }
    {
        // A GUARD over the bound matrix. `constGuard` reads comparisons and
        // connectives, not comprehensions, so a matrix generator's guards go
        // through the expression parser and are evaluated as constants. Here
        // the guard drops exactly one of the three matrices.
        const Translation t = run(
            "language ESSENCE' 1.0\n"
            "find x: int(1..3)\n"
            "such that\n"
            "    and([x != t[1] | t : matrix indexed by [int(1..1)] of int(1..3),\n"
            "                     t[1] != 2])\n");
        VERIFY(t.ok());
        VERIFY(countOf(t.toSmt2(), "distinct") + countOf(t.toSmt2(), "not (=") == 2);
    }
    {
        // A guard that is itself a FOLD over the matrix -- which is what
        // Conjure actually writes -- rather than a bare comparison.
        const Translation t = run(
            "language ESSENCE' 1.0\n"
            "find x: int(1..9)\n"
            "such that\n"
            "    and([x != t[1] + t[2] | t : matrix indexed by [int(1..2)] of int(1..2),\n"
            "                            and([t[q] = 1 | q : int(1..2)])])\n");
        VERIFY(t.ok());
        // Only [1,1] survives the guard, so one conjunct: x != 2.
        VERIFY(countOf(t.toSmt2(), "distinct") + countOf(t.toSmt2(), "not (=") == 1);
    }
    {
        // The space is |values|^|cells|, so the cost is exponential in the
        // shape and the refusal is by name rather than by running out of
        // memory. 9^8 is 43 million.
        const Translation t = run(
            "language ESSENCE' 1.0\n"
            "find x: int(1..3)\n"
            "such that\n"
            "    and([x != t[1] | t : matrix indexed by [int(1..8)] of int(1..9)])\n");
        VERIFY(!t.ok());
        VERIFY(t.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        VERIFY(has(firstError(t), "elaborator range"));
    }

    std::cout << "All Essence' guard, catchUndef, matrix-literal, "
                 "alldifferent_except, <lex and flatten tests passed.\n";
    return 0;
}
