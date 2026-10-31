// Index sets: named, and more than one.
//
// Two MiniZinc constructs that this frontend refused, and that turn out to be
// one idea rather than two:
//
//   * `set of int: ROW = 1..n;` -- a PARAMETER set. Its value is known at parse
//     time, so it is a compile-time integer range and NOT the HIR's finite-set
//     theory, which `var set of int` uses. Nine of the sixteen upstream files
//     stopped on this line.
//
//   * `array[ROW, COL] of var int: a;` -- two index sets. An HIR array is
//     SMT-LIB's, a total function of ONE index, so a second dimension has to be
//     flattened, and the frontend previously refused rather than choose that
//     encoding silently. Four upstream files stopped here, and eight more
//     arrive here as soon as the first item above is read.
//
// They are one idea because a `set of int` item IS an index set: once an array
// dimension can be a named set, an array with two of them is the same code
// twice. Doing them separately would have built the index-set abstraction with
// one dimension baked into it.
//
// The flattening is row-major and recorded as an EncodingChoice. It is exact,
// not an approximation -- a bijection between the declared index sets and
// `0 .. n0*n1-1` -- and the frontend still holds both original sets, so an
// out-of-range index in EITHER dimension is still an error rather than a
// select into the total function's unconstrained part.
//
// The failure this file exists to catch is the quiet one. A wrong flattening
// (column-major, an off-by-one in a stride, the wrong dimension's size) is
// still a well-sorted select at an in-range index. Nothing downstream can
// object: the script parses, the solver answers, and the answer is to a
// different question. So the assertions below pin the emitted INDEX, not the
// fact that indexing happened.

#include "distinct_scope.h"
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

Translation mzn(const std::string& src) {
    Lang::SourceUnit u;
    u.inline_source = src;
    u.display_name = "<test>";
    TranslateOptions opts;
    opts.language_id = "minizinc";
    return translate(u, opts);
}

std::string firstError(const Translation& t) {
    for (const Diagnostic& d : t.diagnostics().all()) {
        if (d.severity == Severity::ERROR) { return d.message; }
    }
    return "<no error>";
}

/** How many `(select ...)` terms the emitted script contains. */
std::size_t selects(const std::string& smt) {
    std::size_t n = 0;
    for (std::size_t p = smt.find("(select "); p != std::string::npos;
         p = smt.find("(select ", p + 1)) {
        ++n;
    }
    return n;
}

} // namespace

int main() {
    std::cout << "======= MiniZinc: named and multi-dimensional index sets =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    // ---- A named index set. -------------------------------------------------
    {
        const Translation t = mzn(
            "set of int: S = 1..3;\n"
            "array[S] of var int: a;\n"
            "constraint a[2] > 0;\n"
            "solve satisfy;\n");
        if (!t.ok()) { std::cout << "  refused: " << firstError(t) << "\n"; VERIFY(false); }
        const std::string smt = t.toSmt2();
        // The set is a RANGE, so a one-dimensional array indexed by it keeps the
        // source index -- `a[2]` is `(select a 2)`, not a rebased 1 or 0. The
        // named set must not quietly change the meaning of an index.
        VERIFY(has(smt, "(select a 2)"));
        ParserPtr p = newParser();
        VERIFY(p->parseStr(smt));
    }
    {
        // The bound travels with the name: an index outside the named set is the
        // same modelling error as one outside a literal range.
        const Translation t = mzn(
            "set of int: S = 1..3;\n"
            "array[S] of var int: a;\n"
            "constraint a[4] > 0;\n"
            "solve satisfy;\n");
        VERIFY(!t.ok());
        VERIFY(t.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        VERIFY(has(firstError(t), "index set"));
    }
    {
        // The same fixed set may be a value domain, both for a scalar and for
        // every array cell. It is an Int carrier plus explicit bounds, not an
        // unconstrained Int and not an unrelated enum sort.
        const Translation t = mzn(
            "set of int: VALUE = 2..4;\n"
            "var VALUE: x;\n"
            "array[1..2] of var VALUE: a;\n"
            "constraint x = a[1];\n"
            "solve satisfy;\n");
        VERIFY(t.ok());
        const std::string smt = t.toSmt2();
        VERIFY(has(smt, "(>= x 2)"));
        VERIFY(has(smt, "(<= x 4)"));
        VERIFY(has(smt, "(>= (select a 1) 2)"));
        VERIFY(has(smt, "(<= (select a 2) 4)"));
    }
    {
        // A set built from a literal and a union, which is how the corpus writes
        // one: `{Table} union blocks`. {0} union 1..2 is 0..2 and contiguous, so
        // it is a usable index set.
        const Translation t = mzn(
            "set of int: S = {0} union 1..2;\n"
            "array[S] of var int: a;\n"
            "constraint a[0] > 0;\n"
            "solve satisfy;\n");
        if (!t.ok()) { std::cout << "  refused: " << firstError(t) << "\n"; VERIFY(false); }
        VERIFY(has(t.toSmt2(), "(select a 0)"));
    }
    {
        // ...and one with a hole in it is NOT. An HIR array index set is a
        // contiguous span, so `{1, 3}` would have to be widened to 1..3 --
        // silently adding an index the model never declared, which is a select
        // into the total function's unconstrained part.
        const Translation t = mzn(
            "set of int: S = {1, 3};\n"
            "array[S] of var int: a;\n"
            "constraint a[1] > 0;\n"
            "solve satisfy;\n");
        VERIFY(!t.ok());
        VERIFY(t.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        VERIFY(has(firstError(t), "contiguous"));
    }
    {
        // A generator over a named set. `forall(i in S)` is the reason the sets
        // exist in the corpus at all.
        const Translation t = mzn(
            "set of int: S = 1..3;\n"
            "array[S] of var int: a;\n"
            "constraint forall(i in S)(a[i] > 0);\n"
            "solve satisfy;\n");
        if (!t.ok()) { std::cout << "  refused: " << firstError(t) << "\n"; VERIFY(false); }
        const std::string smt = t.toSmt2();
        VERIFY(selects(smt) == 3);
        VERIFY(has(smt, "(select a 1)"));
        VERIFY(has(smt, "(select a 3)"));
    }
    {
        // A set whose bounds are computed from parameters, which is every
        // occurrence in the corpus: `set of int: COL = 1..(n + 2);`.
        const Translation t = mzn(
            "int: n = 2;\n"
            "set of int: S = 1..(n + 2);\n"
            "array[S] of var int: a;\n"
            "constraint a[4] > 0;\n"
            "solve satisfy;\n");
        if (!t.ok()) { std::cout << "  refused: " << firstError(t) << "\n"; VERIFY(false); }
        VERIFY(has(t.toSmt2(), "(select a 4)"));
    }
    {
        // A decision-variable index is partial in MiniZinc but `select` is total
        // in SMT-LIB. Bounds therefore belong to the left disjunct's Boolean
        // scope: i=99 must satisfy the model through the right disjunct.
        const Translation t = mzn(
            "array[1..3] of var int: a;\n"
            "var int: i;\n"
            "constraint (a[i] + 3) > 10 \\/ i = 99;\n"
            "solve satisfy;\n");
        if (!t.ok()) { std::cout << "  refused: " << firstError(t) << "\n"; VERIFY(false); }
        const std::string smt = t.toSmt2();
        VERIFY(has(smt, "(select a i)"));
        VERIFY(has(smt, "(<= i 3)"));
        VERIFY(has(smt, "(>= i 1)"));
        VERIFY(has(smt, "(= i 99)"));
        VERIFY(!has(smt, "(assert (and (<= i 3) (>= i 1)))"));
        VERIFY(t.report().fidelity().sound && t.report().fidelity().complete && t.report().fidelity().preserves_optimum && t.report().fidelity().bounds.empty() && t.report().fidelity().count_status == CountStatus::UNASSESSED);
    }

    // ---- Two index sets. ----------------------------------------------------
    {
        const Translation t = mzn(
            "array[1..2, 1..3] of var int: a;\n"
            "constraint a[2, 3] > 0;\n"
            "solve satisfy;\n");
        if (!t.ok()) { std::cout << "  refused: " << firstError(t) << "\n"; VERIFY(false); }
        const std::string smt = t.toSmt2();
        // Row-major, zero-based: (2-1)*3 + (3-1) = 5. Every wrong flattening
        // this could have -- column-major (1 + 2*2 = ...), one-based, the other
        // dimension's stride -- lands on a DIFFERENT in-range index and is
        // otherwise indistinguishable, so the number is the assertion.
        VERIFY(has(smt, "(select a 5)"));
        ParserPtr p = newParser();
        VERIFY(p->parseStr(smt));

        // beta reverses row-major flattening cell by cell. A direct `a -> a`
        // projection would expose the target's one-dimensional total array and
        // lose both source index sets.
        Sem::Assignment target;
        for (int i = 0; i < 6; ++i) {
            target["(select a " + std::to_string(i) + ")"] =
                std::to_string(10 + i);
        }
        Sem::Assignment source;
        Diagnostics projection_diags;
        VERIFY(t.semantics().project(target, source, projection_diags));
        VERIFY(source.at("a[1,1]") == "10");
        VERIFY(source.at("a[2,3]") == "15");
        VERIFY(source.count("a") == 0);
    }
    {
        // The first cell and the last, to pin both ends of the stride.
        const Translation t = mzn(
            "array[1..2, 1..3] of var int: a;\n"
            "constraint a[1, 1] > 0;\n"
            "constraint a[1, 3] > 0;\n"
            "constraint a[2, 1] > 0;\n"
            "solve satisfy;\n");
        VERIFY(t.ok());
        const std::string smt = t.toSmt2();
        VERIFY(has(smt, "(select a 0)"));      // (1,1)
        VERIFY(has(smt, "(select a 2)"));      // (1,3) -- the row's last
        VERIFY(has(smt, "(select a 3)"));      // (2,1) -- the next row's first
    }
    {
        // A non-1-based pair of index sets, where a flattening that forgets to
        // subtract the lower bound still produces an in-range index for some
        // cells and not others.
        const Translation t = mzn(
            "array[0..1, 2..3] of var int: a;\n"
            "constraint a[1, 3] > 0;\n"
            "solve satisfy;\n");
        VERIFY(t.ok());
        // (1-0)*2 + (3-2) = 3
        VERIFY(has(t.toSmt2(), "(select a 3)"));
    }
    {
        // Wrong number of indices is an error, not a guess. Supplying one index
        // to a two-dimensional array is the shape a reader of the flattened
        // output would have to write, and accepting it would mean the source
        // and the encoding disagree about what `a[i]` denotes.
        const Translation t = mzn(
            "array[1..2, 1..3] of var int: a;\n"
            "constraint a[2] > 0;\n"
            "solve satisfy;\n");
        VERIFY(!t.ok());
        VERIFY(t.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        VERIFY(has(firstError(t), "2 index"));
    }
    {
        // Out of range in the SECOND dimension. This is the case a flattened
        // bounds check gets wrong: 4 is outside 1..3, but the flat index
        // (2-1)*3 + (4-1) = 6 is inside 0..5 and denotes cell (3,1) of an array
        // that has no third row. Checking after flattening would accept it.
        const Translation t = mzn(
            "array[1..2, 1..3] of var int: a;\n"
            "constraint a[2, 4] > 0;\n"
            "solve satisfy;\n");
        VERIFY(!t.ok());
        VERIFY(t.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
    }
    {
        // Named sets in both dimensions -- the corpus's actual shape.
        const Translation t = mzn(
            "int: n = 2;\n"
            "set of int: ROW = 1..n;\n"
            "set of int: COL = 1..(n + 1);\n"
            "array[ROW, COL] of var int: a;\n"
            "constraint forall(r in ROW, c in COL)(a[r, c] > 0);\n"
            "solve satisfy;\n");
        if (!t.ok()) { std::cout << "  refused: " << firstError(t) << "\n"; VERIFY(false); }
        const std::string smt = t.toSmt2();
        VERIFY(selects(smt) == 6);             // 2 rows x 3 columns, each once
        VERIFY(has(smt, "(select a 0)"));
        VERIFY(has(smt, "(select a 5)"));
        VERIFY(!has(smt, "(select a 6)"));     // and nothing past the last cell
    }
    {
        // Element bounds are emitted per CELL, not per row: a two-dimensional
        // `var 0..1` array has one pair of bounds for each of its four cells.
        const Translation t = mzn(
            "array[1..2, 1..2] of var 0..1: a;\n"
            "solve satisfy;\n");
        VERIFY(t.ok());
        VERIFY(t.report().stats().num_constraints == 8);
        VERIFY(selects(t.toSmt2()) == 8);
    }
    {
        // The decision is in the report, not only in the output. A reader of the
        // emitted script cannot tell a flattened two-dimensional array from a
        // one-dimensional one -- which is exactly why the frontend refused to
        // make the choice silently, and exactly what an EncodingChoice is for.
        const Translation t = mzn(
            "array[1..2, 1..3] of var int: a;\n"
            "constraint a[1, 1] > 0;\n"
            "solve satisfy;\n");
        VERIFY(t.ok());
        bool recorded = false;
        for (const EncodingChoice& c : t.report().choices()) {
            if (c.strategy == "array-flatten-row-major") { recorded = true; }
        }
        VERIFY(recorded);
        // Exact: the flattening is a bijection, so nothing about the answer
        // changes. If this ever stops being exact it is a different encoding.
        VERIFY(t.report().fidelity().sound && t.report().fidelity().complete && t.report().fidelity().preserves_optimum && t.report().fidelity().bounds.empty() && t.report().fidelity().count_status == CountStatus::UNASSESSED);
    }
    {
        // A one-dimensional array records NO such choice: there was nothing to
        // decide, and a report listing a choice per array would drown the ones
        // that matter.
        const Translation t = mzn(
            "array[1..3] of var int: a;\n"
            "constraint a[1] > 0;\n"
            "solve satisfy;\n");
        VERIFY(t.ok());
        for (const EncodingChoice& c : t.report().choices()) {
            VERIFY(c.strategy != "array-flatten-row-major");
        }
    }
    {
        // alldifferent over a flattened array covers every cell exactly once.
        // The global carries a half-open [lo, hi) over the FLAT index space, so
        // a decomposition that used the first dimension's bounds would compare
        // one row and report success.
        const Translation t = mzn(
            "array[1..2, 1..3] of var int: a;\n"
            "constraint alldifferent(a);\n"
            "solve satisfy;\n");
        if (!t.ok()) { std::cout << "  refused: " << firstError(t) << "\n"; VERIFY(false); }
        const std::string smt = t.toSmt2();
        // Six flat cells occur once in native distinct.
        VERIFY(selects(smt) == 6);
        VERIFY(SomtTest::hasDistinctArguments(t.parser(), {"(select a 0)", "(select a 1)", "(select a 2)",
                        "(select a 3)", "(select a 4)", "(select a 5)"}));
        ParserPtr p = newParser();
        VERIFY(p->parseStr(smt));
    }

    // ---- A generator's source is WIDER than an index set, deliberately. -----
    {
        // `forall(r in {1, n + 2})` -- a non-contiguous literal. An array's
        // index set may not have a hole, because it becomes an index SPACE and
        // widening it would add indices the model never declared. A generator's
        // source is only ITERATED, so a hole costs nothing and refusing one
        // would reject an ordinary idiom: `battleships.mzn.model` writes
        // exactly this for the first and last row of a grid.
        const Translation t = mzn(
            "int: n = 2;\n"
            "array[1..4] of var int: a;\n"
            "constraint forall(i in {1, n + 2})(a[i] > 0);\n"
            "solve satisfy;\n");
        if (!t.ok()) { std::cout << "  refused: " << firstError(t) << "\n"; VERIFY(false); }
        const std::string smt = t.toSmt2();
        VERIFY(selects(smt) == 2);
        VERIFY(has(smt, "(select a 1)"));
        VERIFY(has(smt, "(select a 4)"));
        // ...and NOT the values a widened 1..4 would have added. This is the
        // assertion that separates "iterated the literal" from "took its span".
        VERIFY(!has(smt, "(select a 2)"));
        VERIFY(!has(smt, "(select a 3)"));
    }
    {
        // The same set as an INDEX SET is still refused: the asymmetry above is
        // a claim about what each position means, not a gap that happens to be
        // open on one side.
        const Translation t = mzn(
            "set of int: S = {1, 3};\n"
            "array[S] of var int: a;\n"
            "solve satisfy;\n");
        VERIFY(!t.ok());
        VERIFY(has(firstError(t), "contiguous"));
    }
    {
        // A duplicate iterates once. `{1, 1}` is one element -- MiniZinc's sets
        // are sets -- and iterating it twice would emit the constraint twice.
        const Translation t = mzn(
            "array[1..2] of var int: a;\n"
            "constraint forall(i in {1, 1})(a[i] > 0);\n"
            "solve satisfy;\n");
        VERIFY(t.ok());
        VERIFY(selects(t.toSmt2()) == 1);
    }

    // ---- Fixed comprehensions and remaining refusals. ------------------------
    {
        // A fixed set comprehension is evaluated during elaboration. It does
        // not require a solver-level collection value merely to bind S.
        const Translation t = mzn(
            "set of int: S = {i * i | i in 1..3};\n"
            "solve satisfy;\n");
        VERIFY(t.ok());
    }
    {
        // A set item with no value has nowhere to get one: unlike `int: n;`
        // there is no `.dzn` reader for a set in this subset, and inventing an
        // empty set would make every constraint over it vacuously true.
        const Translation t = mzn(
            "set of int: S;\n"
            "solve satisfy;\n");
        VERIFY(!t.ok());
        VERIFY(t.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
    }

    std::cout << "All MiniZinc index-set tests passed." << std::endl;
    return 0;
}
