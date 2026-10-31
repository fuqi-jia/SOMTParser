// Essence' multi-dimensional matrices.
//
// `matrix indexed by [a, b]` is TWO index sets and an HIR array holds one, so
// the dimensions are flattened row-major -- the same convention MiniZinc's
// flatIndex uses, and for the same reason. Unlike a parameter array, whose
// cells fold to literals and never reach the output (`mps.md` §4.7), a
// decision matrix IS emitted, so nothing in the script distinguishes a
// flattened two-dimensional matrix from a one-dimensional one and a reader of
// the output alone cannot recover the source shape. That makes the flattening
// an EncodingChoice, and it is recorded.
//
// Three things here are easy to get subtly wrong, and each produces a model
// that still translates:
//
//   * checking only the flattened OFFSET instead of each subscript against its
//     own domain -- `q[1,5]` on an int(1..4) second dimension lands inside the
//     next row, in range for the flat vector and wrong for the model;
//   * taking dimension one's span as `alldifferent`'s bounds, which constrains
//     the first row and leaves the rest free -- strictly weaker, still sound
//     looking;
//   * naming the projection's observables by the flattened offset, so a reader
//     mapping a solution back sees `q[7]` where the source says `q[2,3]`.
//
// One dimension keeps the SOURCE index -- `q[3]` is still `(select q 3)` --
// because every existing fixture says so and rebasing it would be a gratuitous
// change to output nobody asked to move.

#include "distinct_scope.h"
#include "somtparser/translation/translate.h"
#include "somtparser/languages/register_all.h"

#include <iostream>
#include <string>

#include "test_helpers.h"

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

Translation run(const std::string& text) {
    Lang::SourceUnit unit;
    unit.inline_source = text;
    unit.display_name = "<essence-matrix-test>";
    TranslateOptions options;
    options.language_id = "essence";
    options.profile_id = "ground";
    return translate(unit, options);
}

bool has(const std::string& text, const std::string& fragment) {
    return text.find(fragment) != std::string::npos;
}

std::string firstError(const Translation& t) {
    for (const Diagnostic& d : t.diagnostics().all()) {
        if (d.severity == Severity::ERROR) { return d.message; }
    }
    return "<no error>";
}

const char* kHead = "language ESSENCE' 1.0\n";

} // namespace

int main() {
    std::cout << "======= Essence' multi-dimensional matrices =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    {
        // Row-major, pinned CELL BY CELL. One corner would pass for a
        // column-major reading of a square matrix, so the shape is
        // deliberately 2x3 and every cell is named.
        const Translation t = run(
            std::string(kHead)
            + "find q: matrix indexed by [int(1..2), int(1..3)] of int(0..9)\n"
              "such that\n"
              "    q[1,1] = 11, q[1,2] = 12, q[1,3] = 13,\n"
              "    q[2,1] = 21, q[2,2] = 22, q[2,3] = 23\n");
        VERIFY(t.ok());
        const std::string smt = t.toSmt2();
        // offsets 0..5, last dimension fastest
        VERIFY(has(smt, "(= (select q 0) 11)") || has(smt, "(= 11 (select q 0))"));
        VERIFY(has(smt, "(= (select q 2) 13)") || has(smt, "(= 13 (select q 2))"));
        VERIFY(has(smt, "(= (select q 3) 21)") || has(smt, "(= 21 (select q 3))"));
        VERIFY(has(smt, "(= (select q 5) 23)") || has(smt, "(= 23 (select q 5))"));
    }

    {
        // One dimension is unchanged and keeps the source index.
        const Translation t = run(
            std::string(kHead)
            + "find q: matrix indexed by [int(3..5)] of int(0..9)\n"
              "such that q[3] = 7\n");
        VERIFY(t.ok());
        VERIFY(has(t.toSmt2(), "(select q 3)"));
    }

    {
        // Each subscript is checked against ITS OWN domain. `q[1,5]` flattens
        // to offset 4, which is a real cell -- the second row's second column
        // -- so a check on the offset alone would accept it.
        const Translation t = run(
            std::string(kHead)
            + "find q: matrix indexed by [int(1..2), int(1..4)] of int(0..9)\n"
              "such that q[1,5] = 1\n");
        VERIFY(t.ok());
        VERIFY(has(t.toSmt2(), "(assert false)"));
    }

    {
        // Wrong subscript ARITY is not an out-of-range index.
        const Translation t = run(
            std::string(kHead)
            + "find q: matrix indexed by [int(1..2), int(1..3)] of int(0..9)\n"
              "such that q[1] = 1\n");
        VERIFY(!t.ok());
        VERIFY(t.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        VERIFY(has(firstError(t), "subscript"));
    }

    {
        // The element domain is materialised over EVERY cell, not one row. An
        // SMT-LIB array is total, so an unbounded cell is one the solver picks.
        const Translation t = run(
            std::string(kHead)
            + "find q: matrix indexed by [int(1..2), int(1..2)] of int(5..6)\n"
              "such that q[1,1] = 5\n");
        VERIFY(t.ok());
        const std::string smt = t.toSmt2();
        for (const char* off : {"0", "1", "2", "3"}) {
            VERIFY(has(smt, std::string("(select q ") + off + ")"));
        }
    }

    {
        // The flattening is recorded, because the emitted script shows only
        // the offset and the source shape is recoverable from nowhere else.
        const Translation t = run(
            std::string(kHead)
            + "find q: matrix indexed by [int(1..2), int(1..3)] of int(0..9)\n"
              "such that q[1,1] = 1\n");
        VERIFY(t.ok());
        bool recorded = false;
        for (const EncodingChoice& c : t.report().choices()) {
            if (c.strategy == "matrix-flatten-row-major") {
                recorded = true;
                VERIFY(c.site == "q");
                VERIFY(c.fidelity.sound && c.fidelity.complete && c.fidelity.preserves_optimum && c.fidelity.bounds.empty() && c.fidelity.count_status == CountStatus::UNASSESSED);
                VERIFY(has(c.rationale, "int(1..2)"));
                VERIFY(has(c.rationale, "int(1..3)"));
            }
        }
        VERIFY(recorded);
    }

    {
        // ...and a ONE-dimensional matrix records nothing, or the entry says
        // nothing about the model.
        const Translation t = run(
            std::string(kHead)
            + "find q: matrix indexed by [int(1..3)] of int(0..9)\n"
              "such that q[1] = 1\n");
        VERIFY(t.ok());
        for (const EncodingChoice& c : t.report().choices()) {
            VERIFY(c.strategy != "matrix-flatten-row-major");
        }
    }

    {
        // alldifferent over a multi-dimensional matrix covers every cell.
        // Dimension one's span would constrain the first two cells and leave
        // the other four free -- strictly weaker, and it still translates.
        const Translation t = run(
            std::string(kHead)
            + "find q: matrix indexed by [int(1..2), int(1..3)] of int(0..9)\n"
              "such that allDiff(q)\n");
        VERIFY(t.ok());
        const std::string smt = t.toSmt2();
        // Check the distinct arguments, not mentions elsewhere: domain
        // bounds also mention every cell even if allDiff omitted a row.
        VERIFY(SomtTest::hasDistinctArguments(t.parser(), {"(select q 0)", "(select q 1)", "(select q 2)",
                        "(select q 3)", "(select q 4)", "(select q 5)"}));
    }

    {
        // A non-constant subscript on a multi-dimensional matrix was REFUSED by
        // name until 2026-09-22, on the grounds that this frontend expands its
        // quantifiers, so a surviving variable subscript meant something it had
        // not been taught to read. That was true of the quantifiers and false
        // of the corpus: Conjure writes subscripts that are expressions OVER
        // comprehension variables -- `m[q1 + 1, q2]` -- which expansion turns
        // into a term, not a literal. The flattened offset is now built with
        // the same Horner recurrence `offsetOf` evaluates.
        //
        // `q` is indexed by [int(1..2), int(1..2)], so `q[i,1]` has offset
        // ((0*2) + (i-1))*2 + (1-1) = 2*(i-1): affine in `i`, and NOT `i`
        // itself. That last part is the assertion worth making. A reader which
        // forgot it had two dimensions would emit `(select q i)`, which is
        // well-sorted, translates, and silently reads the flat vector at 1 and
        // 2 where the model means 0 and 2 -- the same shape of error as
        // checking the flattened offset instead of each subscript.
        const Translation t = run(
            std::string(kHead)
            + "find i: int(1..2)\n"
              "find q: matrix indexed by [int(1..2), int(1..2)] of int(0..9)\n"
              "such that q[i,1] = 1\n");
        VERIFY(t.ok());
        const std::string smt = t.toSmt2();
        // The subscript reaches the output as a term...
        VERIFY(has(smt, "(select q ("));
        // ...and specifically not as the raw variable.
        VERIFY(!has(smt, "(select q i)"));
        // `i` keeps its declared bounds as hard constraints. This is what
        // confines the offset to the flattened space: the bound is per
        // SUBSCRIPT, never on the offset, so it cannot be satisfied by an
        // index that lands in the wrong row.
        VERIFY(has(smt, "(>= i 1)") || has(smt, "(<= 1 i)"));
        VERIFY(has(smt, "(<= i 2)") || has(smt, "(>= 2 i)"));
    }

    std::cout << "All Essence' matrix tests passed.\n";
    return 0;
}
