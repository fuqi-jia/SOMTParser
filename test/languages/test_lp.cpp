// The LP frontend, and the obligations docs/languages/lp.md wrote down before
// it existed.
//
// The first one is the whole point of the document and it is a single line of
// code:
//
//     **A variable with no `Bounds` entry is NON-NEGATIVE.**
//
// That is the LP format's semantics, from linear programming's own tradition,
// and no file says it. Omitting it produces a strictly weaker model -- more
// feasible points, so a better "optimum" -- that parses, type-checks,
// round-trips, exits 0 and reports exact(). There is no Fidelity value for "I
// translated a different problem", which is why this is a fixture and not a
// comment.
//
// The others are the same shape at smaller scale: Binary contributes the 0/1
// carrier while explicit Bounds may further restrict it; a semi-continuous variable is a
// DISJUNCTION and not an interval; and `<` means `<=`, because linear
// programming has no strict inequality.
//
// One obligation is now moot, and that is worth asserting too: lp.md §4.1's
// scaling rescue existed because the HIR had no real literal, and it required
// the scale factor to be recorded or "the reported optimum is wrong by a factor
// nobody wrote down". ExprKind::LIT_REAL landed on 2026-08-12 and is exact, so
// nothing is scaled and there is no factor.

#include "somtparser/translation/translate.h"
#include "somtparser/languages/lp.h"
#include "somtparser/languages/register_all.h"
#include "somtparser/frontend/parser.h"
#include "somtparser/lowering/omt_emitter.h"

#include <cassert>
#include <iostream>
#include <string>

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

bool has(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

std::size_t count(const std::string& hay, const std::string& needle) {
    std::size_t n = 0, at = 0;
    while ((at = hay.find(needle, at)) != std::string::npos) { ++n; at += needle.size(); }
    return n;
}

Translation run(const std::string& src) {
    Lang::SourceUnit u;
    u.main_path = "t.lp";
    u.display_name = "t.lp";
    u.inline_source = src;
    TranslateOptions opts;
    opts.language_id = "lp";
    return translate(u, opts);
}

Translation runFile(const std::string& path) {
    Lang::SourceUnit u;
    u.main_path = path;
    u.display_name = path;
    TranslateOptions opts;
    opts.language_id = "lp";
    return translate(u, opts);
}

} // namespace

int main() {
    std::cout << "======= LP frontend =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    Lang::Language* l = Lang::LanguageRegistry::instance().byId("lp");
    assert(l != nullptr);
    assert(l->extensions().size() == 1 && l->extensions()[0] == ".lp");

    // ---- The document's own example. ----------------------------------------
    {
        const Translation t = runFile("languages/lp/instances/ok/doc_example.lp");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // Continuous variables are Real; General and Binary are Int.
        assert(has(smt, "declare-fun x () Real"));
        assert(has(smt, "declare-fun z () Int"));
        assert(has(smt, "declare-fun w () Int"));
        // Maximize, not minimize.
        assert(has(smt, "OBJECTIVE_MAX"));
        // The range row is ONE row and TWO inequalities.
        assert(has(smt, "and"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(t.toSmt2(Lower::OmtDialect::Z3)));
    }

    // ---- The obligation: no Bounds entry means non-negative. ----------------
    {
        const Translation t = runFile("languages/lp/instances/ok/default_nonneg.lp");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // One lower bound per variable, and neither is written in the file.
        assert(has(smt, "(>= x 0.0)"));
        assert(has(smt, "(>= y 0.0)"));
        assert(t.report().stats().num_vars == 2);
    }
    {
        // A constraint that would be satisfiable without the default bound is
        // the case where dropping it changes the answer rather than the shape:
        // `x <= -1` with the default is infeasible, and without it is not. The
        // translation must carry the bound whatever the constraints say.
        const Translation t = run("Minimize\n obj: x\nSubject To\n c1: x <= -1\nEnd\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(>= x 0.0)"));
    }
    {
        // A `Bounds` entry OVERRIDES the default -- that is what the section is
        // for, and the default must not be emitted on top of it.
        const Translation t =
            run("Minimize\n obj: x\nSubject To\n c1: x <= 5\nBounds\n -3 <= x <= 5\nEnd\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(- 3.0)") || has(smt, "-3"));
        assert(!has(smt, "(>= x 0.0)"));
    }
    {
        // ...and `free` is the one way to have neither bound.
        const Translation t =
            run("Minimize\n obj: x\nSubject To\n c1: x <= 5\nBounds\n x free\nEnd\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(!has(smt, "(>= x 0.0)"));
        assert(count(smt, "assert") == 1);        // only c1
    }

    // ---- Binary carrier intersects explicit Bounds. ------------------------
    {
        const Translation t =
            runFile("languages/lp/instances/ok/binary_overrides_bounds.lp");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "declare-fun b () Int"));
        assert(has(smt, "(>= b 0)"));
        assert(has(smt, "(<= b 1)"));
        // CPLEX retains explicit alternative bounds (with a warning) while the
        // Binary section still contributes integrality and the intrinsic 0/1
        // carrier. These bounds are redundant here but cannot be discarded in
        // the important `b = 0` case.
        assert(has(smt, "10"));
    }
    {
        const Translation t = run(
            "Minimize\n obj: -b\nSubject To\nBounds\n b = 0\nBinary\n b\nEnd\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "declare-fun b () Int"));
        assert(has(smt, "(>= b 0)") && has(smt, "(<= b 1)"));
        assert(has(smt, "(<= b 0.0)") && has(smt, "(>= b 0.0)"));
    }

    // ---- Semi-continuous is a disjunction, not an interval. ----------------
    // The interval reading admits every value between 0 and l, which is exactly
    // the range the modeller excluded -- so it is more permissive, and the
    // optimum it reports may lie in the excluded band.
    {
        const Translation t = runFile("languages/lp/instances/ok/semicontinuous.lp");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "or"));
        assert(has(smt, "(= 0.0 x)") || has(smt, "(= x 0.0)"));
        // NOT written as a plain bound: `2 <= x` must appear only inside the
        // disjunction, never as a standalone assertion that would forbid zero.
        assert(!has(smt, "(assert (<= 2.0 x))"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(t.toSmt2(Lower::OmtDialect::Z3)));
    }
    {
        // General and Semi-Continuous are orthogonal declarations. Listing a
        // variable in both produces a semi-integer, not a Real whose later
        // section silently erased integrality.
        const Translation t = run(
            "Minimize\n obj: s\nSubject To\n c: s <= 5\nBounds\n 2 <= s <= 4\n"
            "General\n s\nSemi-Continuous\n s\nEnd\n");
        assert(t.ok());
        assert(has(t.toSmt2(), "declare-fun s () Int"));
        assert(has(t.toSmt2(), "(or"));
    }

    // ---- `<` means `<=`. ----------------------------------------------------
    // A frontend emitting Op::LT produces a model whose feasible region excludes
    // its own boundary, and an LP optimum usually sits on the boundary.
    {
        const Translation t =
            runFile("languages/lp/instances/ok/strict_is_not_strict.lp");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "<="));
        assert(has(smt, ">="));
        // No strict comparison anywhere: `(< ` and `(> ` with a space are how
        // the engine prints them, and `<=`/`>=` do not match those.
        assert(!has(smt, "(< "));
        assert(!has(smt, "(> "));
    }

    // ---- Decimals are exact, and §4.1's rescue is moot. --------------------
    {
        const Translation t = runFile("languages/lp/instances/ok/exact_decimals.lp");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // 0.1 is one tenth exactly. A double would give
        // 0.1000000000000000055511151231257827, and the scaling rescue would
        // have multiplied the row by 20 and owed a recorded scale factor.
        assert(has(smt, "(/ 1 10)"));
        assert(has(smt, "(/ 1 4)"));
        assert(has(smt, "(/ 15 4)"));            // 3.75
        assert(!has(smt, "0.1000000"));
    }
    {
        // LP permits exponent notation, omitted whitespace between a numeric
        // coefficient and variable, and a constant objective offset. All are
        // exact rationals in the semantic core.
        const Translation t = run(
            "Minimize\n obj: 1e-3x + 2.5\nSubject To\n"
            " 2x + .5 <= 1e2\nEnd\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(/ 1 1000)"));
        assert(has(smt, "(/ 5 2)"));
        assert(has(smt, "100"));
    }
    {
        // A lower bound may be written with the value first. Separate unnamed
        // constraints each begin on a new line and must not be concatenated.
        const Translation t = run(
            "Minimize\n x\nSubject To\n x <= 5\n x >= -2\nBounds\n"
            " -3 <= x\nEnd\n");
        assert(t.ok());
        assert(t.report().stats().num_constraints == 2);
        const std::string smt = t.toSmt2();
        assert(has(smt, "(- 3.0)") || has(smt, "-3"));
        assert(!has(smt, "declare-fun |3|"));
    }
    {
        // LP expressions continue across physical lines. A sign at the start
        // of a continuation line separates the next term; an empty left-hand
        // side is the constant zero. Both forms occur in HiGHS' 2122.lp and
        // are accepted by CPLEX 22.1.
        const Translation t = run(
            "Minimize\n obj: 3 x\n -2 y\n +4 z\nSubject To\n"
            " zero: = +0\n c: x + y + z >= 1\nEnd\n");
        assert(t.ok());
        assert(t.report().stats().num_vars == 3);
        assert(t.report().stats().num_constraints == 2);
        const std::string smt = t.toSmt2();
        assert(has(smt, "(* y (- 2.0))") || has(smt, "(* (- 2.0) y)"));
        assert(has(smt, "(* z 4.0)"));
    }

    // ---- What is refused, and how. -----------------------------------------
    {
        // SOS sets are a coverage gap, not a parse error: the file is valid LP.
        const Translation t = runFile("languages/lp/instances/reject/sos.lp");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        Lang::Language* lp = Lang::LanguageRegistry::instance().byId("lp");
        // Quadratic expressions left this list on 2026-09-20 (lp.md §4.5), so
        // supported went 6 -> 7 and `missing` lost its first entry. The row is
        // kept because what it guards is the RELATION between the three --
        // `len(missing) == total - supported` -- which is the invariant that
        // stops a coverage figure improving by forgetting a gap. The Python
        // suite enforces it for every language; this one pins the numbers for
        // the language whose fixture is right here.
        assert(lp->coverage().total == 9);
        assert(lp->coverage().supported == 7);
        assert(lp->coverage().missing.size() == 2);
        assert(lp->coverage().missing[1] == "SOS1/SOS2");
    }
    {
        // This asserted that a quadratic objective is REFUSED until
        // 2026-09-20. It pinned a limitation of the subset rather than a
        // property of LP, so lifting the limitation moved it: the same input
        // now translates, and the coefficient shows the written divisor was
        // applied. The feature itself is covered in test_lp_quadratic.cpp,
        // against the MPS spelling of the same model.
        const Translation quadratic = run(
            "Minimize\n obj: [ x ^ 2 ] / 2\nSubject To\n x >= 0\nEnd\n");
        assert(quadratic.ok());
        assert(has(quadratic.toSmt2(), "(* x x)"));

        const Translation indicator = run(
            "Minimize\n obj: x\nSubject To\n b = 1 -> x <= 2\nEnd\n");
        assert(!indicator.ok());
        assert(indicator.diagnostics().firstErrorCode()
               == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
    }
    {
        const Translation t = runFile("languages/lp/instances/reject/no_operator.lp");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
    }
    {
        const Translation t = runFile("languages/lp/instances/nosuch.lp");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_IO);
    }

    // ---- Keywords are case-insensitive and come in several spellings. -------
    {
        for (const char* head : {"Maximize", "MAXIMISE", "max"}) {
            const Translation t =
                run(std::string(head) + "\n obj: x\nSubject To\n c1: x <= 1\nEnd\n");
            assert(t.ok());
            assert(has(t.toSmt2(), "OBJECTIVE_MAX"));
        }
        for (const char* head : {"Subject To", "st", "s.t."}) {
            const Translation t =
                run(std::string("Minimize\n obj: x\n") + head + "\n c1: x <= 1\nEnd\n");
            assert(t.ok());
            assert(t.report().stats().num_constraints >= 1);
        }
    }

    std::cout << "All LP tests passed." << std::endl;
    return 0;
}
