// MiniZinc arrays and alldifferent, end to end.
//
// The decomposition pass, the GLOBAL expression kind and the ground/quantified
// profiles all landed together, and until now every one of them was exercised
// only from hand-built HIR. That is a real gap rather than a stylistic one: the
// ground-versus-quantified axis is the project's central experimental
// parameter, and a parameter reachable only from a unit test is a parameter no
// benchmark can vary. This file drives it from a MiniZinc source string, which
// is the path an instance actually takes.
//
// The failure it exists to catch is an off-by-one, and it is the kind that no
// type check can see. MiniZinc's index set `1..n` is inclusive at both ends;
// the HIR's alldifferent takes a half-open `[lo, hi)`, because the
// decomposition enumerates `for i = lo; i < hi`. Both forms are well-sorted, so
// handing over `n` instead of `n + 1` drops the last element of every
// alldifferent in the corpus and every stage downstream agrees it is fine.

#include "somtparser/translation/translate.h"
#include "somtparser/languages/minizinc.h"
#include "somtparser/languages/register_all.h"

#include <cassert>
#include <iostream>
#include <string>

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

Translation run(const std::string& src, const char* profile) {
    Lang::SourceUnit u;
    u.main_path = "t.mzn";
    u.display_name = "t.mzn";
    u.inline_source = src;
    TranslateOptions opts;
    opts.language_id = "minizinc";
    opts.profile_id = profile;
    return translate(u, opts);
}

/** How many `(select …)` terms the emitted script contains -- the size measure
 *  that separates the two encodings. */
std::size_t selects(const std::string& smt) {
    std::size_t n = 0, at = 0;
    while ((at = smt.find("(select ", at)) != std::string::npos) { ++n; ++at; }
    return n;
}

bool has(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

const char* kFour =
    "array[1..4] of var int: a;\n"
    "constraint alldifferent(a);\n"
    "solve satisfy;\n";

} // namespace

int main() {
    std::cout << "======= MiniZinc arrays and globals =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    // ---- The ground encoding enumerates the terms. --------------------------
    {
        const Translation t = run(kFour, "ground");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // Include all four indices exactly once in native distinct.
        assert(selects(smt) == 4);
        assert(has(smt, "(distinct "));
        assert(has(smt, "(Array Int Int)"));
        assert(!has(smt, "forall"));
    }

    // ---- The quantified encoding does not. ----------------------------------
    {
        const Translation t = run(kFour, "quantified");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "forall"));
        assert(selects(smt) == 2);
    }

    // ---- ...and the difference is a function of size, not a constant. -------
    // The point of having both encodings. Doubling the array doubles the
    // ground form and leaves the quantified one alone; a test on one size
    // cannot tell the two encodings apart from two spellings of one.
    {
        const char* eight =
            "array[1..8] of var int: a;\n"
            "constraint alldifferent(a);\n"
            "solve satisfy;\n";
        const Translation g = run(eight, "ground");
        const Translation q = run(eight, "quantified");
        assert(g.ok() && q.ok());
        assert(selects(g.toSmt2()) == 8);
        assert(selects(q.toSmt2()) == 2);
    }

    // ---- The index set is inclusive, and one element is a real case. --------
    // C(1,2) = 0 pairs: the constraint holds vacuously and must become `true`
    // rather than an empty conjunction, which mkOp refuses to build.
    {
        const Translation t = run(
            "array[1..1] of var int: a;\nconstraint alldifferent(a);\nsolve satisfy;\n",
            "ground");
        assert(t.ok());
        assert(selects(t.toSmt2()) == 0);
    }
    {
        // Two elements: exactly one pair. The smallest size at which the
        // constraint says anything, and the one an off-by-one turns into zero.
        const Translation t = run(
            "array[1..2] of var int: a;\nconstraint alldifferent(a);\nsolve satisfy;\n",
            "ground");
        assert(t.ok());
        assert(selects(t.toSmt2()) == 2);
    }

    // ---- The same model under `default`, which is the point. ----------------
    {
        // Until 2026-08-16 this was refused with E_PASS_PIPELINE. `default`'s
        // pipeline was empty -- correct for the walking skeleton, and false
        // from the moment Hir::Global existed -- so the profile the CLI uses
        // with no flag could not translate the most ordinary constraint model
        // there is, while naming, in the error, the registered exact() pass
        // that would have handled it.
        //
        // No coverage table could show this: the frontend read `alldifferent`
        // perfectly and the refusal happened a layer above it. What made it
        // visible was running the corpus under two profiles and asking why the
        // counts differed.
        const Translation t = run(
            "array[1..2] of var int: a;\nconstraint alldifferent(a);\nsolve satisfy;\n",
            "default");
        assert(t.ok());
        // Decomposed, not merely accepted: `alldifferent` must be gone from the
        // output. A profile that admitted the feature and lowered it to a
        // literal `alldifferent` application would also pass `t.ok()`, and no
        // other solver would read the result.
        const std::string smt = t.toSmt2();
        assert(smt.find("alldifferent") == std::string::npos);
        assert(selects(smt) == 2);
        // And the ground encoding is the one that ran, recorded per construct
        // rather than inferred from the profile id.
        bool distinct = false;
        for (const EncodingChoice& c : t.report().choices()) {
            if (c.strategy == "alldifferent-distinct") { distinct = true; }
        }
        assert(distinct);
        // Exact, both encodings being exact -- the change moved no floor.
        assert(t.report().fidelity().sound && t.report().fidelity().complete && t.report().fidelity().preserves_optimum && t.report().fidelity().bounds.empty() && t.report().fidelity().count_status == CountStatus::UNASSESSED);
    }

    // ---- And under every other built-in profile. ----------------------------
    {
        // `bmc` and `bv32` were left refusing for one round after `default` was
        // fixed, on the reasoning that a narrower profile's scope is its own
        // business. That confused two things: a profile declares what it will
        // not PRESERVE through its fidelity floor, and an empty pipeline does
        // not decline to encode a global constraint, it makes the model
        // unanswerable. Those are different answers to a benchmark harness.
        //
        // Driven from a MiniZinc source rather than from the profile table,
        // because what has to hold is that a MODEL translates -- a pipeline
        // containing the right pass id can still be misordered or misread.
        const char* kSrc =
            "array[1..2] of var int: a;\nconstraint alldifferent(a);\nsolve satisfy;\n";
        for (const char* profile : {"default", "strict", "ground", "quantified",
                                    "bmc", "bv32"}) {
            const Translation t = run(kSrc, profile);
            if (!t.ok()) {
                std::cout << "  refused under '" << profile << "': "
                          << t.diagnostics().all().front().message << "\n";
                assert(false);
            }
            // Decomposed, not merely admitted: a pipeline that let the feature
            // through to HirToParser would be an internal error, and one that
            // emitted a literal `alldifferent` application would produce a
            // script no other solver reads.
            assert(t.toSmt2().find("alldifferent") == std::string::npos);
        }
    }
    {
        // bv32 runs two passes over the same model, and both effects must
        // survive: the global is gone AND the unbounded ints are clamped. A
        // pipeline where one pass undid or shadowed the other would still
        // report ok().
        const Translation t = run(
            "array[1..2] of var int: a;\nvar int: x;\n"
            "constraint alldifferent(a);\nconstraint x > 0;\nsolve satisfy;\n",
            "bv32");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(smt.find("alldifferent") == std::string::npos);
        assert(has(smt, "2147483647"));           // the width bound reached x
        assert(!t.report().fidelity().complete);
        assert(!t.report().fidelity().preserves_optimum);
        // Bounding the integer domain explicitly makes no count guarantee.
        assert(t.report().fidelity().count_status == CountStatus::NO_GUARANTEE);
    }

    // ---- Indexing, and the bound MiniZinc has that SMT-LIB does not. --------
    {
        const Translation t = run(
            "array[1..3] of var int: a;\nconstraint a[1] < a[3];\nsolve satisfy;\n",
            "default");
        assert(t.ok());
        assert(selects(t.toSmt2()) == 2);
    }
    {
        // An SMT-LIB array is total, so `a[4]` on a 1..3 array would lower to a
        // perfectly well-formed select denoting an unconstrained value. In
        // MiniZinc it is an error, and the frontend is the only place that
        // still knows the index set.
        const Translation t = run(
            "array[1..3] of var int: a;\nconstraint a[4] > 0;\nsolve satisfy;\n",
            "default");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        assert(t.diagnostics().all()[0].message.find("index set") != std::string::npos);
    }
    {
        // ...and index 0 is out of a 1-based set, which is the other end of the
        // same check and the one a 0-based reader forgets.
        const Translation t = run(
            "array[1..3] of var int: a;\nconstraint a[0] > 0;\nsolve satisfy;\n",
            "default");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
    }

    // ---- alldifferent over a non-array, and over nothing. -------------------
    {
        const Translation t = run(
            "var int: x;\nconstraint alldifferent(x);\nsolve satisfy;\n", "ground");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
    }
    {
        const Translation t = run(
            "constraint alldifferent(nosuch);\nsolve satisfy;\n", "ground");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
    }

    // ---- A Bool array is an array too. --------------------------------------
    // The element sort reaches the emitted sort rather than defaulting to Int.
    {
        const Translation t = run(
            "array[1..3] of var bool: b;\nconstraint b[2];\nsolve satisfy;\n",
            "default");
        assert(t.ok());
        assert(has(t.toSmt2(), "(Array Int Bool)"));
    }

    std::cout << "All MiniZinc array/global tests passed." << std::endl;
    return 0;
}
