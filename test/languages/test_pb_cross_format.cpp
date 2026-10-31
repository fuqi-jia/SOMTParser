// WCNF's `top` and WBO's `T` are the same word for two different things, and
// this file is where that is said.
//
//     WCNF `top`     a MARKER on weights. A clause whose weight is >= top is
//                    HARD. It says nothing about the total cost, and an
//                    assignment of any cost is a solution.
//     WBO  `soft: T` a hard ADMISSIBILITY BOUND. The total cost of the violated
//                    soft constraints must be STRICTLY LESS THAN T. An
//                    assignment whose cost reaches T is not a solution at all,
//                    and the instance can be UNSATISFIABLE even though a
//                    minimum-cost assignment exists.
//
// docs/languages/wcnf.md §2.2 draws the line and docs/languages/opb-wbo.md §2.4
// draws it from the other side, both in prose. This is the executable form.
//
// Neither frontend can see the difference alone: each reading is coherent
// within its own format, and swapping them produces a well-formed script in
// both directions. The failure is one-sided and silent -- WBO's reading applied
// to WCNF adds a threshold the file never stated, and WCNF's reading applied to
// WBO drops one it did, which ADMITS assignments the format rejects. That
// second direction is the format document's own Example 3: minimum cost exactly
// 6 with `soft: 6;`, where the correct answer is UNSATISFIABLE and the dropped
// threshold reports an optimum instead.

#include "somtparser/translation/translate.h"
#include "somtparser/languages/register_all.h"

#include <cassert>
#include <iostream>
#include <string>
#include <vector>

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

bool has(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

Translation run(const char* language, const std::string& src, const char* ext) {
    Lang::SourceUnit u;
    u.main_path = std::string("t") + ext;
    u.display_name = u.main_path;
    u.inline_source = src;
    TranslateOptions opts;
    opts.language_id = language;
    return translate(u, opts);
}

void singleMinimization(const Translation& translation) {
    assert(translation.objectiveCount() == 1);
    assert(translation.report().stats().num_objectives == 1);
    const std::vector<Hir::ObjKind> directions = {Hir::ObjKind::MINIMIZE};
    assert(!translation.semantics().stages().empty());
    for (const auto& stage : translation.semantics().stages()) {
        assert(stage.objectives.source == Sem::ObjectiveOrder::MINIMIZE);
        assert(stage.objectives.target == Sem::ObjectiveOrder::MINIMIZE);
        assert(stage.objectives.source_directions == directions);
        assert(stage.objectives.target_directions == directions);
        assert(stage.objectives.order_preserving && stage.objectives.order_reflecting);
    }
}

} // namespace

int main() {
    std::cout << "======= pseudo-Boolean cross-format obligations =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    // Two instances of the same shape: two soft items of cost 2 and 3, and a
    // limit written `5`. In WCNF that 5 is a weight marker; in WBO it is a cost
    // bound. The number is the same and it means different things.
    const Translation wcnf =
        run("wcnf", "p wcnf 2 2 5\n2 1 0\n3 -2 0\n", ".wcnf");
    const Translation wbo =
        run("opb", "soft: 5 ;\n[2] 1 x1 >= 1 ;\n[3] 1 x2 >= 1 ;\n", ".wbo");
    assert(wcnf.ok() && wbo.ok());

    const std::string ws = wcnf.toSmt2();
    const std::string bs = wbo.toSmt2();

    // ---- WCNF: `top` marks weights, and constrains no total. ----------------
    // Both clauses have weight below 5, so both stay soft, and there is no
    // bound on what they may cost together.
    assert(has(ws, "assert-soft"));
    assert(has(ws, ":weight 2"));
    assert(has(ws, ":weight 3"));
    // The soft group is one minimization objective; it does not impose a
    // hard admissibility threshold or need a separate arithmetic command.
    singleMinimization(wcnf);
    assert(!has(ws, "define-objective"));
    assert(wcnf.parser()->getAssertions().empty());
    assert(wcnf.parser()->getSoftAssertions().size() == 2);
    assert(!has(wcnf.toSmt2(Lower::OmtDialect::Z3), "(minimize "));

    // ---- WBO: `T` bounds the total, and that changes the model. -------------
    // 2 + 3 = 5 is not strictly less than 5, so the all-violated assignment is
    // not admissible. The threshold has to appear as a hard constraint.
    singleMinimization(wbo);
    assert(wbo.parser()->getSoftAssertions().empty());
    assert(has(bs, "define-objective"));
    assert(has(wbo.toSmt2(Lower::OmtDialect::Z3), "(minimize "));
    assert(has(bs, "!r0"));                       // relaxation variables
    assert(has(bs, "!r1"));

    // Both metadata vectors contain one minimized cost. Their hard feasible
    // sets differ: WCNF has no hard assertion here; WBO has the exact strict
    // threshold over its relaxation variables. Compare the parsed assertion,
    // not only a printed numeral or the number of objectives.
    auto expected_threshold = newParser();
    assert(expected_threshold->parseStr(
        "(declare-fun !r0 () Int)(declare-fun !r1 () Int)"
        "(assert (<= (+ (* 2 !r0) (* 3 !r1)) 4))"));
    const auto expected = expected_threshold->toString(
        expected_threshold->getAssertions().front());
    bool found_threshold = false;
    for (const auto& assertion : wbo.parser()->getAssertions()) {
        found_threshold |= wbo.parser()->toString(assertion) == expected;
    }
    assert(found_threshold);

    // ---- The threshold is STRICT, and that is where the answer lives. -------
    // Cost must be < T, so the emitted bound is T - 1. Writing `<= T` would
    // admit exactly the assignments the format rejects -- and on the format
    // document's Example 3 that is the difference between UNSATISFIABLE and a
    // reported optimum.
    assert(has(bs, " 4)"));
    assert(!has(bs, "(<= (+ (* !r0 2) (* !r1 3)) 5)"));

    // ---- And WCNF's marker really is a marker. ------------------------------
    // Raise one clause's weight to 5 and it becomes HARD -- the threshold
    // reading would instead have left it soft and made the instance
    // infeasible. Same file shape, one digit changed, and the two readings
    // diverge on exactly that digit.
    {
        const Translation t = run("wcnf", "p wcnf 2 2 5\n5 1 0\n3 -2 0\n", ".wcnf");
        assert(t.ok());
        const std::string s = t.toSmt2();
        assert(has(s, ":weight 3"));
        assert(!has(s, ":weight 5"));            // weight 5 clause is hard now
        // A single-literal clause prints bare, so the hard one is `(assert x1)`
        // rather than `(assert (...))` -- asserted on the semantics of "there
        // is a hard assertion" and not on a shape the builders may simplify.
        assert(has(s, "(assert x1)"));
    }
    {
        // The WBO counterpart of "one digit changed": T = 6 makes the same
        // instance vacuous, because 5 < 6. The threshold disappears and the
        // translation becomes native soft constraints -- so WBO's number is
        // load-bearing in a way WCNF's is not.
        const Translation t =
            run("opb", "soft: 6 ;\n[2] 1 x1 >= 1 ;\n[3] 1 x2 >= 1 ;\n", ".wbo");
        assert(t.ok());
        const std::string s = t.toSmt2();
        assert(has(s, "assert-soft"));
        assert(!has(s, "!r0"));
        singleMinimization(t);
        assert(t.parser()->getSoftAssertions().size() == 2);
        assert(!has(s, "define-objective"));
        const Translation unbounded = run("opb",
            "soft: ;\n[2] 1 x1 >= 1 ;\n[3] 1 x2 >= 1 ;\n", ".wbo");
        assert(unbounded.ok());
        singleMinimization(unbounded);
        assert(s == unbounded.toSmt2());
    }

    // ---- What the two formats agree on. -------------------------------------
    // The disagreement is one word, not a general divergence, so a reader who
    // over-corrects is as wrong as one who under-corrects.
    {
        // Both carry per-item costs into `assert-soft` when nothing binds, and
        // both mean by it "cost incurred exactly when violated".
        const Translation w = run("wcnf", "p wcnf 1 1 99\n7 1 0\n", ".wcnf");
        const Translation b = run("opb", "soft: ;\n[7] 1 x1 >= 1 ;\n", ".wbo");
        assert(w.ok() && b.ok());
        assert(has(w.toSmt2(), ":weight 7"));
        assert(has(b.toSmt2(), ":weight 7"));
    }
    {
        // And both treat a cost of zero or below as malformed rather than as
        // "free to violate".
        assert(!run("wcnf", "p wcnf 1 1 9\n0 1 0\n", ".wcnf").ok());
        assert(!run("opb", "soft: 9 ;\n[0] 1 x1 >= 1 ;\n", ".wbo").ok());
    }

    std::cout << "All pseudo-Boolean cross-format tests passed." << std::endl;
    return 0;
}
