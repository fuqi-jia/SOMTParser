// The WCNF (MaxSAT) frontend, and the three obligations docs/languages/wcnf.md
// wrote down before it existed.
//
// All three are about the same question -- **which clauses are hard** -- and
// each is silent when got wrong, because the constraints are all still there
// either way:
//
//   old format   a clause whose weight is >= `top` is HARD, not a soft clause at
//                a large cost. Read as soft, the instance stays answerable and
//                becomes strictly more permissive: hard constraints turn
//                violable at a price, so the optimum found is not the one asked
//                for.
//   new format   a clause with no leading weight is hard, and the ABSENCE of a
//                weight is the declaration -- the `h` marker's job, not a
//                default.
//   both         soft clauses are JOINTLY optimised: the objective is the sum of
//                the violated weights, which no single clause states.
//
// The strongest thing this file does is translate the same instance in both
// formats and assert the two agree. wcnf.md §2.2 says they are the same problem;
// if either reading of `top` were wrong, they would not be.

#include "somtparser/translation/translate.h"
#include "somtparser/languages/wcnf.h"
#include "somtparser/languages/register_all.h"
#include "somtparser/frontend/parser.h"

#include <cassert>

#include "test_helpers.h"
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

Translation run(const std::string& src, bool strict = false) {
    Lang::SourceUnit u;
    u.main_path = "t.wcnf";
    u.display_name = "t.wcnf";
    u.inline_source = src;
    TranslateOptions opts;
    opts.language_id = "wcnf";
    opts.parse.strict = strict;
    return translate(u, opts);
}

Translation runFile(const std::string& path) {
    Lang::SourceUnit u;
    u.main_path = path;
    u.display_name = path;
    TranslateOptions opts;
    opts.language_id = "wcnf";
    return translate(u, opts);
}

} // namespace

int main() {
    std::cout << "======= WCNF (MaxSAT) frontend =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    Lang::Language* w = Lang::LanguageRegistry::instance().byId("wcnf");
    assert(w != nullptr);
    assert(w->extensions().size() == 1 && w->extensions()[0] == ".wcnf");

    // ---- The two formats describe the same instance. ------------------------
    // wcnf.md §2.2 says so in as many words: top = 12 and the first clause's
    // weight is 12, "so it is hard -- the same instance as §2.1's". This is the
    // assertion that catches either reading of `top` being wrong, because a
    // misreading breaks the agreement without breaking either file.
    {
        const Translation nf = runFile("languages/wcnf/instances/ok/new_format.wcnf");
        const Translation of = runFile("languages/wcnf/instances/ok/old_format.wcnf");
        assert(nf.ok() && of.ok());

        const std::string ns = nf.toSmt2();
        const std::string os = of.toSmt2();
        // BYTE-IDENTICAL. §2.2 says they are the same instance, and this is the
        // strongest form of that claim -- stronger than counting clauses, and it
        // is what a misreading of `top` breaks without breaking either file on
        // its own.
        assert(ns == os);
        // One hard clause, three soft ones.
        assert(count(ns, "(assert-soft") == 3);
        assert(count(ns, "(assert (") == 1);
        // The same weights survive: 1, 6, 4.
        for (const char* wgt : {":weight 1", ":weight 6", ":weight 4"}) {
            assert(has(ns, wgt));
            assert(has(os, wgt));
        }
        // ...and no soft clause carries the hard clause's weight, which is what
        // reading `top` as "a big cost" would produce.
        assert(!has(ns, ":weight 12"));
        assert(!has(os, ":weight 12"));

        ParserPtr reader = newParser();
        assert(reader->parseStr(os));
    }

    // ---- `top` is a marker, not a threshold. --------------------------------
    // >= top is hard, and a weight far above top is hard too. wcnf.md §2.2 draws
    // the line against WBO, whose `soft: T ;` is a hard admissibility BOUND --
    // an assignment whose cost reaches T is not a solution at all. Translating
    // either with the other's meaning changes the answer.
    {
        const Translation t =
            runFile("languages/wcnf/instances/ok/weight_above_top.wcnf");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(count(smt, "assert-soft") == 1);          // only the weight-3 one
        assert(has(smt, ":weight 3"));
        assert(!has(smt, ":weight 99"));                 // 99 >= 10, so hard
    }
    {
        // Exactly at top is hard: `>=`, not `>`. Off by one here silently turns
        // one hard clause soft.
        const Translation t = run("p wcnf 2 2 10\n10 1 0\n9 -2 0\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(count(smt, "assert-soft") == 1);
        assert(has(smt, ":weight 9"));
        assert(!has(smt, ":weight 10"));
    }

    // ---- No `top` field: weighted MaxSAT with NO hard clauses. --------------
    // There is no marker to compare against, so a weight of 50 is just a weight.
    {
        const Translation t = runFile("languages/wcnf/instances/ok/no_top.wcnf");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(count(smt, "assert-soft") == 2);
        assert(has(smt, ":weight 50"));
    }

    // ---- `p cnf` in a .wcnf file: unweighted MaxSAT. ------------------------
    // Every clause soft at 1, and no clause carries a leading weight -- so the
    // first token of each line is a LITERAL and must not be eaten as a weight.
    {
        const Translation t = runFile("languages/wcnf/instances/ok/unweighted.wcnf");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(count(smt, "assert-soft") == 2);
        assert(t.report().stats().num_vars == 2);
        // Both literals of the first clause survived: reading `1` as a weight
        // would have left a one-literal clause.
        assert(has(smt, "x1"));
        assert(has(smt, "x2"));
    }

    // ---- The new format's hard marker. --------------------------------------
    {
        // `h` and only `h` makes a clause hard here. A clause with a weight is
        // soft however large the weight, because the new format has no `top`.
        const Translation t = run("h 1 0\n999999 -1 0\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(count(smt, "assert-soft") == 1);
        assert(has(smt, ":weight 999999"));
    }
    {
        // No problem line at all is normal in the new format, and the variable
        // count comes from the clauses.
        const Translation t = run("h 1 5 0\n2 -3 0\n");
        assert(t.ok());
        assert(t.report().stats().num_vars == 5);
    }

    // ---- A soft empty clause is a constant cost. ----------------------------
    // Not the same as a hard one, which makes the instance unsatisfiable. And
    // mkOp(OR, {}) throws rather than producing false, so both are branches.
    {
        const Translation t =
            runFile("languages/wcnf/instances/ok/soft_empty_clause.wcnf");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "assert-soft false") || has(smt, "assert-soft (false"));
        assert(has(smt, ":weight 5"));
    }
    {
        // The hard one, for contrast.
        const Translation t = run("h 0\n1 1 0\n");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(assert false)"));
    }

    // ---- Soft constraints reach the target as soft. -------------------------
    // The property the old refusal in HirToParser was protecting: hardening a
    // soft clause changes the problem from "violate this at cost w" to "never
    // violate this", which can turn a satisfiable MaxSAT instance UNSAT.
    {
        const Translation t = runFile("languages/wcnf/instances/ok/new_format.wcnf");
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // Exactly one hard assertion; the rest are soft. Counted as
        // `(assert (` so that `(assert-soft` is not matched -- subtracting one
        // count from the other underflows a size_t when there are more soft
        // clauses than hard ones, which is the normal case for MaxSAT.
        assert(count(smt, "(assert (") == 1);
        assert(count(smt, "(assert-soft") == 3);
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }

    // ---- Malformed files. ---------------------------------------------------
    {
        // A weight must be positive: a non-positive one is not "free to
        // violate", it is a malformed file.
        const Translation t =
            runFile("languages/wcnf/instances/reject/negative_weight.wcnf");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
    }
    {
        const Translation t = runFile("languages/wcnf/instances/reject/unterminated.wcnf");
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "terminated"));
    }
    {
        const Translation t = runFile("languages/wcnf/instances/reject/bad_marker.wcnf");
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "neither"));
    }
    {
        const Translation t = runFile("languages/wcnf/instances/nosuch.wcnf");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_IO);
    }
    {
        // The old format's header is still checked against the content, the way
        // dimacs-cnf.md §4.2 prescribes.
        const Translation t = run("p wcnf 2 9 10\n1 1 0\n", /*strict=*/true);
        assert(!t.ok());
    }

    {
        // A comment is a line whose FIRST CHARACTER is `c`. The space after it
        // is conventional, not required: the MaxSAT Evaluation's own
        // standardised instances open with `c{` and continue `c "sha1sum": …`,
        // a JSON metadata block written one line at a time with no separator.
        // Comparing the first whitespace-delimited TOKEN to "c" refused every
        // one of them with E_PARSE -- reporting a well-formed file as
        // malformed input, which is the wrong bucket as well as the wrong
        // answer. Found by vendoring a corpus: 10 of the 25 files failed, and
        // no hand-written fixture had covered the shape.
        const Translation t = run("c{\nc \"nvars\": 2\nc}\nh 1 2 0\n3 -1 0\n");
        VERIFY(t.ok());

        // The old format's header is still reached past such a block.
        const Translation old_format = run("c{\nc}\np wcnf 2 2 10\n10 1 0\n9 -2 0\n");
        VERIFY(old_format.ok());
    }

    std::cout << "All WCNF tests passed." << std::endl;
    return 0;
}
