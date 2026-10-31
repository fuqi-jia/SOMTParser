// The frontend's channel into the TranslationReport.
//
// The project's claim is per-instance recorded fidelity. Until this channel
// existed, the layer that makes most of the encoding decisions -- the frontend
// -- could not write to the record: ParseOutcome carried a model and
// diagnostics and nothing else, so an MPS reader choosing between three
// admissible readings of a bound, or a WBO reader choosing between two
// threshold encodings, could only leave a warning in a terminal. A warning is
// not a record; nothing downstream can stratify on it.
//
// What each test below guards is that a decision REACHES the report. The
// failure they exist to catch is silent: the translation still succeeds, the
// script is still correct, and the report simply does not say which of two
// different encodings produced it. That is invisible until someone tries to
// explain a solver-time difference months later.
//
// Two things deliberately NOT asserted as degradation:
//
//   * TPTP's conjecture negation is recorded exact(). `axioms |= C` holds
//     exactly when `axioms AND NOT C` is unsatisfiable, so the reduction loses
//     nothing. Marking it unsound would put a false approximation into the very
//     column the results tables stratify on. What the record has to carry is
//     the DIRECTION of the verdict, and that is the rationale's job.
//   * WBO's two threshold branches both carry exact-valued flags. They are
//     still two different scripts -- one with relaxation variables and an
//     objective, one with native soft constraints -- and `strategy` is the only
//     field that distinguishes them.

#include "somtparser/translation/translate.h"
#include "somtparser/translation/language.h"
#include "somtparser/languages/register_all.h"

#include <cassert>
#include <iostream>
#include <string>

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

bool has(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

Translation runFile(const std::string& path, const std::string& lang) {
    Lang::SourceUnit u;
    u.main_path = path;
    u.display_name = path;
    TranslateOptions opts;
    opts.language_id = lang;
    return translate(u, opts);
}

Translation runStr(const std::string& src, const std::string& lang,
                   const std::string& name) {
    Lang::SourceUnit u;
    u.main_path = name;
    u.display_name = name;
    u.inline_source = src;
    TranslateOptions opts;
    opts.language_id = lang;
    return translate(u, opts);
}

/** Find a choice by its unified_op. Returns nullptr when absent, which is the
 *  state every one of these tests is here to rule out. */
const EncodingChoice* choiceFor(const Translation& t, const std::string& op) {
    for (const EncodingChoice& c : t.report().choices()) {
        if (c.unified_op == op) { return &c; }
    }
    return nullptr;
}

} // namespace

int main() {
    std::cout << "======= frontend fidelity channel =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    // ---- TPTP: the inverted verdict mapping is recorded, not just warned. ---
    {
        const Translation t =
            runStr("fof(g, conjecture, ![X] : (p(X) => p(X))).\n", "tptp", "g.p");
        assert(t.ok());
        const EncodingChoice* c = choiceFor(t, "conjecture");
        // Before the channel existed this was a diagnostic note and nothing
        // else, so `choices()` was empty for every TPTP instance ever run.
        assert(c != nullptr);
        assert(c->strategy == "negate-and-refute");
        // The rationale has to state the direction: a reader who has only the
        // fidelity flags cannot tell that UNSAT means Theorem here and the
        // opposite everywhere else in the corpus.
        assert(has(c->rationale, "inverted"));
        assert(has(c->rationale, "CounterSatisfiable"));
        // Exact on purpose -- see the header comment.
        assert(c->fidelity.sound && c->fidelity.complete && c->fidelity.preserves_optimum && c->fidelity.bounds.empty() && c->fidelity.count_status == CountStatus::UNASSESSED);
        assert(t.report().fidelity().sound && t.report().fidelity().complete && t.report().fidelity().preserves_optimum && t.report().fidelity().bounds.empty() && t.report().fidelity().count_status == CountStatus::UNASSESSED);
    }
    {
        // An axiom-only file makes no such choice, so the channel must be
        // empty. Without this, a frontend that recorded the choice
        // unconditionally would pass every assertion above and describe
        // every instance as having a negated conjecture.
        const Translation t = runStr("fof(a, axiom, p(c)).\n", "tptp", "a.p");
        assert(t.ok());
        assert(choiceFor(t, "conjecture") == nullptr);
    }

    // ---- WBO: which threshold encoding ran. --------------------------------
    {
        // Threshold above the total cost: vacuous, so option B.
        const Translation t = runStr(
            "* #variable= 2 #constraint= 2\nsoft: 100 ;\n"
            "[1] +1 x1 >= 1 ;\n[1] +1 x2 >= 1 ;\n", "opb", "v.wbo");
        assert(t.ok());
        const EncodingChoice* c = choiceFor(t, "wbo-threshold");
        assert(c != nullptr);
        assert(c->strategy == "option-b-native-soft");
    }
    {
        // Threshold at or below the total cost: it constrains, so option A.
        const Translation t = runStr(
            "* #variable= 2 #constraint= 2\nsoft: 1 ;\n"
            "[1] +1 x1 >= 1 ;\n[1] +1 x2 >= 1 ;\n", "opb", "c.wbo");
        assert(t.ok());
        const EncodingChoice* c = choiceFor(t, "wbo-threshold");
        assert(c != nullptr);
        assert(c->strategy == "option-a-relaxation-vars");
    }
    {
        // The mechanical claim neither half can be deleted on its own: the same
        // two soft constraints under two thresholds produce DIFFERENT scripts,
        // and the report says which is which. A frontend that recorded a fixed
        // strategy string would satisfy each assertion above in isolation and
        // fail here.
        const char* body = "[1] +1 x1 >= 1 ;\n[1] +1 x2 >= 1 ;\n";
        const Translation vac =
            runStr(std::string("soft: 100 ;\n") + body, "opb", "a.wbo");
        const Translation con =
            runStr(std::string("soft: 1 ;\n") + body, "opb", "b.wbo");
        assert(vac.ok() && con.ok());
        assert(vac.toSmt2() != con.toSmt2());
        assert(choiceFor(vac, "wbo-threshold")->strategy
                   != choiceFor(con, "wbo-threshold")->strategy);
    }

    // ---- MPS: the reader divergence is on the record. ----------------------
    {
        const Translation t = runFile("languages/mps/instances/ok/up_negative.mps", "mps");
        assert(t.ok());
        const EncodingChoice* c = choiceFor(t, "BOUNDS UP");
        assert(c != nullptr);
        assert(c->strategy == "cplex-negative-up-opens-lower");
        // Naming the rule is the point: a row produced under CPLEX's reading is
        // not comparable with one produced by a reader that keeps the lower
        // bound at 0, and only the record can say which ran.
        assert(has(c->rationale, "CPLEX"));
        // `UP 0` is the third behaviour and is NOT this case, so a frontend
        // that fired on any non-positive value would be caught here.
        assert(has(c->rationale, "-infinity"));
    }
    {
        // The second N row. Added after a breakage probe deleted this record
        // and every test still passed: the choice was being written and
        // nothing asserted it, which is the same "recorded but unguarded"
        // shape as an obligation that is entailed rather than enforced.
        const Translation t = runFile("languages/mps/instances/ok/second_n_row.mps", "mps");
        assert(t.ok());
        const EncodingChoice* c = choiceFor(t, "N row");
        assert(c != nullptr);
        assert(c->strategy == "first-n-row-is-objective");
        // Which row won has to be in the record: the convention is not
        // universal, and a reader that took the last N row would produce a
        // different objective from the same file.
        assert(has(c->rationale, "second N row"));
    }
    {
        // A single N row is the ordinary case and makes no choice at all.
        const Translation t = runFile("languages/mps/instances/ok/doc_example.mps", "mps");
        assert(t.ok());
        assert(choiceFor(t, "N row") == nullptr);
    }

    // ---- MiniZinc: predicate inlining, once per predicate. -----------------
    {
        const Translation t = runStr(
            "predicate pos(var int: a) = a > 0;\n"
            "var int: x;\nvar int: y;\n"
            "constraint pos(x);\nconstraint pos(y);\n"
            "solve satisfy;\n", "minizinc", "p.mzn");
        assert(t.ok());
        const EncodingChoice* c = choiceFor(t, "predicate");
        assert(c != nullptr);
        assert(c->strategy == "inline-at-call-site");
        // Two call sites, one entry: the record's size must describe the
        // decision, not how often the model happened to use the predicate.
        int n = 0;
        for (const EncodingChoice& e : t.report().choices()) {
            if (e.unified_op == "predicate") { ++n; }
        }
        assert(n == 1);
    }
    {
        // Two distinct predicates are two decisions, so two entries. Without
        // this, a frontend that recorded the first inlining and then never
        // again would pass the test above.
        const Translation t = runStr(
            "predicate pos(var int: a) = a > 0;\n"
            "predicate neg(var int: a) = a < 0;\n"
            "var int: x;\nvar int: y;\n"
            "constraint pos(x);\nconstraint neg(y);\n"
            "solve satisfy;\n", "minizinc", "q.mzn");
        assert(t.ok());
        int n = 0;
        for (const EncodingChoice& e : t.report().choices()) {
            if (e.unified_op == "predicate") { ++n; }
        }
        assert(n == 2);
    }

    // ---- The aggregate meets rather than being copied. ---------------------
    {
        // A frontend choice and whatever the passes and lowering contribute
        // both land in one report, and the aggregate is their meet. Asserting
        // the count is what catches a merge that overwrites instead of folding.
        const Translation t =
            runStr("fof(g, conjecture, p(c)).\n", "tptp", "m.p");
        assert(t.ok());
        assert(t.report().choices().size() >= 1);
        Fidelity expected = Fidelity::exact();
        for (const EncodingChoice& c : t.report().choices()) {
            expected = Fidelity::meet(expected, c.fidelity);
        }
        assert(t.report().fidelity().sound == expected.sound);
        assert(t.report().fidelity().complete == expected.complete);
        assert(t.report().fidelity().preserves_optimum == expected.preserves_optimum);
    }

    // ---- A failed parse contributes no choices. ----------------------------
    {
        // Choices from a parse that produced no model describe a translation
        // that does not exist; an experiment row carrying them could not be
        // reproduced. The diagnostics are where a failure is reported.
        const Translation t = runStr("fof(broken, conjecture, \n", "tptp", "x.p");
        assert(!t.ok());
        assert(t.report().choices().empty());
    }

    // ---- The choice survives into the serialised record. -------------------
    {
        // The report only matters because it reaches the evaluation database.
        // A choice that is in memory and not in the JSON is not recorded.
        const Translation t =
            runStr("fof(g, conjecture, p(c)).\n", "tptp", "j.p");
        assert(t.ok());
        const std::string json = t.report().toJson();
        assert(has(json, "negate-and-refute"));
        assert(has(json, "CounterSatisfiable"));
    }

    std::cout << "All fidelity-channel tests passed." << std::endl;
    return 0;
}
