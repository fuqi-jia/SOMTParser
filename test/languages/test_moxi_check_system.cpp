// What a published MoXI `check-system` says.
//
// The frontend read `check-system` as a place to find `:invariant` and
// `:reachable` formulas. It is three things more than that, and each one was a
// wrong answer rather than a missing feature.
//
//   1. **A condition carries a NAME.** The corpus writes
//      `:reachable (rch (= o #b00001010))`, and the whole of that was asserted
//      as a formula -- so `rch` became a function applied to the equality. The
//      symptom was the ENGINE's `Unknown or unexpected symbol "rch"`, naming a
//      line in a generated script the reader has never seen, for a file whose
//      own text is unimpeachable.
//
//      Queries select these condition names. Keyword references and a
//      check-system `:invariant` are not part of the published grammar.
//
//   2. **A `check-system` RESTATES the interface, under names of its own.**
//      `:input ((i (_ BitVec 8)))` against the system's `:input ((in ...))`
//      IDENTIFIES `i` with `in` positionally. They are one variable -- not two
//      joined by an equation -- which is the same trap §4.2 records for a
//      subsystem's argument list, one level up. Undeclared, the condition's `i`
//      surfaced as the engine's `Unknown or unexpected symbol "i"`.
//
//   3. **A condition not named by the query is NOT CHECKED.** §2.4 says so, and
//      the frontend translated every condition it found. That does not fail; it
//      answers a question the file did not ask, which is worse.
//
// The remaining obligations tested here are semantic: `:current` replaces IS,
// reachability conditions are conjoined eventualities, and finite depth n still
// provides state n+1 for primed formulas.

#include "somtparser/languages/register_all.h"
#include "somtparser/translation/language.h"
#include "somtparser/translation/translate.h"

#include <iostream>
#include <string>

#include "test_helpers.h"

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

bool has(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

std::size_t count(const std::string& hay, const std::string& needle) {
    std::size_t n = 0;
    for (std::size_t p = hay.find(needle); p != std::string::npos;
         p = hay.find(needle, p + needle.size())) {
        ++n;
    }
    return n;
}

Translation run(const std::string& src, int depth = 2,
                const std::string& query = {}, int check_index = -1) {
    Lang::SourceUnit u;
    u.main_path = "t.moxi";
    u.display_name = "t.moxi";
    u.inline_source = src;
    TranslateOptions opts;
    opts.language_id = "moxi";
    opts.profile_id = "bmc";
    opts.parse.options["bmc_depth"] = std::to_string(depth);
    if (!query.empty()) { opts.parse.options["query"] = query; }
    if (check_index >= 0) {
        opts.parse.options["check_index"] = std::to_string(check_index);
    }
    return translate(u, opts);
}

/** The concatenated diagnostic messages, for asserting what was reported. */
std::string messages(const Translation& t) {
    std::string all;
    for (const Diagnostic& d : t.diagnostics().all()) { all += d.message + "\n"; }
    return all;
}

/** No diagnostic may be a raw engine message. The engine reports against a
 *  GENERATED script, so its line numbers and symbol names refer to text that is
 *  not on disk -- the one refusal shape this project rules out. */
void noEngineLeak(const Translation& t, const char* what) {
    const std::string all = messages(t);
    if (has(all, "Unknown or unexpected symbol") || has(all, "in line ")) {
        std::cout << "  a raw engine message reached the reader (" << what << "):\n"
                  << all;
        VERIFY(false);
    }
}

} // namespace

int main() {
    std::cout << "======= MoXI check-system =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    // The corpus shape: named conditions, and the check-system renaming the
    // system's variables. Both defects are in this one file.
    const std::string kModCounter =
        "(set-logic QF_BV)\n"
        "(define-system Cnt\n"
        "  :input ((in (_ BitVec 8)))\n"
        "  :output ((out (_ BitVec 8)))\n"
        "  :init (= out #b00000001)\n"
        "  :trans (= out' (bvadd out in))\n"
        ")\n"
        "(check-system Cnt\n"
        "  :input ((i (_ BitVec 8)))\n"
        "  :output ((o (_ BitVec 8)))\n"
        "  :assumption (a (= i #b00000010))\n"
        "  :reachable (rch (= o #b00001010))\n"
        "  :query (q (a rch))\n"
        ")\n";

    // ---- A condition's name is not part of its formula. ---------------------
    {
        const Translation t = run(kModCounter);
        noEngineLeak(t, "named conditions");
        if (!t.ok()) {
            std::cout << "  did not translate:\n" << messages(t);
            VERIFY(false);
        }
        const std::string smt = t.toSmt2();
        // `rch` and `a` are the conditions' NAMES. If either reached the term
        // language it would be an undeclared function symbol.
        VERIFY(!has(smt, "rch"));
        VERIFY(!has(smt, "(a "));
        // And the formulas themselves are there.
        VERIFY(has(smt, "#b00001010"));
        VERIFY(has(smt, "#b00000010"));
        // The output must be readable: this whole class of defect is a term
        // this parser built and cannot read back.
        ParserPtr reader = newParser();
        VERIFY(reader->parseStr(smt));
    }

    // ---- The check-system's names ARE the system's variables. --------------
    {
        const Translation t = run(kModCounter);
        VERIFY(t.ok());
        const std::string smt = t.toSmt2();
        // `i` was identified with `in`, so the assumption constrains the step
        // variables of `in` -- there is no separate `i` at any step.
        VERIFY(has(smt, "in@0"));
        VERIFY(has(smt, "out@0"));
        VERIFY(!has(smt, "i@0"));
        VERIFY(!has(smt, "o@0"));
        // Identification, not an equation: nothing says `i = in`. Were it an
        // equation, `i@0` would have to exist to be one side of it -- so the
        // assertion above already implies this one, and it is stated because the
        // distinction is the obligation rather than because it adds a check.
    }
    {
        // The identification is POSITIONAL, so a list of a different length
        // cannot be made to correspond and must be refused rather than
        // truncated -- truncating would drop a variable and translate the rest.
        const Translation t = run(
            "(define-system S :input ((a Int) (b Int)) :output ((c Int))\n"
            "  :init (= c 0) :trans (= c' (+ a b)))\n"
            "(check-system S :input ((x Int)) :output ((y Int))\n"
            "  :reachable (r (= y 3)) :query (q (r)))\n");
        VERIFY(!t.ok());
        VERIFY(has(messages(t), "positional"));
        noEngineLeak(t, "length mismatch");
    }
    {
        // Two names for one variable cannot have two sorts.
        const Translation t = run(
            "(define-system S :input ((a Int)) :output ((c Int))\n"
            "  :init (= c 0) :trans (= c' a))\n"
            "(check-system S :input ((x Bool)) :output ((y Int))\n"
            "  :reachable (r (= y 3)) :query (q (r)))\n");
        VERIFY(!t.ok());
        VERIFY(has(messages(t), "two sorts"));
    }
    {
        // Omitting an interface means the empty interface; it does not inherit
        // the define-system declaration implicitly.
        const Translation t = run(
            "(define-system S :input ((a Int)) :output ((c Int))\n"
            "  :trans (= c' a))\n"
            "(check-system S :query (q ()))\n");
        VERIFY(!t.ok());
        VERIFY(has(messages(t), "positional"));
    }

    // ---- A condition the query does not name is not checked. ---------------
    {
        // Two reachables, one query naming one of them. The named one is
        // translated; the other is not, and the reader is told so.
        const Translation t = run(
            "(define-system S :output ((n Int))\n"
            "  :init (= n 0) :trans (= n' (+ n 1)))\n"
            "(check-system S :output ((n Int))\n"
            "  :reachable (asked (= n 1))\n"
            "  :reachable (notasked (= n 99))\n"
            "  :query (q (asked)))\n");
        VERIFY(t.ok());
        const std::string smt = t.toSmt2();
        VERIFY(has(smt, "1"));
        // 99 appears nowhere: the condition was not translated at all, rather
        // than translated and reported separately.
        VERIFY(!has(smt, "99"));
        // And it is REPORTED -- nothing is ever silently dropped.
        VERIFY(has(messages(t), "notasked"));
        VERIFY(has(messages(t), "not named by the query"));
    }
    {
        // A query naming only an assumption still asks whether a conforming
        // trace exists; reachability conditions are optional in the grammar.
        const Translation t = run(
            "(define-system S :output ((n Int))\n"
            "  :init (= n 0) :trans (= n' (+ n 1)))\n"
            "(check-system S :output ((n Int))\n"
            "  :assumption (a (>= n 0))\n"
            "  :reachable (r (= n 1))\n"
            "  :query (q (a)))\n");
        VERIFY(t.ok());
        VERIFY(has(t.toSmt2(), ">= n@0 0"));
        VERIFY(has(t.toSmt2(), ">= n@2 0"));
    }
    {
        // Several queries are several questions, and a ConstraintModel is one.
        // Refused by name rather than merged.
        const Translation t = run(
            "(define-system S :output ((n Int))\n"
            "  :init (= n 0) :trans (= n' (+ n 1)))\n"
            "(check-system S :output ((n Int))\n"
            "  :reachable (r1 (= n 1))\n"
            "  :reachable (r2 (= n 2))\n"
            "  :query (q1 (r1))\n"
            "  :query (q2 (r2)))\n");
        VERIFY(!t.ok());
        VERIFY(has(messages(t), "separate quer"));
    }
    {
        // A selector preserves one source question instead of merging q1 and
        // q2. The unselected target value 2 must not reach the formula.
        const Translation t = run(
            "(define-system S :output ((n Int))\n"
            "  :init (= n 0) :trans (= n' (+ n 1)))\n"
            "(check-system S :output ((n Int))\n"
            "  :reachable (r1 (= n 1)) :reachable (r2 (= n 2))\n"
            "  :query (q1 (r1)) :query (q2 (r2)))\n",
            2, "q1");
        VERIFY(t.ok());
        VERIFY(has(t.toSmt2(), "1"));
        VERIFY(!has(t.toSmt2(), "(= 2 n@") && !has(t.toSmt2(), "(= n@0 2)"));
    }
    {
        const Translation t = run(
            "(define-system S :output ((n Int)) :trans (= n' n))\n"
            "(check-system S :output ((n Int))\n"
            "  :reachable (r1 (= n 1)) :reachable (r2 (= n 2))\n"
            "  :queries ((q1 (r1)) (q2 (r2))))\n",
            1, "q2");
        VERIFY(t.ok());
        VERIFY(has(t.toSmt2(), "2"));
    }
    {
        // A :queries group shares one interpretation of K. Solving q1 alone
        // would let K differ from the interpretation needed by q2, so a
        // single-result selector is not an exact translation of this group.
        const Translation t = run(
            "(declare-const K Int)\n"
            "(define-system S :output ((n Int)) :trans (= n' n))\n"
            "(check-system S :output ((n Int))\n"
            "  :reachable (r1 (= n K)) :reachable (r2 (distinct n K))\n"
            "  :queries ((q1 (r1)) (q2 (r2))))\n",
            1, "q1");
        VERIFY(!t.ok());
        VERIFY(has(messages(t), "share one rigid interpretation"));
    }

    // ---- Published named grammar only. -------------------------------------
    {
        const Translation t = run(
            "(define-system counter\n"
            "  :input ((tick Bool)) :output ((n Int))\n"
            "  :init (= n 0) :trans (= n' (ite tick (+ n 1) n)) :inv (>= n 0))\n"
            "(check-system counter\n"
            "  :input ((tick Bool)) :output ((n Int))\n"
            "  :invariant (< n 10)\n"
            "  :query (q1 (:invariant)))\n");
        VERIFY(!t.ok());
        VERIFY(has(messages(t), "published MoXI grammar"));
    }

    // ---- Several reachables are conjoined eventualities. ------------------
    {
        const Translation t = run(
            "(define-system S :output ((n Int))\n"
            "  :init (= n 0) :trans (= n' (+ n 1)))\n"
            "(check-system S :output ((n Int))\n"
            "  :reachable (one (= n 1))\n"
            "  :reachable (two (= n 2))\n"
            "  :query (q (one two)))\n");
        VERIFY(t.ok());
        const std::string smt = t.toSmt2();
        // depth 2: one init + three TS assertions + two separate eventualities.
        // A single OR across both reachables would produce only five.
        VERIFY(count(smt, "(assert") == 6);
        VERIFY(has(smt, "1") && has(smt, "2"));
    }

    // ---- `:current` replaces the initial predicate at step zero. -----------
    {
        const Translation t = run(
            "(define-system S :output ((n Int))\n"
            "  :init (= n 0) :trans (= n' (+ n 1)))\n"
            "(check-system S :output ((n Int))\n"
            "  :current (start (= n 5))\n"
            "  :reachable (six (= n 6))\n"
            "  :query (q (start six)))\n", 1);
        VERIFY(t.ok());
        const std::string smt = t.toSmt2();
        VERIFY(has(smt, "(= 5 n@0)") || has(smt, "(= n@0 5)"));
        VERIFY(!has(smt, "(= 0 n@0)") && !has(smt, "(= n@0 0)"));
        VERIFY(!has(smt, "(= 5 n@1)") && !has(smt, "(= n@1 5)"));
    }

    // ---- A depth-zero query can still mention next-state variables. --------
    {
        const Translation t = run(
            "(define-system S :input ((i Bool)) :output ((n Int))\n"
            "  :init (= n 0) :trans (= n' (ite i' 1 0)))\n"
            "(check-system S :input ((i Bool)) :output ((n Int))\n"
            "  :assumption (a i')\n"
            "  :reachable (r (= n' 1))\n"
            "  :query (q (a r)))\n", 0);
        VERIFY(t.ok());
        const std::string smt = t.toSmt2();
        VERIFY(has(smt, "i@1") && has(smt, "n@1"));
        ParserPtr reader = newParser();
        VERIFY(reader->parseStr(smt));
    }

    // ---- Formula variable roles are checked before unrolling. --------------
    {
        const Translation t = run(
            "(define-system S :output ((n Int)) :trans (= n' n))\n"
            "(check-system S :output ((n Int))\n"
            "  :assumption (a (= n' 0)) :query (q (a)))\n");
        VERIFY(!t.ok());
        VERIFY(has(messages(t), "may prime only an input"));
    }
    {
        const Translation t = run(
            "(define-system S :output ((n Int)) :trans (= n' n))\n"
            "(check-system S :output ((n Int))\n"
            "  :current (c (= n' 0)) :query (q (c)))\n");
        VERIFY(!t.ok());
        VERIFY(has(messages(t), "one-state initiality"));
    }
    {
        const Translation t = run(
            "(define-system S :output ((n Int)) :trans (= n' n))\n"
            "(check-system S :output ((n Int)) :query (q ()))\n"
            "(check-system S :output ((n Int)) :query (q2 ()))\n");
        VERIFY(!t.ok());
        VERIFY(has(messages(t), "multiple check-system"));
    }
    {
        const Translation t = run(
            "(define-system S :output ((n Int)) :trans (= n' n))\n"
            "(check-system S :output ((n Int))\n"
            "  :reachable (r1 (= n 1)) :query (q (r1)))\n"
            "(check-system S :output ((n Int))\n"
            "  :reachable (r2 (= n 2)) :query (q (r2)))\n",
            1, "q", 1);
        VERIFY(t.ok());
        VERIFY(has(t.toSmt2(), "2"));
    }

    // ---- A constant array survives being placed at a step. -----------------
    {
        // `((as const (Array T U)) v)` has a sort that cannot be derived from
        // its argument, so rebuilding it while renaming variables aborted inside
        // the frontend and reported E_INTERNAL. The unrolling renames every
        // formula at every step, so any file with a constant array hit it.
        const Translation t = run(
            "(set-logic QF_ABV)\n"
            "(define-system A\n"
            "  :input ((in (_ BitVec 8)))\n"
            "  :output ((out (_ BitVec 8)))\n"
            "  :local ((M (Array (_ BitVec 8) (_ BitVec 8))))\n"
            "  :init (and (= out #b00000000)\n"
            "             (= M ((as const (Array (_ BitVec 8) (_ BitVec 8))) #b00001010)))\n"
            "  :trans (= out' (select M in)))\n"
            "(check-system A\n"
            "  :input ((in (_ BitVec 8)))\n"
            "  :output ((out (_ BitVec 8)))\n"
            "  :local ((M (Array (_ BitVec 8) (_ BitVec 8))))\n"
            "  :reachable (rch (= out #b00001010))\n"
            "  :query (q (rch)))\n");
        if (!t.ok()) {
            std::cout << "  constant array did not survive:\n" << messages(t);
            VERIFY(false);
        }
        const std::string smt = t.toSmt2();
        VERIFY(has(smt, "as const"));
        ParserPtr reader = newParser();
        VERIFY(reader->parseStr(smt));
    }

    std::cout << "All MoXI check-system tests passed." << std::endl;
    return 0;
}
