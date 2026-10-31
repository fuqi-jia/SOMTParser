// The MoXI frontend.
//
// MoXI is the reverse of VMT-LIB: it keeps SMT-LIB's TERM language and replaces
// its commands. So the term parsing is reused and the command grammar is read
// by the frontend, and the obligations are about the commands.
//
// Published MoXI check conditions are named. A query is an existence-of-trace
// question selecting assumptions, initiality conditions and reachability
// eventualities by those names. In particular there is no check-system
// `:invariant`; a safety violation is written as a reachable `(not P)` formula.

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

Translation runFile(const std::string& path, int depth) {
    Lang::SourceUnit u;
    u.main_path = path;
    u.display_name = path;
    TranslateOptions opts;
    opts.language_id = "moxi";
    opts.profile_id = "bmc";
    opts.parse.options["bmc_depth"] = std::to_string(depth);
    return translate(u, opts);
}

Translation run(const std::string& src, int depth) {
    Lang::SourceUnit u;
    u.main_path = "t.moxi";
    u.display_name = "t.moxi";
    u.inline_source = src;
    TranslateOptions opts;
    opts.language_id = "moxi";
    opts.profile_id = "bmc";
    opts.parse.options["bmc_depth"] = std::to_string(depth);
    return translate(u, opts);
}

} // namespace

int main() {
    std::cout << "======= MoXI frontend =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    Lang::Language* m = Lang::LanguageRegistry::instance().byId("moxi");
    assert(m != nullptr);

    // ---- The system's shape survives. --------------------------------------
    {
        const Translation t = runFile("languages/moxi/instances/ok/counter.moxi", 2);
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // n-satisfaction at depth 2 may read primed variables at step 2, so the
        // declarations cover states 0 through 3.
        assert(has(smt, "n@0") && has(smt, "n@2") && has(smt, "n@3"));
        assert(has(smt, "tick@0") && has(smt, "tick@3"));
        // `n'` is the next-step copy, not a variable of its own.
        assert(!has(smt, "n'"));
        assert(!has(smt, "moxi.next"));
        // :init at step 0 only; :trans is part of `always TS`, including step 2.
        assert(has(smt, "(= 0 n@0)"));
        assert(has(smt, "n@1 (ite tick@0"));
        assert(has(smt, "n@3 (ite tick@2"));
        // :inv holds at every step.
        assert(has(smt, "(>= n@0 0)") && has(smt, "(>= n@2 0)"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }

    // ---- Safety violations are explicit reachable formulas. ----------------
    {
        // The source asks to reach `(not (< n 10))`; the frontend preserves
        // that formula and does not invent a separate property polarity.
        const Translation t = runFile("languages/moxi/instances/ok/counter.moxi", 2);
        const std::string smt = t.toSmt2();
        assert(has(smt, ">= n@0 10") || has(smt, "(not (< n@0 10))"));
    }
    {
        // A reachable formula is asserted positively.
        const Translation t = runFile("languages/moxi/instances/ok/reachable.moxi", 2);
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "(= 2 n@2)") || has(smt, "(= n@2 2)"));
        assert(!has(smt, "(not (= 2 n@2))") && !has(smt, "distinct 2 n@2"));
    }

    // ---- The bound is on the record, in the right direction. --------------
    {
        const Translation t = runFile("languages/moxi/instances/ok/counter.moxi", 3);
        const EncodingChoice* c = nullptr;
        for (const EncodingChoice& e : t.report().choices()) {
            if (e.unified_op == "transition-system") { c = &e; }
        }
        assert(c != nullptr);
        assert(c->fidelity.sound && !c->fidelity.complete);
        assert(c->fidelity.bounds[0].kind == Fidelity::Bound::BMC_DEPTH);
        assert(c->fidelity.bounds[0].value == 3);
        assert(has(c->rationale, ":reachable") && has(c->rationale, ":current"));
        assert(has(c->rationale, "state n+1"));
    }

    // ---- Subsystem flattening. ---------------------------------------------
    {
        const Translation t = runFile("languages/moxi/instances/ok/subsys.moxi", 2);
        assert(t.ok());
        ParserPtr reader = newParser();
        assert(reader->parseStr(t.toSmt2()));
    }
    {
        const Translation t = runFile("languages/moxi/instances/ok/two_instances.moxi", 1);
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // The two Cell instances have independent copies of local `s`.
        assert(has(smt, "A.s@0") && has(smt, "B.s@0"));
    }

    // ---- The global signature is rigid and available in every system. -----
    {
        const Translation t = runFile(
            "languages/moxi/instances/upstream/QF_BV_QuotedSymbols.moxi", 2);
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "INPUT"));
        // INPUT is a rigid source constant, not an unconstrained input copied
        // once per time position.
        assert(!has(smt, "INPUT@"));
        assert(has(smt, "$out@0") && !has(smt, ".moxi.next"));
    }
    {
        // Both published prime spellings, |name|' and |name'|, denote the same
        // next-state variable and therefore produce the same transition.
        const Translation outside = runFile(
            "languages/moxi/instances/upstream/QF_BV_QuotedSymbols.moxi", 2);
        const Translation inside = runFile(
            "languages/moxi/instances/upstream/QF_BV_QuotedSymbols2.moxi", 2);
        assert(outside.ok() && inside.ok());
        assert(outside.toSmt2() == inside.toSmt2());
    }
    {
        const Translation t = runFile(
            "languages/moxi/instances/upstream/StateProgression.moxi", 2);
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "declare-datatypes") && has(smt, "Start")
               && has(smt, "Active") && has(smt, "Done"));
    }
    {
        // This official file exercises an enum, a define-fun macro and bare
        // numerals in Real ite branches.
        const Translation t = runFile(
            "languages/moxi/instances/upstream/QF_LRA_TimedSwitch3.moxi", 2);
        assert(t.ok());
        assert(has(t.toSmt2(), "n@0 () Real"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(t.toSmt2()));
    }
    {
        // A PARAMETRIC datatype as an interface sort: the upstream
        // LossyIntChannelX shape made spec-well-formed (constructor list
        // parenthesized, one system, one query, `(as Absent (Event Real))`
        // for the constructor that mentions no parameter).
        const Translation t = runFile(
            "languages/moxi/instances/ok/datatype_channel.moxi", 2);
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "declare-datatypes") && has(smt, "(par (X)"));
        assert(has(smt, "Absent") && has(smt, "Present"));
        assert(has(smt, "(as Absent (Event Real))"));
        assert(has(smt, "(val out@2)"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // Query-free libraries are validated before reporting a missing query.
        // This upstream file has malformed parametric datatype syntax, so its
        // parse error must not be hidden by the absence of check-system.
        const Translation t = runFile(
            "languages/moxi/instances/upstream/QF_LRA_LossyIntChannelX.moxi", 2);
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
    }
    {
        // The upstream datatype spelling omits the constructor list's own
        // parens, which the SMT-LIB grammar requires (z3 rejects it too).
        // A file that DOES ask something therefore fails in the environment,
        // with E_PARSE rather than an internal error.
        const Translation t = run(
            "(set-logic QF_LRA)\n"
            "(declare-datatype Event (par (X) (Absent) (Present (val X))))\n"
            "(define-system c\n"
            "  :output ((o (Event Real)))\n"
            "  :inv true)\n"
            "(check-system c\n"
            "  :output ((o (Event Real)))\n"
            "  :reachable (r true)\n"
            "  :query (q (r)))\n", 1);
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
    }

    // ---- Refusals. ---------------------------------------------------------
    {
        const Translation t = run(
            "(define-system s :output ((n Int)))\n"
            "(check-system s :output ((n Int)) :invariant (< n 2) "
            ":query (q (:invariant)))\n", 1);
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "not a check-system condition"));
    }
    {
        // A system with no check-system asks nothing, and an unrolling with no
        // property is trivially satisfiable.
        const Translation t = run("(define-system s :output ((n Int)) :init (= n 0))\n", 1);
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "trivially satisfiable"));
    }
    {
        const Translation t = run(
            "(define-system s :output ((n Int)) :init (= n 0) :trans (= n' n))\n"
            "(check-system s :output ((n Int)) :fairness (f (= n 0)) "
            ":query (q (f)))\n", 1);
        assert(t.ok());
        bool lasso = false;
        for (const auto& choice : t.report().choices()) {
            if (choice.strategy == "bmc-fair-lasso") {
                lasso = true;
                assert(choice.fidelity.sound && !choice.fidelity.complete);
                assert(has(choice.rationale, "nonperiodic"));
            }
        }
        assert(lasso);
    }
    {
        const Translation t = run(
            "(set-info :source \"not a MoXI command\")\n"
            "(define-system s :output ((n Int)))\n"
            "(check-system s :output ((n Int)) :query (q ()))\n", 1);
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "not in the MoXI grammar"));
    }
    {
        Lang::SourceUnit u;
        u.main_path = "languages/moxi/instances/ok/counter.moxi";
        u.display_name = u.main_path;
        TranslateOptions opts;
        opts.language_id = "moxi";
        opts.profile_id = "bmc";
        const Translation t = translate(u, opts);
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "no default"));
    }
    {
        const Translation t = runFile("languages/moxi/instances/nosuch.moxi", 2);
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_IO);
    }

    // ---- Detection and coverage. -------------------------------------------
    {
        assert(m->sniff("(define-system counter :output ((n Int)))") > 0.5);
        assert(m->sniff("(declare-fun x () Int)") == 0.0);
        const Lang::OpCoverage& cov = m->coverage();
        assert(cov.supported < cov.total);
        assert(cov.missing.size() == cov.total - cov.supported);
    }

    std::cout << "All MoXI tests passed." << std::endl;
    return 0;
}
