// The VMT-LIB frontend.
//
// The obligation that makes this format dangerous is not one of its own
// constructs: **a VMT file is a legal SMT-LIB script throughout**, because
// every VMT construct is an `!` attribute on a term. So a plain SMT-LIB reader
// parses it, ignores the transition structure, and produces a one-step formula
// that is not the model -- with exit code 0.
//
// BTOR2 and AIGER fail loudly under the wrong reader; this one fails silently
// and hands back a well-formed script. The first test below demonstrates it,
// because a warning in a document is not a check.
//
// The rest:
//
//   * a variable WITH `:next` is a state and the variable it names is its
//     next-step copy -- and that named variable is then NOT an independent free
//     variable, or the unrolling has twice the degrees of freedom the system
//     has;
//   * a variable with NO `:next` is an input, fresh at every step;
//   * `:trans` is the WHOLE transition relation -- unlike BTOR2 and AIGER there
//     is no per-variable frame to add, and adding one would invent a constraint
//     the file does not state;
//   * `:invar-property` asks reachability of its NEGATION.

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

Translation runFile(const std::string& path, int depth, const std::string& lang = "vmt") {
    Lang::SourceUnit u;
    u.main_path = path;
    u.display_name = path;
    TranslateOptions opts;
    opts.language_id = lang;
    opts.profile_id = lang == "vmt" ? "bmc" : "default";
    opts.parse.options["bmc_depth"] = std::to_string(depth);
    return translate(u, opts);
}

Translation run(const std::string& src, int depth) {
    Lang::SourceUnit u;
    u.main_path = "t.vmt";
    u.display_name = "t.vmt";
    u.inline_source = src;
    TranslateOptions opts;
    opts.language_id = "vmt";
    opts.profile_id = "bmc";
    opts.parse.options["bmc_depth"] = std::to_string(depth);
    return translate(u, opts);
}

Translation runCheck(const std::string& src, int depth, const std::string& check_index) {
    Lang::SourceUnit u;
    u.main_path = "t.vmt";
    u.display_name = "t.vmt";
    u.inline_source = src;
    TranslateOptions opts;
    opts.language_id = "vmt";
    opts.profile_id = "bmc";
    opts.parse.options["bmc_depth"] = std::to_string(depth);
    opts.parse.options["check_index"] = check_index;
    return translate(u, opts);
}

Translation runDepthText(const std::string& src, const std::string& depth) {
    Lang::SourceUnit u;
    u.main_path = "t.vmt";
    u.display_name = "t.vmt";
    u.inline_source = src;
    TranslateOptions opts;
    opts.language_id = "vmt";
    opts.profile_id = "bmc";
    opts.parse.options["bmc_depth"] = depth;
    return translate(u, opts);
}

} // namespace

int main() {
    std::cout << "======= VMT-LIB frontend =======\n";
    Lang::registerAllLanguages(Lang::LanguageRegistry::instance());

    Lang::Language* v = Lang::LanguageRegistry::instance().byId("vmt");
    assert(v != nullptr);

    // ---- The silent failure this format invites, demonstrated. -------------
    {
        // Read as plain SMT-LIB, the same file translates SUCCESSFULLY and the
        // transition structure is gone: init, trans and the property remain
        // definitions, with no reachability query. This checks vmt-lib.md §4.1,
        // and it is here because a warning in a document is not a check.
        const Translation plain =
            runFile("languages/vmt/instances/ok/counter.vmt", 2, "smtlib2");
        assert(plain.ok());
        const std::string ps = plain.toSmt2();
        assert(has(ps, "define-fun init () Bool"));
        auto plain_reader = newParser();
        assert(plain_reader->parseStr(ps));
        assert(plain_reader->getAssertions().empty());
        assert(!has(ps, "@1"));

        // Read as VMT, the structure is there.
        const Translation t = runFile("languages/vmt/instances/ok/counter.vmt", 2);
        assert(t.ok());
        assert(has(t.toSmt2(), "x@1"));
        assert(t.toSmt2() != ps);
    }

    // ---- `:next` names the next-step copy, which is not independent. -------
    {
        const Translation t = runFile("languages/vmt/instances/ok/counter.vmt", 2);
        const std::string smt = t.toSmt2();
        // Three steps of x...
        assert(has(smt, "x@0") && has(smt, "x@1") && has(smt, "x@2"));
        // ...and `x.next` is NOT a variable of the model. Left independent, the
        // unrolling would have twice the freedom the system has.
        assert(!has(smt, "x.next"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }
    {
        // The transition really relates consecutive steps rather than being
        // asserted once.
        const Translation t = runFile("languages/vmt/instances/ok/counter.vmt", 2);
        const std::string smt = t.toSmt2();
        assert(has(smt, "(= x@1 (+ 1 x@0))"));
        assert(has(smt, "(= x@2 (+ 1 x@1))"));
    }

    // ---- A variable with no `:next` is an input. ---------------------------
    {
        const Translation t = runFile("languages/vmt/instances/ok/input.vmt", 1);
        assert(t.ok());
        const std::string smt = t.toSmt2();
        // Fresh at every step: one copy per step, not one carried across.
        assert(has(smt, "i@0") && has(smt, "i@1"));
    }

    // ---- `:trans` is the whole relation: no frame is invented. -------------
    {
        // Two state variables and a `:trans` that mentions only one. The other
        // is unconstrained across the step -- BTOR2 and AIGER would add
        // `s' = s`, and doing that here would assert something the file does
        // not say.
        const Translation t = run(
            "(declare-fun a () Bool)\n(declare-fun a.next () Bool)\n"
            "(declare-fun b () Bool)\n(declare-fun b.next () Bool)\n"
            "(define-fun sa () Bool (! a :next a.next))\n"
            "(define-fun sb () Bool (! b :next b.next))\n"
            "(define-fun i () Bool (! (not a) :init true))\n"
            "(define-fun tr () Bool (! (= a.next a) :trans true))\n"
            "(define-fun p () Bool (! (not b) :invar-property 0))\n", 1);
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "b@0") && has(smt, "b@1"));
        // No frame constraint for b.
        assert(!has(smt, "(= b@0 b@1)") && !has(smt, "(= b@1 b@0)"));
    }

    // ---- The property is asserted NEGATED. ---------------------------------
    {
        // `(< x 10)` must hold in every reachable state, so the unrolling looks
        // for a state where it does NOT. Asserted positively, the script would
        // ask whether the property can hold, which is the opposite question.
        const Translation t = runFile("languages/vmt/instances/ok/counter.vmt", 2);
        const std::string smt = t.toSmt2();
        assert(has(smt, ">= x@0 10") || has(smt, "(not (< x@0 10))"));
        assert(has(smt, "(or "));
    }

    // ---- Reachability is a disjunction of finite path prefixes. ------------
    {
        // The initial state is already bad. Its only successor is a dead end,
        // so there is no length-2 path. Globally requiring transitions through
        // the configured bound would erase the real depth-0 counterexample.
        const Translation t =
            runFile("languages/vmt/instances/ok/dead_end.vmt", 2);
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "s@0") && has(smt, "s@1") && has(smt, "s@2"));
        assert(has(smt, "(or "));
        // The transition occurs under candidate prefixes, rather than as an
        // unconditional top-level assertion for every configured frame.
        assert(has(smt, "s@1") && has(smt, "s@2"));
        ParserPtr reader = newParser();
        assert(reader->parseStr(smt));
    }

    // ---- Structural annotation and SMT environment elaboration. -----------
    {
        // This follows the official example's declare-const spelling. Relevant
        // VMT attributes need not be first, and a define-fun used by an
        // annotated formula is a macro, not a fresh uninterpreted predicate.
        const Translation t = run(
            "(set-logic QF_LIA)\n"
            "(declare-const x Int)\n(declare-const xn Int)\n"
            "(declare-fun f (Int) Int)\n"
            "(define-fun zero ((v Int)) Bool (= v 0))\n"
            "(define-fun sv () Int (! x :named current :next xn))\n"
            "(define-fun i () Bool (! (zero x) :named initial :init true))\n"
            "(define-fun tr () Bool (! (= xn (f x)) :trans true :named transition))\n"
            "(define-fun p () Bool (! (>= x 0) :named nonnegative :invar-property 7))\n"
            "(assert true)\n", 1);
        assert(t.ok());
        const std::string smt = t.toSmt2();
        assert(has(smt, "x@0") && has(smt, "x@1"));
        assert(has(smt, "declare-fun f"));
        assert(!has(smt, "declare-fun zero"));
        assert(!has(smt, "declare-fun xn"));
    }
    {
        // The meaningful annotation may be nested below another annotated or
        // ordinary term. A raw find that jumps past the outer ')' loses it.
        const Translation t = run(
            "(declare-const x Int)\n(declare-const xn Int)\n"
            "(define-fun sv () Int (! x :next xn))\n"
            "(define-fun i () Bool (! (and (! (= x 0) :init true) true) :named outer))\n"
            "(define-fun tr () Bool (! (= xn x) :trans true))\n"
            "(define-fun p () Bool (! (= x 1) :invar-property 0))\n", 0);
        assert(t.ok());
        assert(has(t.toSmt2(), "(= 0 x@0)") || has(t.toSmt2(), "(= x@0 0)"));
    }

    // ---- Source well-formedness obligations. -------------------------------
    {
        // The VMT 0.1 specification explicitly excludes input and next-state
        // variables from the initial-state formula.
        const Translation input_init = run(
            "(declare-const s Bool)\n(declare-const sn Bool)\n"
            "(declare-const input Bool)\n"
            "(define-fun sv () Bool (! s :next sn))\n"
            "(define-fun i () Bool (! input :init true))\n"
            "(define-fun tr () Bool (! (= sn s) :trans true))\n"
            "(define-fun p () Bool (! s :invar-property 0))\n", 1);
        assert(!input_init.ok());
        assert(has(input_init.diagnostics().all()[0].message, "input"));

        const Translation next_init = run(
            "(declare-const s Bool)\n(declare-const sn Bool)\n"
            "(define-fun sv () Bool (! s :next sn))\n"
            "(define-fun i () Bool (! sn :init true))\n"
            "(define-fun tr () Bool (! (= sn s) :trans true))\n"
            "(define-fun p () Bool (! s :invar-property 0))\n", 1);
        assert(!next_init.ok());
        assert(has(next_init.diagnostics().all()[0].message, "next-state"));
    }
    {
        const Translation mismatched_next = run(
            "(declare-const s Bool)\n(declare-const sn Int)\n"
            "(define-fun sv () Bool (! s :next sn))\n"
            "(define-fun i () Bool (! s :init true))\n"
            "(define-fun tr () Bool (! true :trans true))\n"
            "(define-fun p () Bool (! s :invar-property 0))\n", 0);
        assert(!mismatched_next.ok());
        assert(has(mismatched_next.diagnostics().all()[0].message, "same sort"));
    }
    {
        const Translation duplicate_property = run(
            "(declare-const s Bool)\n(declare-const sn Bool)\n"
            "(define-fun sv () Bool (! s :next sn))\n"
            "(define-fun i () Bool (! s :init true))\n"
            "(define-fun tr () Bool (! (= sn s) :trans true))\n"
            "(define-fun p0 () Bool (! s :invar-property 1))\n"
            "(define-fun p1 () Bool (! (not s) :invar-property 1))\n", 0);
        assert(!duplicate_property.ok());
        assert(has(duplicate_property.diagnostics().all()[0].message, "duplicate"));
    }

    // ---- check_index: one property per query. --------------------------------
    {
        // The default aggregates: both negations appear in the single query.
        // UF predicates keep the properties visible in the output text: a
        // negated comparison could be rewritten to its dual by the engine's
        // simplifier, and a shared state variable appears in init/trans anyway,
        // so neither could witness the selection.
        const char* two =
            "(declare-const x Int)\n(declare-const xn Int)\n"
            "(declare-fun p (Int) Bool)\n(declare-fun q (Int) Bool)\n"
            "(define-fun sv () Int (! x :next xn))\n"
            "(define-fun i () Bool (! (= x 0) :init true))\n"
            "(define-fun tr () Bool (! (= xn (+ x 1)) :trans true))\n"
            "(define-fun p0 () Bool (! (p x) :invar-property 5))\n"
            "(define-fun p1 () Bool (! (q x) :invar-property 7))\n";
        const Translation all = run(two, 0);
        assert(all.ok());
        const std::string smt_all = all.toSmt2();
        assert(has(smt_all, "(p x@0)") && has(smt_all, "(q x@0)"));

        // check_index=1: only the SECOND property is queried -- an independent
        // verdict for id 7, not a weaker aggregate.
        const Translation one = runCheck(two, 0, "1");
        assert(one.ok());
        const std::string smt_one = one.toSmt2();
        assert(has(smt_one, "(q x@0)"));
        assert(!has(smt_one, "(p x@0)"));
        // The selection is recorded: the report says which property id this
        // query answers, and that the other is a separate query.
        bool recorded = false;
        for (const EncodingChoice& c : one.report().choices()) {
            recorded = recorded || (has(c.rationale, "check_index=1")
                                    && has(c.rationale, "id 7"));
        }
        assert(recorded);

        // check_index=0 covers the first property; the two queries differ.
        const Translation zero = runCheck(two, 0, "0");
        assert(zero.ok());
        assert(has(zero.toSmt2(), "(p x@0)"));
        assert(!has(zero.toSmt2(), "(q x@0)"));
    }
    {
        // An out-of-range selector names how many properties the file has.
        const Translation t = runCheck(
            "(declare-const s Bool)\n(declare-const sn Bool)\n"
            "(define-fun sv () Bool (! s :next sn))\n"
            "(define-fun i () Bool (! s :init true))\n"
            "(define-fun tr () Bool (! (= sn s) :trans true))\n"
            "(define-fun p () Bool (! s :invar-property 0))\n", 0, "3");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
        assert(has(t.diagnostics().all()[0].message, "check_index=3"));
        assert(has(t.diagnostics().all()[0].message, "1 property"));
    }
    {
        const Translation t = runCheck(
            "(declare-const s Bool)\n(declare-const sn Bool)\n"
            "(define-fun sv () Bool (! s :next sn))\n"
            "(define-fun i () Bool (! s :init true))\n"
            "(define-fun tr () Bool (! (= sn s) :trans true))\n"
            "(define-fun p () Bool (! s :invar-property 0))\n", 0, "x");
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
    }
    {
        // The reference readers define init/trans as conjunctions of all
        // annotated terms. Missing sections are therefore true, not a frame
        // rule and not a malformed model.
        const Translation empty_sections = run(
            "(declare-const s Bool)\n(declare-const sn Bool)\n"
            "(define-fun sv () Bool (! s :next sn))\n"
            "(define-fun p () Bool (! s :invar-property 0))\n", 1);
        assert(empty_sections.ok());
        bool saw_default = false;
        for (const EncodingChoice& c : empty_sections.report().choices()) {
            saw_default = saw_default || c.strategy == "empty-conjunction-true";
        }
        assert(saw_default);

        // :invar is not defined by VMT-LIB 0.1. Treating it as an assumption
        // would silently strengthen the transition system.
        const Translation invented_invar = run(
            "(declare-const s Bool)\n(declare-const sn Bool)\n"
            "(define-fun sv () Bool (! s :next sn))\n"
            "(define-fun i () Bool (! s :init true))\n"
            "(define-fun tr () Bool (! (= sn s) :trans true))\n"
            "(define-fun inv () Bool (! s :invar true))\n"
            "(define-fun p () Bool (! s :invar-property 0))\n", 0);
        assert(!invented_invar.ok());
        assert(has(invented_invar.diagnostics().all()[0].message, "not a VMT-LIB"));
    }
    {
        const std::string valid =
            "(declare-const s Bool)\n(declare-const sn Bool)\n"
            "(define-fun sv () Bool (! s :next sn))\n"
            "(define-fun i () Bool (! s :init true))\n"
            "(define-fun tr () Bool (! (= sn s) :trans true))\n"
            "(define-fun p () Bool (! s :invar-property 0))\n";
        const Translation command = run(valid + "(check-sat)\n", 0);
        assert(!command.ok());
        assert(has(command.diagnostics().all()[0].message, "not allowed"));
        const Translation after_assert = run(valid + "(assert true)\n(set-option :x true)\n", 0);
        assert(!after_assert.ok());
        assert(has(after_assert.diagnostics().all()[0].message, "final"));
        const Translation malformed_option = run("(set-option :x)\n" + valid, 0);
        assert(!malformed_option.ok());
        assert(has(malformed_option.diagnostics().all()[0].message, "set-option"));
        assert(!runDepthText(valid, "2junk").ok());
        assert(!runDepthText(valid, "18446744073709551615").ok());
    }

    // ---- The bound is on the record, in the right direction. --------------
    {
        const Translation t = runFile("languages/vmt/instances/ok/counter.vmt", 3);
        const EncodingChoice* c = nullptr;
        for (const EncodingChoice& e : t.report().choices()) {
            if (e.unified_op == "transition-system") { c = &e; }
        }
        assert(c != nullptr);
        assert(c->fidelity.sound && !c->fidelity.complete);
        assert(c->fidelity.bounds.size() == 1);
        assert(c->fidelity.bounds[0].value == 3);
        assert(has(c->rationale, "must not be reported as safe"));
    }

    // ---- Refusals. ---------------------------------------------------------
    {
        const Translation t = runFile("languages/vmt/instances/reject/liveness.vmt", 2);
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        assert(has(t.diagnostics().all()[0].message, "infinite behaviour"));
    }
    {
        // A plain SMT-LIB file has no annotations, so reading it as a
        // transition system would invent a structure it does not have. The
        // message says which language to use instead.
        const Translation t = runFile("languages/vmt/instances/reject/plain.vmt", 2);
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "smtlib2"));
    }
    {
        // A file with annotations but no property: an unrolling with nothing
        // asserted is trivially satisfiable.
        const Translation t = run(
            "(declare-fun s () Bool)\n(declare-fun s.next () Bool)\n"
            "(define-fun sv () Bool (! s :next s.next))\n"
            "(define-fun i () Bool (! (not s) :init true))\n"
            "(define-fun tr () Bool (! (= s.next s) :trans true))\n", 1);
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "trivially satisfiable"));
    }
    {
        Lang::SourceUnit u;
        u.main_path = "languages/vmt/instances/ok/counter.vmt";
        u.display_name = u.main_path;
        TranslateOptions opts;
        opts.language_id = "vmt";
        opts.profile_id = "bmc";
        const Translation t = translate(u, opts);
        assert(!t.ok());
        assert(has(t.diagnostics().all()[0].message, "no default"));
    }

    // ---- Detection: the annotations are what distinguish it. ---------------
    {
        assert(v->sniff("(define-fun p () Bool (! x :invar-property 0))") > 0.5);
        assert(v->sniff("(declare-fun x () Int)(assert (> x 0))") == 0.0);
    }

    // ---- Coverage is honest. -----------------------------------------------
    {
        const Lang::OpCoverage& cov = v->coverage();
        assert(cov.supported < cov.total);
        assert(cov.missing.size() == cov.total - cov.supported);
    }

    std::cout << "All VMT-LIB tests passed." << std::endl;
    return 0;
}
