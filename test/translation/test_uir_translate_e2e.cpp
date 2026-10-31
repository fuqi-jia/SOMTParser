// End to end: a registered language, a profile, a dialect, and a report.
#include "somtparser/translation/translate.h"
#include "somtparser/frontend/parser.h"
#include "translation/bound_semantics.h"
#include <cassert>
#include <iostream>
#include <memory>
#include <string>

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

/** A one-line stand-in language so the facade can be tested without depending
 *  on a real frontend. Accepts ".toy" and always yields (declare x Int) and
 *  (assert (> x 0)) plus a minimize objective. */
class ToyLang : public Lang::Language {
public:
    std::string id() const override { return "toy"; }
    std::string displayName() const override { return "Toy"; }
    std::string version() const override { return "0.1"; }
    std::vector<std::string> extensions() const override { return {".toy"}; }
    const Lang::OpCoverage& coverage() const override { return coverage_; }

    Lang::ParseOutcome parse(const Lang::SourceUnit& u,
                             const Lang::ParseOptions&) override {
        Lang::ParseOutcome out;
        if (u.inline_source == "BOOM") {
            out.diagnostics.error(ErrorCode::E_PARSE, "toy: deliberate failure");
            return out;
        }
        auto m = std::make_shared<Hir::ConstraintModel>();
        Hir::VarDecl d;
        d.name = "x";
        d.sort = Hir::Sort::integer();
        m->decls.push_back(d);
        Hir::Constraint c;
        c.formula = Hir::mkOp(Hir::Op::GT,
                              {Hir::mkIdent("x", Hir::Sort::integer()), Hir::mkInt(0)});
        m->constraints.push_back(c);
        Hir::Objective o;
        o.kind = Hir::ObjKind::MINIMIZE;
        o.term = Hir::mkIdent("x", Hir::Sort::integer());
        o.name = "goal";
        m->objectives.push_back(o);
        out.model = m;
        return out;
    }

private:
    Lang::OpCoverage coverage_;
};

/** Yields a model that translates cleanly but whose SMT-LIB rendering cannot be
 *  read back: the variable name is not a legal SMT-LIB symbol. That is the only
 *  way to reach Parser::parseAny's re-parse failure branch, and it is not a
 *  contrived hazard -- several planned frontends (LP/MPS-style formats) allow
 *  identifier characters SMT-LIB does not. */
class BadNameLang : public Lang::Language {
public:
    std::string id() const override { return "toy-badname"; }
    std::string displayName() const override { return "ToyBadName"; }
    std::string version() const override { return "0.1"; }
    std::vector<std::string> extensions() const override { return {".toybad"}; }
    const Lang::OpCoverage& coverage() const override { return coverage_; }

    Lang::ParseOutcome parse(const Lang::SourceUnit&,
                             const Lang::ParseOptions&) override {
        Lang::ParseOutcome out;
        auto m = std::make_shared<Hir::ConstraintModel>();
        Hir::VarDecl d;
        // A name with a `|` in it. SMT-LIB 2.6 §3.1 gives a quoted symbol NO
        // escape -- `|` and `\\` are the two characters it may not contain --
        // so this one has no legal spelling in either form and the round trip
        // fails however carefully the printer chooses.
        //
        // It used to be `(`, which dumped as `(declare-fun ( () Int)`. That
        // stopped failing on 2026-08-17, when the printer learned to quote a
        // symbol that is not a valid simple one: `|(|` re-parses. The example
        // was scaffolding for a defect, and the defect was fixed -- so this is
        // the same decay D19 describes, and the replacement is chosen to be
        // unspellable BY THE STANDARD rather than merely unhandled.
        d.name = "a|b";
        d.sort = Hir::Sort::integer();
        d.lower_bound = Hir::mkInt(1);
        m->decls.push_back(d);
        out.model = m;
        return out;
    }

private:
    Lang::OpCoverage coverage_;
};

/** Emits one soft constraint, which is what the design spec routes every
 *  OPB / WBO / WCNF weight through. Nothing in the library lowers a soft
 *  constraint yet, so this is the shape of every such instance's failure. */
class SoftToyLang : public Lang::Language {
public:
    std::string id() const override { return "toy-soft"; }
    std::string displayName() const override { return "ToySoft"; }
    std::string version() const override { return "0.1"; }
    std::vector<std::string> extensions() const override { return {".toysoft"}; }
    const Lang::OpCoverage& coverage() const override { return coverage_; }

    Lang::ParseOutcome parse(const Lang::SourceUnit&,
                             const Lang::ParseOptions&) override {
        Lang::ParseOutcome out;
        auto m = std::make_shared<Hir::ConstraintModel>();
        Hir::VarDecl d;
        d.name = "x";
        d.sort = Hir::Sort::integer();
        m->decls.push_back(d);
        Hir::Constraint c;
        c.formula = Hir::mkOp(Hir::Op::GT,
                              {Hir::mkIdent("x", Hir::Sort::integer()), Hir::mkInt(0)});
        c.soft = true;
        c.weight = 4.0;
        c.group = "prefs";
        m->constraints.push_back(c);
        out.model = m;
        return out;
    }

private:
    Lang::OpCoverage coverage_;
};

/** Identical to ToyLang except that it claims to read data files. Without it
 *  the data-path guard below would only ever be observed rejecting, which
 *  cannot tell "consults acceptsDataFiles()" from "rejects every data path". */
class DataToyLang : public ToyLang {
public:
    std::string id() const override { return "toy-data"; }
    std::vector<std::string> extensions() const override { return {".toydata"}; }
    bool acceptsDataFiles() const override { return true; }
};

bool contains(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

/** Stands in for "bound-ints" and fails deliberately. BoundIntsPass's own
 *  PassTraits are all empty by design (Task 16's spec: it changes a
 *  variable's domain, not the feature vocabulary), so
 *  ConstraintModel::features() is provably invariant across a real,
 *  successful run of it -- the success-path proof below (which checks that
 *  the recorded fingerprint equals the pre-pass value) cannot by itself catch
 *  a regression that moves the fingerprint capture to *after*
 *  PassManager::run(): for this specific pass the "before" and "after" values
 *  are numerically identical. This stub restores the sharper half of the
 *  original proof for exactly that gap: a pass that fails makes
 *  PassManager::run() -- and so translate() -- return before ever reaching a
 *  wrongly-placed capture line, leaving the fingerprint map empty instead of
 *  merely unchanged. Registered under "bound-ints" itself (overwriting the
 *  real pass in PassRegistry::instance(), which PassRegistry::add() allows),
 *  and only after the real pass has already been exercised once below. */
class FailingBoundInts : public Pass {
public:
    std::string id() const override { return "bound-ints"; }
    PassTraits traits() const override { return PassTraits{}; }
    bool run(Hir::ConstraintModel&, LowerContext& ctx) override {
        ctx.diagnostics->error(ErrorCode::E_INTERNAL, "bound-ints: deliberate test failure");
        return false;
    }
};

} // namespace

int main() {
    Lang::LanguageRegistry::instance().add(std::make_shared<ToyLang>());

    // Happy path with explicit language id.
    {
        Lang::SourceUnit u;
        u.main_path = "m.toy";
        u.inline_source = "anything";
        TranslateOptions opts;
        opts.language_id = "toy";
        Translation t = translate(u, opts);
        assert(t.ok());
        assert(!t.diagnostics().hasErrors());
        assert(t.parser() != nullptr);
        assert(t.parser()->getAssertions().size() == 1);

        // Provenance is always filled in; without it a result row is untraceable.
        assert(t.report().provenance().language_id == "toy");
        assert(t.report().provenance().profile_id == "default");
        assert(!t.report().provenance().profile_content_hash.empty());
        assert(!t.report().provenance().somtparser_version.empty());

        // Feature counts are the domain fingerprint. featureCounts() is keyed
        // by feature *type*, not occurrence: ConstraintModel::features()
        // returns a set, so the recorded value is exactly 1 whenever any
        // int-sorted declaration is present (the model above declares one:
        // "x"), never the number of such declarations. std::map::count()
        // only reports key presence (0 or 1) regardless of the mapped value,
        // so it could not tell "recorded as 1" from "recorded as 5, wrongly";
        // .at(...) checks the value actually recorded.
        assert(t.report().featureCounts().at("int-var") == 1);

        // Default dialect is the proposed standard.
        const std::string s = t.toSmt2();
        assert(contains(s, "(define-objective goal OBJECTIVE_MIN"));
        // The same translation re-emits in another dialect without re-running.
        const std::string z = t.toSmt2(Lower::OmtDialect::Z3);
        assert(contains(z, "(minimize "));
        assert(!contains(z, "define-objective"));
    }

    // The feature fingerprint must be captured before PassManager::run(), not
    // after. "bv32" now names a real, registered pass ("bound-ints") that
    // succeeds and genuinely mutates the model, which is a stronger proof of
    // the ordering than making that pass fail deliberately: a failing pass
    // only shows the fingerprint capture "didn't get there" before the early
    // return, which says nothing about where the capture line actually sits
    // relative to a pass that runs to completion. Here the pipeline runs
    // start to finish, the model measurably changes (the toy model's one
    // unbounded Int variable, "x", gains bounds and an EncodingChoice), and
    // the recorded fingerprint is still exactly what the untouched,
    // pre-pass model would have reported.
    {
        Lang::SourceUnit u;
        u.main_path = "m.toy";
        u.inline_source = "anything";
        TranslateOptions opts;
        opts.language_id = "toy";
        opts.profile_id = "bv32";
        Translation t = translate(u, opts);
        assert(t.ok());
        assert(!t.diagnostics().hasErrors());

        // The fingerprint: one int-sorted declaration, exactly as many as the
        // toy model declares before any pass touches it. Same reasoning as
        // the happy-path block above: the value, not just the key, must be
        // checked -- .at(...) does that, .count(...) would not.
        assert(t.report().featureCounts().at("int-var") == 1);

        // Proof the pass actually ran and rewrote the model, not merely that
        // translate() reported success: bound-ints recorded exactly one
        // choice, for the toy model's only (unbounded) Int variable.
        assert(t.report().choices().size() == 1);
        assert(t.report().choices()[0].site == "x");
        assert(t.report().choices()[0].strategy == "bound-ints");
        assert(t.report().choices()[0].unified_op == "int-var");

        // ...and the emitted parser carries two extra bound assertions
        // (>= and <=) beyond the toy model's original "x > 0", proof the
        // mutation reached all the way through HirToParser.
        const auto asserts = t.parser()->getAssertions();
        assert(asserts.size() == 3);

        // The count is not the check. A swapped mkGe/mkLe in HirToParser
        // emits x <= -2^31 and x >= 2^31-1, which is UNSAT for every model
        // while leaving this count, the recorded BV_WIDTH 32 Bound and the
        // sound/complete flags above completely unchanged. Assert what the
        // clamp actually says: signed 32-bit is [-2^31, 2^31-1].
        assert(test_bounds::hasVarBound(asserts, "x", test_bounds::Rel::GE,
                                        "-2147483648"));
        assert(test_bounds::hasVarBound(asserts, "x", test_bounds::Rel::LE,
                                        "2147483647"));
        assert(!test_bounds::hasVarBound(asserts, "x", test_bounds::Rel::LE,
                                         "-2147483648"));
        assert(!test_bounds::hasVarBound(asserts, "x", test_bounds::Rel::GE,
                                         "2147483647"));
        // The model's own constraint survived alongside them.
        assert(test_bounds::hasVarBound(asserts, "x", test_bounds::Rel::GT, "0"));

        // The fidelity this earns: sound (a found solution is real) but
        // neither complete nor optimum-preserving (the clamp can exclude a
        // real solution or the true optimum). This is the one place in the
        // whole test suite where a successful, end-to-end translate() call
        // produces sound != complete.
        assert(t.report().fidelity().sound);
        assert(!t.report().fidelity().complete);
        assert(!t.report().fidelity().preserves_optimum);
        assert(t.report().fidelity().bounds.size() == 1);
        assert(t.report().fidelity().bounds[0].value == 32);
        assert(t.report().fidelity().bounds[0].site == "x");
    }

    // The other half of the ordering proof: substitute a pass that fails
    // where "bound-ints" was (see FailingBoundInts above for why the
    // successful-run proof above cannot alone catch a regression that moves
    // the fingerprint capture after PassManager::run()). PassRegistry::add()
    // overwrites by id, and registerBuiltinPasses() only installs the real
    // pass when the id is absent, so this replacement sticks for the rest of
    // the process.
    PassRegistry::instance().add(std::make_shared<FailingBoundInts>());
    {
        Lang::SourceUnit u;
        u.main_path = "m.toy";
        u.inline_source = "anything";
        TranslateOptions opts;
        opts.language_id = "toy";
        opts.profile_id = "bv32";
        Translation t = translate(u, opts);
        assert(!t.ok());
        // If the fingerprint were captured after PassManager::run() instead
        // of before, this map would be empty here (the pass fails, so
        // translate() returns before ever reaching a capture line placed
        // after step 5) and .at(...) would throw instead of returning 1.
        assert(t.report().featureCounts().at("int-var") == 1);
        assert(t.report().choices().empty());
    }

    // "An unregistered pass id is rejected" is exercised directly against
    // PassManager::validate() in test_uir_passmanager.cpp using a private
    // registry; nothing here can reproduce that at the translate() level
    // since translate() always registers every built-in pass (step 0) before
    // it ever queries PassRegistry::instance().

    // Auto-detection by extension.
    {
        Lang::SourceUnit u;
        u.main_path = "m.toy";
        u.inline_source = "anything";
        Translation t = translate(u);
        assert(t.ok());
        assert(t.report().provenance().language_id == "toy");
    }

    // Unknown language id fails loudly instead of falling back.
    {
        Lang::SourceUnit u;
        u.main_path = "m.toy";
        u.inline_source = "x";
        TranslateOptions opts;
        opts.language_id = "nonexistent";
        Translation t = translate(u, opts);
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
    }

    // Unknown profile id likewise.
    {
        Lang::SourceUnit u;
        u.main_path = "m.toy";
        u.inline_source = "x";
        TranslateOptions opts;
        opts.profile_id = "no-such-profile";
        Translation t = translate(u, opts);
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_PASS_PIPELINE);
    }

    // Data files handed to a language that does not read them are refused,
    // not dropped. Silently discarding them would translate the model half
    // alone and report success for a problem it never fully read.
    {
        Lang::SourceUnit u;
        u.main_path = "m.toy";
        u.inline_source = "anything";
        u.data_paths = {"d1.dzn", "d2.dzn"};
        TranslateOptions opts;
        opts.language_id = "toy";
        Translation t = translate(u, opts);
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        // Naming the dropped files is the point: "unsupported" alone would not
        // tell a batch run which input half went unread.
        assert(contains(t.diagnostics().all()[0].message, "d1.dzn"));
        assert(contains(t.diagnostics().all()[0].message, "d2.dzn"));
        assert(contains(t.diagnostics().all()[0].message, "toy"));
        // Nothing was translated, so no parser was produced to mistake for one.
        assert(t.parser() == nullptr);
    }

    // The same unit without data paths still succeeds, so the guard is the
    // data path and not the language.
    {
        Lang::SourceUnit u;
        u.main_path = "m.toy";
        u.inline_source = "anything";
        TranslateOptions opts;
        opts.language_id = "toy";
        Translation t = translate(u, opts);
        assert(t.ok());
    }

    // ...and a language that *does* claim data files gets them through, so the
    // guard consults acceptsDataFiles() rather than rejecting unconditionally.
    {
        Lang::LanguageRegistry::instance().add(std::make_shared<DataToyLang>());
        Lang::SourceUnit u;
        u.main_path = "m.toydata";
        u.inline_source = "anything";
        u.data_paths = {"d1.dzn"};
        TranslateOptions opts;
        opts.language_id = "toy-data";
        Translation t = translate(u, opts);
        assert(t.ok());
        assert(!t.diagnostics().hasErrors());
        assert(t.report().provenance().language_id == "toy-data");
    }

    // Undetectable input reports rather than guesses.
    {
        Lang::SourceUnit u;
        u.main_path = "m.unknownext";
        u.inline_source = "x";
        Translation t = translate(u);
        assert(!t.ok());
        assert(t.diagnostics().hasErrors());
    }

    // A frontend failure propagates as a diagnostic, never as an exception.
    {
        Lang::SourceUnit u;
        u.main_path = "m.toy";
        u.inline_source = "BOOM";
        Translation t = translate(u);
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_PARSE);
    }

    // Parser::parseAny is the same path, landing in an existing Parser.
    {
        ParserPtr p = newParser();
        Lang::SourceUnit u;
        u.main_path = "m.toy";
        u.inline_source = "anything";
        assert(p->parseAny(u));
        assert(p->getAssertions().size() == 1);
        assert(p->lastTranslationReport().provenance().language_id == "toy");
    }

    // The toy model's minimize objective must survive Parser::parseAny, not
    // merely the assertion count. HirToParser deliberately never lowers
    // objectives onto a Parser object -- they exist only as the text
    // toSmt2() renders -- so a round trip through plain dumpSMT2()
    // (declarations + assertions only, no objectives) would report success
    // while silently handing back a Parser that solves the wrong,
    // unconstrained problem. Check the destination parser's own recorded
    // objective (kind and term), not just how many assertions arrived.
    {
        ParserPtr p = newParser();
        Lang::SourceUnit u;
        u.main_path = "m.toy";
        u.inline_source = "anything";
        assert(p->parseAny(u));
        auto objs = p->getObjectives();
        assert(objs.size() == 1);
        assert(objs[0]->isMinimize());
        assert(objs[0]->getObjectiveTerm() != nullptr);
        assert(objs[0]->getObjectiveTerm()->getName() == "x");
    }

    // A parseAny round trip that fails must say so in the report, not only in
    // the return value. translate() itself succeeds here -- it is the replay
    // into *this* Parser that fails -- so without a recorded diagnostic
    // lastTranslationReport() would read as a successful, exact-fidelity
    // translation and a caller inspecting it would see no failure at all.
    // (The re-parse prints its own error to stdout; that is expected here.)
    {
        Lang::LanguageRegistry::instance().add(std::make_shared<BadNameLang>());
        Lang::SourceUnit u;
        u.main_path = "m.toybad";
        u.inline_source = "anything";

        // The translation itself is fine: the failure is the round trip.
        TranslateOptions topts;
        topts.language_id = "toy-badname";
        assert(translate(u, topts).ok());

        ParserPtr p = newParser();
        assert(!p->parseAny(u));
        const auto& rep = p->lastTranslationReport();
        bool recorded = false;
        for (const auto& w : rep.warnings()) {
            if (w.severity == Severity::ERROR && w.code == ErrorCode::E_INTERNAL
                && contains(w.message, "parseAny")) {
                recorded = true;
            }
        }
        assert(recorded);
    }

    // The other, far more reachable parseAny failure: the source language
    // itself fails to parse. translate() records the cause in its own
    // Diagnostics, which dies with the Translation -- report() carries none of
    // it -- so without copying it across, a caller inspecting
    // lastTranslationReport() after a failed parse read an exact-fidelity
    // report with no entries: a successful-looking report for an input that
    // never parsed. Assert what was recorded, not merely that parseAny said
    // false; the return value was already correct when this was broken.
    {
        ParserPtr p = newParser();
        Lang::SourceUnit u;
        u.main_path = "m.toy";
        u.inline_source = "BOOM";          // ToyLang: deliberate E_PARSE
        assert(!p->parseAny(u));

        const auto& rep = p->lastTranslationReport();
        bool recorded = false;
        for (const auto& w : rep.warnings()) {
            if (w.severity == Severity::ERROR && w.code == ErrorCode::E_PARSE
                && contains(w.message, "toy: deliberate failure")) {
                recorded = true;
            }
        }
        assert(recorded);
        // ...and the report does not otherwise read as a completed translation.
        assert(rep.provenance().language_id.empty());
    }

    // The same unit, parsed by the same language, still succeeds through
    // parseAny -- so what the block above observes is the parse failure and not
    // parseAny recording an error unconditionally.
    {
        ParserPtr p = newParser();
        Lang::SourceUnit u;
        u.main_path = "m.toy";
        u.inline_source = "anything";
        assert(p->parseAny(u));
        for (const auto& w : p->lastTranslationReport().warnings()) {
            assert(w.severity != Severity::ERROR);
        }
    }

    // The production path for an input construct nothing can lower. A soft
    // A soft constraint used to reach PassManager::validate()'s leftover check
    // with no registered pass able to eliminate it, and was counted as thin
    // construct coverage (E_UNSUPPORTED_CONSTRUCT). That was right while the
    // target could not express one.
    //
    // It can now: Parser::assertSoft and the matching dumpSMT2 emission landed
    // on 2026-08-12, HirToParser lowers soft constraints, and validate() erases
    // feat::softConstraint() the way it erases feat::quantifier(). So this
    // asserts the translation instead of the refusal -- and asserts the
    // property the refusal was protecting, which is that the constraint does
    // NOT arrive as a hard one. Hardening it would change the problem from
    // "violate this at cost w" to "never violate this", which can turn a
    // satisfiable MaxSMT instance UNSAT, and "it translated" alone would pass
    // for a frontend that did exactly that.
    {
        Lang::LanguageRegistry::instance().add(std::make_shared<SoftToyLang>());
        Lang::SourceUnit u;
        u.main_path = "m.toysoft";
        u.inline_source = "anything";
        TranslateOptions opts;
        opts.language_id = "toy-soft";
        Translation t = translate(u, opts);
        assert(t.ok());
        assert(!t.diagnostics().hasErrors());
        const std::string smt = t.toSmt2();
        assert(contains(smt, "assert-soft"));
        // Not hardened: the parser holds no hard assertion for it.
        assert(t.parser()->getAssertions().empty());
    }

    std::cout << "All translate() end-to-end tests passed." << std::endl;
    return 0;
}
