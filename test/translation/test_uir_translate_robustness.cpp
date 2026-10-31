// translate() must return a failure, never raise one.
//
// include/somtparser/translation/diagnostic.h states the contract: "translating tens of
// thousands of benchmarks means one malformed input must degrade to a recorded
// failure, never an escaped exception that ends the run." It was only half
// true. Step 3 guarded the frontend call; steps 5-8 -- passes, lowering,
// emission -- were bare, and Parser's builders throw ParseErrorException on a
// term they cannot build. One bad benchmark therefore ended the batch, and
// through the Python bindings it killed the interpreter.
//
// This file also pins the two other whole-pipeline properties that had no test:
// that a translation done with OmtDialect::None can still be re-emitted in a
// real dialect, and that a pass rejecting its own parameters is reported as the
// configuration error it is.

#include "somtparser/translation/translate.h"
#include "somtparser/frontend/parser.h"
#include "somtparser/lowering/bound_ints_pass.h"

#include <cassert>
#include <iostream>
#include <limits>
#include <memory>
#include <new>
#include <stdexcept>
#include <string>
#include <vector>

using namespace SOMTParser;
using namespace SOMTParser::Uir;

namespace {

/** Minimal well-formed language: one Int variable, one constraint, one
 *  objective. Everything below varies the pipeline around it, not the input. */
class ToyLang : public Lang::Language {
public:
    std::string id() const override { return "robust-toy"; }
    std::string displayName() const override { return "RobustToy"; }
    std::string version() const override { return "0.1"; }
    std::vector<std::string> extensions() const override { return {".rtoy"}; }
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

/** Two declarations of the same name. The frontend contract does not oblige a
 *  frontend to type-check, so this is an ordinary thing for one to hand over,
 *  and it must come back as E_TYPE rather than as one declare-fun and a
 *  num_vars of 2. */
class DuplicateDeclLang : public ToyLang {
public:
    std::string id() const override { return "dup-toy"; }
    std::vector<std::string> extensions() const override { return {".dtoy"}; }

    Lang::ParseOutcome parse(const Lang::SourceUnit& u,
                             const Lang::ParseOptions& o) override {
        Lang::ParseOutcome out = ToyLang::parse(u, o);
        out.model->decls.push_back(out.model->decls.front());
        return out;
    }
};

class AllocationFailureLang : public ToyLang {
public:
    std::string id() const override { return "allocation-failure-toy"; }
    Lang::ParseOutcome parse(const Lang::SourceUnit&,
                            const Lang::ParseOptions&) override {
        throw std::bad_alloc();
    }
};

/** Declares that it reads the encoding style, which is what makes the warning in
 *  translate() retire. Nothing in the shipping build sets this yet; cluster A's
 *  decomposition pass will, and this stands in for it so the retiring half of
 *  the check is tested rather than assumed. */
class StyleAwarePass : public Pass {
public:
    std::string id() const override { return "style-aware"; }
    PassTraits  traits() const override {
        PassTraits t;
        t.reads_encoding_style = true;
        return t;
    }
    bool run(Hir::ConstraintModel&, LowerContext&) override { return true; }
};

/** Stands in for a defective pass. Registered under the builtin's own id, so
 *  that the "bv32" profile -- which is a real, built-in profile naming
 *  "bound-ints" -- runs it. registerBuiltinPasses() only installs the real one
 *  when the id is free, so registering first is enough to take its place. */
class ThrowingPass : public Pass {
public:
    std::string id() const override { return "bound-ints"; }
    PassTraits  traits() const override { return {}; }
    bool run(Hir::ConstraintModel&, LowerContext&) override {
        throw std::runtime_error("deliberate pass failure");
    }
};

class AllocationFailurePass : public ThrowingPass {
public:
    bool run(Hir::ConstraintModel&, LowerContext&) override {
        throw std::bad_alloc();
    }
};

/** A floor that demands nothing, so these tests fail on the thing they are
 *  testing rather than on E_FIDELITY_REJECTED: bound-ints deliberately records
 *  an under-approximation, and a default-constructed Fidelity is the *top* of
 *  the lattice, which no bounded translation can meet. */
Fidelity permissiveFloor() {
    Fidelity f;
    f.sound = false;
    f.complete = false;
    f.preserves_optimum = false;
    // Count has its own state. An UNASSESSED floor imposes no count requirement;
    // the built-in profiles likewise do not require count preservation.
    return f;
}

Lang::SourceUnit unitFor(const char* path) {
    Lang::SourceUnit u;
    u.main_path = path;
    u.display_name = path;
    u.inline_source = "ignored; the toy frontend does not read it";
    return u;
}

bool mentions(const Diagnostics& d, const std::string& needle) {
    for (const auto& e : d.all()) {
        if (e.message.find(needle) != std::string::npos) { return true; }
    }
    return false;
}

} // namespace

int main() {
    std::cout << "======= translate() robustness =======\n";

    auto& langs = Lang::LanguageRegistry::instance();
    langs.add(std::make_shared<ToyLang>());
    langs.add(std::make_shared<DuplicateDeclLang>());
    langs.add(std::make_shared<AllocationFailureLang>());

    // Inject allocation failures without relying on host memory pressure.
    {
        TranslateOptions opts;
        opts.language_id = "allocation-failure-toy";
        const Translation t = translate(unitFor("a.rtoy"), opts);
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_RESOURCE);
        assert(mentions(t.diagnostics(), "frontend parsing"));
    }

    // ---- The baseline translates, so every failure below is about the thing
    // it is testing and not about the fixture. -------------------------------
    {
        TranslateOptions opts;
        opts.language_id = "robust-toy";
        const Translation t = translate(unitFor("a.rtoy"), opts);
        assert(t.ok());
        assert(t.report().stats().num_vars == 1);
        assert(t.report().stats().num_objectives == 1);
    }

    // ---- A model that is not well-sorted is a recorded E_TYPE, not a crash
    // and not a translated script. -------------------------------------------
    {
        TranslateOptions opts;
        opts.language_id = "dup-toy";
        const Translation t = translate(unitFor("a.dtoy"), opts);
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_TYPE);
        assert(mentions(t.diagnostics(), "declared more than once"));
        // num_vars used to count decls, so this model reported two variables
        // while emitting one declare-fun. It never reaches lowering now, but
        // the statistic is what the experiment tabulates, so pin it where it
        // can be reached: see the well-formed case above, which declares one.
    }

    // ---- Dropping an objective needs a feasibility-only fidelity floor. -----
    // Step 7 proves objective emission works so that toSmt2() may assert
    // instead of silently dropping objectives. It used to run that proof
    // through emitObjectives() with the caller's dialect -- and OmtDialect::None
    // returns "" before looking at anything, so exactly the configuration that
    // emitted no objectives was also the one that checked none. toSmt2(Z3) on
    // such a Translation then tripped the assert the proof exists to justify.
    {
        TranslateOptions exact;
        exact.language_id = "robust-toy";
        exact.omt_dialect = Lower::OmtDialect::None;
        const Translation rejected = translate(unitFor("a.rtoy"), exact);
        assert(!rejected.ok());
        assert(rejected.diagnostics().firstErrorCode()
               == ErrorCode::E_FIDELITY_REJECTED);

        TranslateOptions opts;
        opts.language_id = "robust-toy";
        opts.omt_dialect = Lower::OmtDialect::None;
        opts.profile_id = "feasibility";
        const Translation t = translate(unitFor("a.rtoy"), opts);
        assert(t.ok());
        assert(t.report().fidelity().sound);
        assert(t.report().fidelity().complete);
        assert(!t.report().fidelity().preserves_optimum);
        assert(t.report().provenance().target_dialect == "none");

        const std::string none = t.toSmt2();
        assert(none.find("minimize") == std::string::npos);

        const std::string z3 = t.toSmt2(Lower::OmtDialect::Z3);
        assert(z3.find("(minimize x)") != std::string::npos);
        // ...and before (check-sat), or no solver would read it.
        assert(z3.find("(minimize x)") < z3.find("(check-sat)"));
    }

    // ---- A declared encoding style that nothing consumes is said out loud. --
    // `ground` and `quantified` are the experiment's size-versus-solvability
    // axis, and both have empty pipelines today because the pass that would
    // face the question is cluster A's, which does not exist. Two profiles that
    // produce byte-identical output while claiming different encodings is the
    // failure class this project keeps meeting, so the claim is checked rather
    // than trusted.
    {
        // **The warning has retired.** decompose-globals sets
        // reads_encoding_style, so these two profiles no longer claim something
        // nothing acts on. This assertion is the retirement observed end to end
        // rather than inferred: it was the opposite assertion until the pass
        // landed, and flipping it is the intended lifecycle.
        for (const char* id : {"ground", "quantified"}) {
            TranslateOptions opts;
            opts.language_id = "robust-toy";
            opts.profile_id = id;
            const Translation t = translate(unitFor("a.rtoy"), opts);
            assert(t.ok());
            assert(!t.diagnostics().hasErrors());
            assert(!mentions(t.diagnostics(), "has no effect in this build"));
        }
        // A profile that takes no position says nothing, so ordinary runs stay
        // quiet -- a warning on every translation would be noise nobody reads.
        TranslateOptions opts;
        opts.language_id = "robust-toy";
        opts.profile_id = "default";
        const Translation t = translate(unitFor("a.rtoy"), opts);
        assert(t.ok());
        assert(!mentions(t.diagnostics(), "has no effect in this build"));
    }
    {
        // ...and the warning retires on its own. A pipeline containing a pass
        // that declares it reads the style is silent, which is what makes this
        // a temporary scaffold rather than a permanent apology.
        PassRegistry::instance().add(std::make_shared<StyleAwarePass>());
        auto profile = EncodingProfile::make(
            "test-style-consumed", {PassSpec{"style-aware", {}}},
            permissiveFloor(), EncodingStyle::QUANTIFIED);

        auto model = std::make_shared<Hir::ConstraintModel>();
        TranslationReport report;
        Diagnostics diags;
        assert(PassManager::run(*model, *profile, PassRegistry::instance(),
                                report, diags));
        // Both branches of the predicate, driven directly. An earlier version of
        // this block asserted only that the declaration was *visible*, which no
        // breakage of the retiring logic could fail -- a check that cannot fail,
        // found by a probe that broke the retirement and watched the test pass.
        assert(encodingStyleIsConsumed(*profile, PassRegistry::instance()));

        // The same style with a pipeline that does NOT read it: not consumed.
        auto inert = EncodingProfile::make(
            "test-style-inert", {PassSpec{"bound-ints", {}}},
            permissiveFloor(), EncodingStyle::QUANTIFIED);
        assert(!encodingStyleIsConsumed(*inert, PassRegistry::instance()));

        // An empty pipeline claiming a style is the shipping ground/quantified
        // case, and is not consumed.
        auto empty = EncodingProfile::make(
            "test-style-empty", {}, permissiveFloor(), EncodingStyle::GROUND);
        assert(!encodingStyleIsConsumed(*empty, PassRegistry::instance()));

        // A profile claiming nothing is vacuously consumed, so ordinary runs
        // stay quiet.
        auto none = EncodingProfile::make("test-style-none", {}, permissiveFloor());
        assert(encodingStyleIsConsumed(*none, PassRegistry::instance()));
    }

    // ---- An out-of-range pass parameter is a configuration error. -----------
    // `1LL << (w - 1)` is undefined behaviour outside 1..64, and the results
    // looked plausible rather than broken: width 65 pinned every integer to
    // [-1, 0] while recording "65" as the Bound, so the experiment data would
    // have claimed a 65-bit under-approximation of a two-valued domain.
    {
        auto profile = EncodingProfile::make(
            "test-bad-width", {PassSpec{"bound-ints", {{"width", "65"}}}}, permissiveFloor());
        Lower::registerBuiltinPasses(PassRegistry::instance());

        auto model = std::make_shared<Hir::ConstraintModel>();
        Hir::VarDecl d;
        d.name = "x";
        d.sort = Hir::Sort::integer();
        model->decls.push_back(d);

        TranslationReport report;
        Diagnostics diags;
        assert(!PassManager::run(*model, *profile, PassRegistry::instance(),
                                 report, diags));
        assert(diags.firstErrorCode() == ErrorCode::E_PASS_PIPELINE);
        assert(mentions(diags, "out of range"));
        // The variable is left alone: a pass that refuses must not half-apply.
        assert(!model->decls.front().lower_bound);
    }
    {
        // 64 is in range and must still be computed without overflowing.
        auto profile = EncodingProfile::make(
            "test-w64", {PassSpec{"bound-ints", {{"width", "64"}}}}, permissiveFloor());
        auto model = std::make_shared<Hir::ConstraintModel>();
        Hir::VarDecl d;
        d.name = "x";
        d.sort = Hir::Sort::integer();
        model->decls.push_back(d);

        TranslationReport report;
        Diagnostics diags;
        assert(PassManager::run(*model, *profile, PassRegistry::instance(),
                                report, diags));
        assert(model->decls.front().lower_bound->int_value
               == std::numeric_limits<long long>::min());
        assert(model->decls.front().upper_bound->int_value
               == std::numeric_limits<long long>::max());
    }

    // ---- An exception from anywhere in the pipeline is recorded, not raised.
    // Registered last, because it replaces the real bound-ints for the rest of
    // this process.
    {
        PassRegistry::instance().add(std::make_shared<ThrowingPass>());

        auto profile = EncodingProfile::make(
            "test-throwing", {PassSpec{"bound-ints", {}}}, permissiveFloor());
        auto model = std::make_shared<Hir::ConstraintModel>();
        TranslationReport report;
        Diagnostics diags;

        bool escaped = false;
        try {
            assert(!PassManager::run(*model, *profile, PassRegistry::instance(),
                                     report, diags));
        } catch (...) {
            escaped = true;
        }
        // PassManager itself does not catch; translate() is the boundary, and
        // that is what the next block checks.
        assert(escaped);
    }
    {
        TranslateOptions opts;
        opts.language_id = "robust-toy";
        opts.profile_id = "bv32";        // a built-in profile naming bound-ints

        bool escaped = false;
        Translation t;
        try {
            t = translate(unitFor("a.rtoy"), opts);
        } catch (...) {
            escaped = true;
        }
        assert(!escaped);
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_INTERNAL);
        assert(mentions(t.diagnostics(), "deliberate pass failure"));
    }

    {
        PassRegistry::instance().add(std::make_shared<AllocationFailurePass>());
        TranslateOptions opts;
        opts.language_id = "robust-toy";
        opts.profile_id = "bv32";
        const Translation t = translate(unitFor("a.rtoy"), opts);
        assert(!t.ok());
        assert(t.diagnostics().firstErrorCode() == ErrorCode::E_RESOURCE);
        assert(mentions(t.diagnostics(), "HIR passes"));
        assert(mentions(t.diagnostics(), "bound-ints"));
    }

    std::cout << "All translate() robustness tests passed." << std::endl;
    return 0;
}
