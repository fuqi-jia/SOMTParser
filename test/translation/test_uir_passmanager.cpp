// The pipeline is validated symbolically before any pass runs. A misordered
// profile must be rejected up front, not discovered by way of a silently wrong
// SMT file buried in ten thousand benchmarks.
#include "somtparser/translation/pass.h"
#include <cassert>
#include <iostream>
#include <stdexcept>
#include <string>

using namespace SOMTParser::Uir;
using namespace SOMTParser::Uir::Hir;

namespace {

/** Eliminates int variables, standing in for the real int-to-bv pass. */
class IntToBvStub : public Pass {
public:
    std::string id() const override { return "int-to-bv"; }
    PassTraits traits() const override {
        PassTraits t;
        t.eliminates = {feat::intVar()};
        return t;
    }
    bool run(ConstraintModel& m, LowerContext& ctx) override {
        for (auto& d : m.decls) {
            if (d.sort.kind == SortKind::INT) {
                d.sort = Sort::boolean();     // stand-in for a real BV sort
            }
        }
        EncodingChoice c;
        c.site = "model";
        c.unified_op = "int-var";
        c.strategy = "int-as-bv";
        c.fidelity = Fidelity::underApprox(
            {Fidelity::Bound::BV_WIDTH, ctx.spec->intParam("width", 32), "model"});
        ctx.report->addChoice(c);
        ++ran;
        return true;
    }
    static int ran;
};
int IntToBvStub::ran = 0;

/** Requires int variables to be gone already: the dependency the static
 *  check exists to catch. */
class BitmaskStub : public Pass {
public:
    std::string id() const override { return "alldiff-bitmask"; }
    PassTraits traits() const override {
        PassTraits t;
        t.requires_absent = {feat::intVar()};
        t.eliminates = {feat::globalConstraint()};
        return t;
    }
    bool run(ConstraintModel&, LowerContext&) override { ++ran; return true; }
    static int ran;
};
int BitmaskStub::ran = 0;

/** Introduces a feature it never eliminates, and has no requires_absent of its
 *  own. Exists to exercise the terminal leftover-feature check in isolation:
 *  neither the unknown-pass check nor the requires_absent check can explain a
 *  rejection of a pipeline built from this pass and int-to-bv, so only the
 *  terminal "nothing high-level survives the pipeline" check can. */
class ReifyStub : public Pass {
public:
    std::string id() const override { return "reify-stub"; }
    PassTraits traits() const override {
        PassTraits t;
        t.introduces = {feat::reification()};
        return t;
    }
    bool run(ConstraintModel&, LowerContext&) override { ++ran; return true; }
    static int ran;
};
int ReifyStub::ran = 0;

/** Eliminates soft constraints. Nothing in the real library does yet, which is
 *  the whole point: registering this one and not registering it is the only
 *  difference between "no encoding exists for this input construct" and "this
 *  profile just does not run the pass that would". */
class SoftToHardStub : public Pass {
public:
    std::string id() const override { return "soft-to-hard"; }
    PassTraits traits() const override {
        PassTraits t;
        t.eliminates = {feat::softConstraint()};
        return t;
    }
    bool run(ConstraintModel& m, LowerContext&) override {
        // Actually remove the feature, so the stub's traits are not a lie.
        for (auto& c : m.constraints) {
            c.soft = false;
        }
        ++ran;
        return true;
    }
    static int ran;
};
int SoftToHardStub::ran = 0;

bool mentions(const std::string& hay, const std::string& needle) {
    return hay.find(needle) != std::string::npos;
}

ConstraintModel intModel() {
    ConstraintModel m;
    VarDecl d;
    d.name = "x";
    d.sort = Sort::integer();
    m.decls.push_back(d);
    Constraint c;
    c.formula = mkOp(Op::GT, {mkIdent("x", Sort::integer()), mkInt(0)});
    m.constraints.push_back(c);
    return m;
}

} // namespace

int main() {
    PassRegistry reg;
    reg.add(std::make_shared<IntToBvStub>());
    reg.add(std::make_shared<BitmaskStub>());
    reg.add(std::make_shared<ReifyStub>());
    assert(reg.get("int-to-bv") != nullptr);
    assert(reg.get("nope") == nullptr);
    assert(reg.ids().size() == 3);

    // Registering a null pass is a caller bug, never an input condition.
    // Dropping it silently left every profile naming that pass rejecting with
    // E_PASS_PIPELINE as if it had never been written -- the failure would be
    // blamed on the profile, miles from the registration that caused it.
    {
        bool threw = false;
        try {
            reg.add(nullptr);
        } catch (const std::runtime_error&) {
            threw = true;
        }
        assert(threw);
        assert(reg.ids().size() == 3);   // and nothing was recorded
    }

    // Wrong order: bitmask before int-to-bv, while the model still has int vars.
    {
        const auto bad = EncodingProfile::make(
            "bad", {PassSpec{"alldiff-bitmask", {}}, PassSpec{"int-to-bv", {}}},
            Fidelity::exact());
        ConstraintModel m = intModel();
        Diagnostics d;
        assert(!PassManager::validate(m, *bad, reg, d));
        assert(d.hasErrors());
        assert(d.firstErrorCode() == ErrorCode::E_PASS_PIPELINE);

        // Nothing ran: validation happens before execution, not during it.
        IntToBvStub::ran = 0;
        BitmaskStub::ran = 0;
        TranslationReport r;
        Diagnostics d2;
        assert(!PassManager::run(m, *bad, reg, r, d2));
        assert(IntToBvStub::ran == 0);
        assert(BitmaskStub::ran == 0);
        assert(d2.firstErrorCode() == ErrorCode::E_PASS_PIPELINE);
    }

    // Right order validates and runs.
    {
        const auto good = EncodingProfile::make(
            "good", {PassSpec{"int-to-bv", {{"width", "16"}}},
                     PassSpec{"alldiff-bitmask", {}}},
            Fidelity{false, false, false, {}});   // floor permits approximation
        ConstraintModel m = intModel();
        Diagnostics d;
        assert(PassManager::validate(m, *good, reg, d));
        assert(!d.hasErrors());

        IntToBvStub::ran = 0;
        BitmaskStub::ran = 0;
        TranslationReport r;
        Diagnostics d2;
        assert(PassManager::run(m, *good, reg, r, d2));
        assert(IntToBvStub::ran == 1);
        assert(BitmaskStub::ran == 1);
        // The pass recorded its choice and the parameter reached it.
        assert(r.choices().size() == 1);
        assert(r.fidelity().bounds.size() == 1);
        assert(r.fidelity().bounds[0].value == 16);
    }

    // An unknown pass id is a configuration error, not a silent skip.
    {
        const auto unknown = EncodingProfile::make(
            "u", {PassSpec{"does-not-exist", {}}}, Fidelity::exact());
        ConstraintModel m = intModel();
        Diagnostics d;
        assert(!PassManager::validate(m, *unknown, reg, d));
        assert(d.firstErrorCode() == ErrorCode::E_PASS_PIPELINE);
    }

    // The terminal check: a pass that introduces a feature nothing eliminates
    // leaves the model not fully lowered. Neither pass is unknown and neither
    // has a requires_absent violation, so only the terminal check explains the
    // rejection -- this isolates it from the other two checks above.
    //
    // The feature was put there by a pass in this profile, not by the input, so
    // this stays E_PASS_PIPELINE: the profile composes a pass whose output no
    // other pass consumes. Calling it E_UNSUPPORTED_CONSTRUCT would count a
    // profile-composition defect as thin coverage of an input language that
    // never mentioned reification at all.
    {
        const auto leftover = EncodingProfile::make(
            "leftover", {PassSpec{"int-to-bv", {}}, PassSpec{"reify-stub", {}}},
            Fidelity{false, false, false, {}});
        ConstraintModel m = intModel();
        Diagnostics d;
        assert(!PassManager::validate(m, *leftover, reg, d));
        assert(d.hasErrors());
        assert(d.firstErrorCode() == ErrorCode::E_PASS_PIPELINE);
        // Naming both is what makes the message actionable: which feature
        // survived, and which pass in this profile produced it.
        assert(mentions(d.all()[0].message, "reification"));
        assert(mentions(d.all()[0].message, "reify-stub"));
        assert(mentions(d.all()[0].message, "'leftover'"));
    }

    // A soft constraint is a high-level feature nothing lowers yet, so it must
    // survive validate()'s leftover check rather than be erased from it. Erasing
    // it let a pipeline with no notion of weights or groups validate anyway,
    // and HirToParser then asserted the constraint as a hard one -- the weight
    // and group silently gone, with no diagnostic and no fidelity change.
    //
    // What it is reported *as* matters as much as that it is reported.
    // ErrorCode is the denominator of the evaluation's failure-cause breakdown
    // (diagnostic.h says so), and this is the leftover every OPB/WBO/WCNF
    // instance reaches -- the design spec routes their weights through
    // softConstraint(). Filing them all under E_PASS_PIPELINE would blame the
    // profile for inputs that no profile could have translated, and count thin
    // construct coverage as a pipeline defect.
    {
        const auto any = EncodingProfile::make(
            "any", {PassSpec{"int-to-bv", {}}}, Fidelity{false, false, false, {}});
        // The subject used to be soft-constraint. It stopped being a valid
        // subject on 2026-08-12, when Parser::assertSoft and the matching
        // dumpSMT2 emission landed and PassManager::validate began erasing
        // feat::softConstraint() the way it erases feat::quantifier() -- both
        // lower natively, so neither is an "input construct we have no encoding
        // for" any more. The (a)/(b)/(c) contrast is about distinguishing an
        // unsupported CONSTRUCT from a misconfigured PIPELINE and is worth
        // keeping, so the subject moved to a feature that still has no native
        // lowering rather than the test being deleted.
        ConstraintModel m = intModel();
        Constraint s;
        s.formula = mkGlobal("alldifferent",
                             {mkIdent("a", Sort::array(Sort::integer(),
                                                       Sort::integer())),
                              mkInt(0), mkInt(3)});
        m.constraints.push_back(s);
        assert(m.features().count(feat::globalConstraint()) == 1);

        // (a) No registered pass eliminates global-constraint anywhere in
        //     `reg_none`, and the input is where it came from: an input
        //     construct we have no encoding for, named in the message.
        PassRegistry reg_none;
        reg_none.add(std::make_shared<IntToBvStub>());
        reg_none.add(std::make_shared<ReifyStub>());
        Diagnostics d;
        assert(!PassManager::validate(m, *any, reg_none, d));
        assert(d.hasErrors());
        assert(d.firstErrorCode() == ErrorCode::E_UNSUPPORTED_CONSTRUCT);
        assert(mentions(d.all()[0].message, "global-constraint"));

        // (b) The control that makes (a) mean something: identical model,
        //     identical profile, a registry differing only in that it contains
        //     a pass which does eliminate soft-constraint. Now nothing is
        //     unsupported -- this profile simply does not run that pass -- and
        //     the code must change to the configuration one, naming the profile
        //     and the pass that would have lowered it. Two inputs differing in
        //     one respect, two different codes: neither test alone could show
        //     the causes are distinguished rather than one code renamed.
        // `reg` differs from `reg_none` in exactly one pass: alldiff-bitmask,
        //     which eliminates global-constraint.
        Diagnostics d2;
        assert(!PassManager::validate(m, *any, reg, d2));
        assert(d2.hasErrors());
        assert(d2.firstErrorCode() == ErrorCode::E_PASS_PIPELINE);
        assert(mentions(d2.all()[0].message, "global-constraint"));
        assert(mentions(d2.all()[0].message, "'any'"));
        assert(mentions(d2.all()[0].message, "alldiff-bitmask"));

        // (c) ...and a profile that does run that pass validates, so what (b)
        //     reports is a pass the profile is missing and not the mere
        //     presence of the feature.
        const auto with_soft = EncodingProfile::make(
            "with-soft", {PassSpec{"int-to-bv", {}}, PassSpec{"alldiff-bitmask", {}}},
            Fidelity{false, false, false, {}});
        Diagnostics d3;
        assert(PassManager::validate(m, *with_soft, reg, d3));
        assert(!d3.hasErrors());

        // The same model without the soft constraint validates, so what the
        // pipeline rejects is the unlowerable feature and not the model.
        ConstraintModel hard = intModel();
        Diagnostics d4;
        assert(PassManager::validate(hard, *any, reg, d4));
        assert(!d4.hasErrors());
    }

    // A pipeline that leaves the resulting fidelity below the profile floor is
    // rejected, which is how "strict" refuses lossy translations.
    {
        const auto strict = EncodingProfile::make(
            "s", {PassSpec{"int-to-bv", {}}}, Fidelity::exact());
        ConstraintModel m = intModel();
        TranslationReport r;
        Diagnostics d;
        assert(!PassManager::run(m, *strict, reg, r, d));
        assert(d.firstErrorCode() == ErrorCode::E_FIDELITY_REJECTED);
    }

    std::cout << "All PassManager tests passed." << std::endl;
    return 0;
}
