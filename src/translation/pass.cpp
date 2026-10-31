/* -*- Source -*-
 * PassRegistry and PassManager.
 * Copyright (C) 2026 Fuqi Jia
 */

#include "somtparser/translation/pass.h"

#include "somtparser/core/asserting.h"

#include <algorithm>
#include <new>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace SOMTParser::Uir {

namespace {

using FeatureSet = std::unordered_set<Feature, Feature::Hash>;

/** Ids of every registered pass that declares it eliminates @p f, sorted.
 *  Sorted because PassRegistry stores an unordered_map and this list is
 *  quoted into a diagnostic message the evaluation reads back: an order that
 *  varies run to run would make two identical failures look different. */
std::vector<std::string> eliminatorsOf(const PassRegistry& registry, Feature f) {
    std::vector<std::string> out;
    for (const auto& id : registry.ids()) {
        const Pass* p = registry.get(id);
        // ids() is built from the same map get() reads, so a null here means
        // the registry's own invariant is broken, not a runtime condition.
        condAssert(p != nullptr,
                   "PassRegistry: ids() named '" + id + "' but get() returned null");
        const PassTraits t = p->traits();
        if (std::find(t.eliminates.begin(), t.eliminates.end(), f) != t.eliminates.end()) {
            out.push_back(id);
        }
    }
    std::sort(out.begin(), out.end());
    return out;
}

std::string quotedList(const std::vector<std::string>& ids) {
    std::string out;
    for (const auto& id : ids) {
        if (!out.empty()) { out += ", "; }
        out += '\'' + id + '\'';
    }
    return out;
}

} // namespace

PassRegistry& PassRegistry::instance() {
    static PassRegistry r;
    return r;
}

void PassRegistry::add(PassPtr p) {
    // A null pass is a caller bug, never an input condition. Swallowing it
    // would leave the profile that names this pass rejecting with
    // E_PASS_PIPELINE as if the pass had never been written. Matches
    // LanguageRegistry::add.
    condAssert(p != nullptr, "PassRegistry::add: null pass");
    passes_[p->id()] = std::move(p);
}

Pass* PassRegistry::get(const std::string& id) const {
    const auto it = passes_.find(id);
    return it == passes_.end() ? nullptr : it->second.get();
}

std::vector<std::string> PassRegistry::ids() const {
    std::vector<std::string> out;
    out.reserve(passes_.size());
    for (const auto& kv : passes_) {
        out.push_back(kv.first);
    }
    return out;
}

bool encodingStyleIsConsumed(const EncodingProfile& profile,
                             const PassRegistry& registry) {
    if (profile.style() == EncodingStyle::UNSPECIFIED) {
        // Nothing was claimed, so nothing is unconsumed. Answering "false" here
        // would make translate() warn about every ordinary profile.
        return true;
    }
    for (const auto& spec : profile.pipeline()) {
        const Pass* p = registry.get(spec.pass_id);
        if (p != nullptr && p->traits().reads_encoding_style) {
            return true;
        }
    }
    return false;
}

bool PassManager::validate(const Hir::ConstraintModel& model,
                           const EncodingProfile& profile,
                           const PassRegistry& registry,
                           Diagnostics& diagnostics) {
    const FeatureSet from_input = model.features();
    FeatureSet present = from_input;
    // Which pass put a feature into the model that the input did not have, so
    // a leftover can name the pass responsible instead of blaming the input.
    std::unordered_map<Feature, std::string, Feature::Hash> introduced_by;
    bool ok = true;

    for (const auto& spec : profile.pipeline()) {
        const Pass* p = registry.get(spec.pass_id);
        if (p == nullptr) {
            diagnostics.error(ErrorCode::E_PASS_PIPELINE,
                              "profile '" + profile.id() + "' names unknown pass '"
                                  + spec.pass_id + "'");
            ok = false;
            continue;
        }
        const PassTraits t = p->traits();
        if ((!model.bool_var_ranges.empty() || !model.packed_bool_clauses.empty())
            && !t.preserves_packed_clauses) {
            diagnostics.error(ErrorCode::E_PASS_PIPELINE,
                "pass '" + spec.pass_id
                    + "' does not declare preservation of packed Boolean clause HIR");
            ok = false;
        }
        if ((!model.scalar_var_ranges.empty() || model.packed_function_calls)
            && !t.preserves_packed_scalar_calls) {
            diagnostics.error(ErrorCode::E_PASS_PIPELINE,
                "pass '" + spec.pass_id + "' does not declare preservation of compact scalar/call HIR");
            ok = false;
        }
        if (model.packed_linear_rows != nullptr && !t.preserves_packed_linear_rows) {
            diagnostics.error(ErrorCode::E_PASS_PIPELINE,
                "pass '" + spec.pass_id
                    + "' does not declare preservation of packed linear-row HIR");
            ok = false;
        }
        for (const auto& f : t.requires_absent) {
            if (present.count(f) != 0) {
                diagnostics.error(
                    ErrorCode::E_PASS_PIPELINE,
                    "pass '" + spec.pass_id + "' requires feature '"
                        + std::string(f.name())
                        + "' to be eliminated first, but it is still present");
                ok = false;
            }
        }
        for (const auto& f : t.eliminates) {
            present.erase(f);
        }
        for (const auto& f : t.introduces) {
            present.insert(f);
            if (from_input.count(f) == 0) {
                introduced_by[f] = spec.pass_id;
            }
        }
    }

    // Int and real variables lower natively to SMT, so they are not features the
    // pipeline is obliged to eliminate. softConstraint() is deliberately NOT on
    // this list: nothing lowers a soft constraint yet (HirToParser refuses one),
    // so erasing it here would let a pipeline that cannot express weights or
    // groups validate anyway and harden every soft constraint in silence. It
    // therefore reaches the loop below, which files it under
    // E_UNSUPPORTED_CONSTRUCT for as long as no pass eliminates it.
    present.erase(feat::intVar());
    present.erase(feat::realVar());
    present.erase(feat::nonlinear());
    // Quantifiers lower natively too, and that is cluster C's whole point:
    // docs/languages-scoping.md §3.1 records that it needs "**none** -- SMT-LIB
    // natively expresses quantifiers, so this is a straight pass-through to the
    // engine's existing mkForall/mkExists, unlike every other cluster here".
    // Without this erase, decompose-globals -- which introduces quantifiers
    // under the quantified style -- would be reported as introducing a feature
    // no pass eliminates, and the `quantified` profile would reject every model
    // it is meant to encode.
    present.erase(feat::quantifier());
    // Soft constraints lower natively as well, since Parser::assertSoft and the
    // matching dumpSMT2 emission landed on 2026-08-12. Before that HirToParser
    // refused them and this line would have been wrong -- validate() would have
    // waved through a model that then failed one layer down, which is worse
    // than the refusal it replaced. The two changes belong together and landed
    // together.
    present.erase(feat::softConstraint());

    // Report the leftovers in a stable order. `present` is an unordered_set, and
    // which diagnostic is recorded first decides firstErrorCode(), which is the
    // key the evaluation buckets this failure under.
    std::vector<Feature> leftover(present.begin(), present.end());
    std::sort(leftover.begin(), leftover.end(),
              [](Feature a, Feature b) { return a.name() < b.name(); });

    for (const Feature f : leftover) {
        const std::string fname(f.name());
        const std::vector<std::string> eliminators = eliminatorsOf(registry, f);
        if (!eliminators.empty()) {
            // A registered pass could have lowered this one; this profile does
            // not run it (or runs it before whatever puts the feature back).
            // That is a configuration problem and the profile is what is wrong.
            diagnostics.error(ErrorCode::E_PASS_PIPELINE,
                              "profile '" + profile.id() + "' leaves feature '" + fname
                                  + "' unlowered; registered pass(es) that eliminate it: "
                                  + quotedList(eliminators));
        } else if (from_input.count(f) != 0) {
            // No registered pass can ever eliminate it, and the input is where
            // it came from: the input used a construct we have no encoding for.
            // Filing that under E_PASS_PIPELINE would blame the profile for
            // every OPB/WBO/WCNF instance (the design spec routes their weights
            // through softConstraint()) and bury the real, countable cause --
            // thin construct coverage -- under a pipeline-defect count. The
            // header comment on ErrorCode exists to stop exactly that blurring.
            diagnostics.error(ErrorCode::E_UNSUPPORTED_CONSTRUCT,
                              "input feature '" + fname
                                  + "' cannot be lowered: no registered pass eliminates it");
        } else {
            // Not from the input and nothing can eliminate it, so a pass in
            // this profile introduced something no pass consumes. `present`
            // only ever grows through `introduces`, so a feature that is in
            // neither the input nor introduced_by cannot exist.
            const auto it = introduced_by.find(f);
            condAssert(it != introduced_by.end(),
                       "PassManager::validate: feature '" + fname
                           + "' is in neither the input nor any pass's introduces");
            diagnostics.error(ErrorCode::E_PASS_PIPELINE,
                              "profile '" + profile.id() + "' is not a valid pipeline: pass '"
                                  + it->second + "' introduces feature '" + fname
                                  + "' and no registered pass eliminates it");
        }
        ok = false;
    }
    return ok;
}

bool PassManager::run(Hir::ConstraintModel& model,
                      const EncodingProfile& profile,
                      const PassRegistry& registry,
                      TranslationReport& report,
                      Diagnostics& diagnostics) {
    if (!validate(model, profile, registry, diagnostics)) {
        return false;
    }
    for (const auto& spec : profile.pipeline()) {
        Pass* p = registry.get(spec.pass_id);
        LowerContext ctx;
        ctx.report = &report;
        ctx.diagnostics = &diagnostics;
        ctx.spec = &spec;
        ctx.profile = &profile;
        const std::size_t before = diagnostics.all().size();
        bool passed = false;
        try {
            passed = p->run(model, ctx);
        } catch (const std::bad_alloc&) {
            diagnostics.error(ErrorCode::E_RESOURCE,
                "memory allocation failed during HIR passes: '" + spec.pass_id + "'");
            return false;
        }
        if (!passed) {
            // Only speak for the pass when it said nothing. A pass that reported
            // its own cause -- bound-ints rejecting an out-of-range width as
            // E_PASS_PIPELINE, say -- would otherwise have a bare E_INTERNAL
            // stacked on top of it, and the evaluation reads these codes as its
            // failure-cause breakdown.
            if (diagnostics.all().size() == before) {
                diagnostics.error(ErrorCode::E_INTERNAL,
                                  "pass '" + spec.pass_id
                                      + "' failed without recording a cause");
            }
            return false;
        }
    }
    if (!report.fidelity().meets(profile.minFidelity())) {
        diagnostics.error(ErrorCode::E_FIDELITY_REJECTED,
                          "translation fidelity is below the floor required by profile '"
                              + profile.id() + "'");
        return false;
    }
    return true;
}

} // namespace SOMTParser::Uir
