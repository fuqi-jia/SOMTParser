/* -*- Source -*-
 * EncodingProfile: built-in profiles and content hashing.
 * Copyright (C) 2026 Fuqi Jia
 */

#include "somtparser/translation/profile.h"
#include "somtparser/core/asserting.h"

#include <cstdint>
#include <exception>
#include <sstream>
#include <string>
#include <utility>

namespace SOMTParser::Uir {

namespace {

/** FNV-1a. Chosen over std::hash because the digest must be identical across
 *  runs, compilers and machines -- it is recorded in experiment data. */
std::string fnv1a64Hex(const std::string& s) {
    std::uint64_t h = 1469598103934665603ULL;
    for (const unsigned char c : s) {
        h ^= c;
        h *= 1099511628211ULL;
    }
    std::string out(16, '0');
    for (int i = 15; i >= 0; --i) {
        out[static_cast<std::size_t>(i)] = "0123456789abcdef"[h & 0xF];
        h >>= 4;
    }
    return out;
}

/** `default` and `strict`: exact, and they decompose global constraints.
 *
 *  Both pipelines were empty, on the reasoning that "the minimal HIR is already
 *  feature-free apart from int variables, which lower natively". That was true
 *  of the walking skeleton and stopped being true when `Hir::Global` arrived:
 *  from then on **every model containing `alldifferent` was refused** under
 *  `default` with `E_PASS_PIPELINE`, naming a pass that existed, was
 *  registered, and was `exact()` -- it simply sat in no pipeline the CLI
 *  reaches without a flag. The most idiomatic constraint model there is did not
 *  translate, and the coverage tables could not show it, because the frontend
 *  had read the construct perfectly and the refusal happened a layer later.
 *
 *  The style is GROUND and it is stated rather than left UNSPECIFIED. The pass
 *  reads UNSPECIFIED as ground anyway, so declaring it changes no behaviour;
 *  what it changes is that `encodingStyleIsConsumed` can check it, and that a
 *  reader of the profile learns which of two admissible encodings this is
 *  without having to know the pass's fallback. The choice is recorded per
 *  construct as an `EncodingChoice` (`alldifferent-distinct`), so it is visible
 *  in the report rather than made silently here.
 *
 *  Ground and quantified are BOTH exact on the established SAT/objective
 *  axes -- they differ in output size and solver behaviour, not in those
 *  guarantees -- so this does not move the profile floor. Count remains
 *  unassessed unless its own evidence is recorded. One consequence is worth
 *  knowing: the ground encoding enumerates the index range, so an
 *  `alldifferent` whose bounds are not literals is refused under `default`
 *  with a message pointing at `quantified`. That is a narrower refusal than
 *  the one it replaces, and an actionable one.
 */
std::shared_ptr<const EncodingProfile> makeDefault() {
    Fidelity floor = Fidelity::exact();
    // No built-in profile demands count preservation. A floor gates which
    // ENCODINGS a pipeline may use, and an encoding that is perfectly good for
    // a satisfiability or optimisation query may still multiply the model
    // count -- the OPB WBO relaxation is exactly that. Counting is a property
    // of the QUESTION, so the gate lives where the question is asked.
    return EncodingProfile::make("default",
                                 {PassSpec{"decompose-globals", {}}},
                                 floor, EncodingStyle::GROUND);
}

std::shared_ptr<const EncodingProfile> makeStrict() {
    Fidelity floor = Fidelity::exact();
    return EncodingProfile::make("strict",
                                 {PassSpec{"decompose-globals", {}}},
                                 floor, EncodingStyle::GROUND);
}

/** The under-approximation direction, with no passes.
 *
 *  `default` and `strict` both demand soundness AND completeness, so a
 *  translation that records an honest approximation cannot be produced under
 *  either -- it is refused rather than labelled. That is right for a
 *  translation that could have been exact and was not. It is wrong for one that
 *  cannot be exact even in principle: **bounded model checking is
 *  under-approximate by construction**, so every BTOR2 instance was
 *  untranslatable under every built-in profile.
 *
 *  So this is the floor for a bounded question: `sound` holds -- a trace found
 *  within k steps is a real trace -- and `complete` does not, because "no
 *  counterexample within k" is not "safe". `bv32` has the same two flags and a
 *  bound-ints pipeline, which is a different reason for the same shape; the
 *  BOUND here comes from the frontend rather than from a pass.
 *
 *  Whether `default` should also admit an approximation now that one is
 *  RECORDED rather than silent is a separate question, left alone here: the
 *  test that pins the current floor says "no silent approximation", and the
 *  word that matters is silent.
 *
 *  It decomposes global constraints, as every built-in profile now does. This
 *  pipeline was empty and that was read as "a bounded question needs no
 *  eliminating pass" -- but an empty pipeline does not decline to encode a
 *  global constraint, it REFUSES THE MODEL, and the two are not the same
 *  answer. A profile's fidelity floor is where a profile says what it will not
 *  preserve; its pipeline is not, and using an empty one to express a scope
 *  decision made every such model unanswerable under it rather than answered
 *  approximately. */
std::shared_ptr<const EncodingProfile> makeBmc() {
    Fidelity f;
    f.complete = false;
    f.preserves_optimum = false;
    return EncodingProfile::make("bmc", {PassSpec{"decompose-globals", {}}}, f,
                                 EncodingStyle::GROUND);
}

/** Preserve the feasible set but permit an optimization problem to be emitted
 * as plain SMT. This is intentionally separate from `default`: selecting the
 * `none` dialect drops the objective and therefore cannot satisfy an exact
 * optimum-preservation floor. */
std::shared_ptr<const EncodingProfile> makeFeasibility() {
    Fidelity floor = Fidelity::exact();
    floor.preserves_optimum = false;
    return EncodingProfile::make("feasibility",
                                 {PassSpec{"decompose-globals", {}}},
                                 floor, EncodingStyle::GROUND);
}

/** The two profiles named after the encoding style they select.
 *
 *  They run cluster A's global-constraint decomposition, which reads the style
 *  and encodes each global accordingly. The check in translate() -- a profile
 *  declaring a style no pass in its pipeline consumes says so out loud -- is
 *  what kept them honest while the pass did not yet exist, and it stays silent
 *  now because decompose-globals sets reads_encoding_style.
 *
 *  Since 2026-08-17 they are no longer the ONLY profiles that decompose; every
 *  built-in one does. What still distinguishes these two is that the style is
 *  what they are for, rather than a position they take in passing. */
std::shared_ptr<const EncodingProfile> makeGround() {
    // Both styles are exact on the established SAT/objective axes: they differ
    // in size and solver behaviour, so the floor cannot separate them. Count
    // preservation is not required by this profile.
    Fidelity floor = Fidelity::exact();
    return EncodingProfile::make("ground",
                                 {PassSpec{"decompose-globals", {}}},
                                 floor, EncodingStyle::GROUND);
}

std::shared_ptr<const EncodingProfile> makeQuantified() {
    Fidelity floor = Fidelity::exact();
    return EncodingProfile::make("quantified",
                                 {PassSpec{"decompose-globals", {}}},
                                 floor, EncodingStyle::QUANTIFIED);
}

std::shared_ptr<const EncodingProfile> makeBv32() {
    // Despite the name, this does not convert Int to a bit-vector sort -- that
    // needs a BV Sort in HIR, which is Plan 6's scope. Until then "bv32" bounds
    // every unbounded Int variable's domain to a signed 32-bit range instead,
    // via "bound-ints". That is a real, honestly-recorded loss (the floor
    // below reflects it), not the bit-vector encoding the id suggests; a
    // profile_id that promised bit-vectors while delivering range constraints
    // would mislead a reader of the experiment data.
    Fidelity floor;
    floor.complete = false;           // a fixed width loses solutions outside it
    floor.preserves_optimum = false;
    // decompose-globals FIRST, and the order is the interesting part.
    //
    // It makes no difference today: bound-ints walks `model.decls` only, and
    // the ground decomposition introduces no declarations, so the two commute
    // and either order emits the same script.
    //
    // It is ordered this way for what happens when that stops being true. This
    // profile's promise is that EVERY otherwise-unbounded Int is clamped to the
    // recorded width; `minizinc.md` §4.3 names a bitmask/one-hot encoding of
    // `alldifferent` as a third admissible decomposition, and that one does
    // introduce variables. Running bound-ints first would leave them
    // unclamped -- while the report still carried a `Bound{BV_WIDTH, 32}`
    // saying they were. The floor would be a claim about a model the pipeline
    // no longer produced, which is the one failure mode this whole structure
    // exists to prevent.
    return EncodingProfile::make(
        "bv32",
        {PassSpec{"decompose-globals", {}}, PassSpec{"bound-ints", {{"width", "32"}}}},
        floor, EncodingStyle::GROUND);
}

} // namespace

std::string PassSpec::param(const std::string& key, const std::string& dflt) const {
    const auto it = params.find(key);
    return it == params.end() ? dflt : it->second;
}

long long PassSpec::intParam(const std::string& key, long long dflt) const {
    const auto it = params.find(key);
    if (it == params.end()) {
        return dflt;                      // absent is legitimate: use the default
    }
    // Present but unparseable is NOT legitimate. Silently substituting the
    // default would let a profile typo -- width = "abc" -- run as width = 32
    // while the report claims 32 was chosen deliberately. That makes the
    // recorded provenance a lie, which is worse than a crash.
    std::size_t consumed = 0;
    long long   value = 0;
    try {
        value = std::stoll(it->second, &consumed);
    } catch (const std::exception& e) {
        condAssert(false, "pass parameter '" + key + "' has non-integer value '"
                              + it->second + "': " + e.what());
    }
    condAssert(consumed == it->second.size(),
               "pass parameter '" + key + "' has trailing characters in value '"
                   + it->second + "'");
    return value;
}

const char* encodingStyleName(EncodingStyle s) {
    switch (s) {
    case EncodingStyle::UNSPECIFIED: return "unspecified";
    case EncodingStyle::GROUND:      return "ground";
    case EncodingStyle::QUANTIFIED:  return "quantified";
    }
    // A new style must fail here rather than print a stand-in: the evaluation
    // groups result rows by this string, and an unnamed style would silently
    // join whichever bucket the stand-in named.
    condAssert(false, "encodingStyleName: unhandled EncodingStyle");
    return "";   // unreachable; condAssert always throws
}

std::shared_ptr<const EncodingProfile> EncodingProfile::make(
        std::string id, std::vector<PassSpec> pipeline, Fidelity min_fidelity,
        EncodingStyle style) {
    auto p = std::make_shared<EncodingProfile>();
    p->id_ = std::move(id);
    p->pipeline_ = std::move(pipeline);
    p->min_fidelity_ = std::move(min_fidelity);
    p->style_ = style;
    return p;
}

std::string EncodingProfile::contentHash() const {
    if (!cached_hash_.empty()) {
        return cached_hash_;
    }
    std::ostringstream o;
    o << id_ << '|'
      << (min_fidelity_.sound ? '1' : '0')
      << (min_fidelity_.complete ? '1' : '0')
      << (min_fidelity_.preserves_optimum ? '1' : '0')
      << countStatusName(min_fidelity_.count_status) << '|'
      << encodingStyleName(style_) << '|';
    for (const auto& ps : pipeline_) {
        o << ps.pass_id << '(';
        for (const auto& kv : ps.params) {     // std::map: deterministic order
            o << kv.first << '=' << kv.second << ';';
        }
        o << ')';
    }
    cached_hash_ = fnv1a64Hex(o.str());
    return cached_hash_;
}

std::shared_ptr<const EncodingProfile> EncodingProfile::builtin(std::string_view id) {
    if (id == "default") { static const auto p = makeDefault(); return p; }
    if (id == "strict")  { static const auto p = makeStrict();  return p; }
    if (id == "bv32")    { static const auto p = makeBv32();    return p; }
    if (id == "bmc")     { static const auto p = makeBmc();     return p; }
    if (id == "feasibility") {
        static const auto p = makeFeasibility();
        return p;
    }
    if (id == "ground")     { static const auto p = makeGround();     return p; }
    if (id == "quantified") { static const auto p = makeQuantified(); return p; }
    return nullptr;
}

std::vector<std::string> EncodingProfile::builtinIds() {
    return {"default", "strict", "bmc", "feasibility", "bv32", "ground",
            "quantified"};
}

} // namespace SOMTParser::Uir
