/* -*- Header -*-
 *
 * EncodingProfile — an encoding choice is a pass pipeline configuration.
 *
 * "Strict mode" is a profile whose min_fidelity demands both soundness and
 * completeness, not a separate flag. That way strict, default and aggressive
 * are three points on one experimental axis and can be compared side by side.
 *
 * Parameters are plain strings, matching the existing
 * GlobalOptions::setOption(key, value) convention. That keeps the public header
 * free of any JSON dependency, maps directly onto a Python dict, and keeps the
 * ABI stable.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#ifndef SOMTPARSER_TRANSLATION_PROFILE_HEADER
#define SOMTPARSER_TRANSLATION_PROFILE_HEADER

#include "somtparser/translation/fidelity.h"

#include <map>
#include <memory>
#include <string>
#include <string_view>
#include <vector>

namespace SOMTParser::Uir {

using ParamMap = std::map<std::string, std::string>;

struct PassSpec {
    std::string pass_id;
    ParamMap    params;

    std::string param(const std::string& key, const std::string& dflt) const;
    long long   intParam(const std::string& key, long long dflt) const;
};

/**
 * Whether a construct with a finite index set is expanded or kept quantified.
 *
 * This is a *cross-cutting* policy rather than one pass's parameter, which is
 * why it lives on the profile: a global-constraint decomposition, a
 * comprehension and an array-indexed constraint all face the same question and
 * must answer it the same way within one translation.
 *
 *     alldifferent(a[1..n])
 *       GROUND      AND over i<j of  a_i != a_j          O(n^2) assertions
 *       QUANTIFIED  forall i,j. 1<=i<j<=n -> select(a,i) != select(a,j)   O(1)
 *
 * Both are Fidelity::exact(), which is the point: they are not a fidelity
 * trade-off but a size-and-solver-behaviour one, so the min_fidelity floor
 * cannot distinguish them and an experiment must. CP and SAT toolchains emit
 * ground encodings because their targets cannot do better; an SMT solver can
 * take either, and which wins is a measurement rather than a guess.
 *
 * UNSPECIFIED means the profile takes no position -- correct for profiles whose
 * pipelines contain nothing that faces the question.
 */
enum class EncodingStyle { UNSPECIFIED, GROUND, QUANTIFIED };

/** Stable name for reports. Throws on a value outside the enum rather than
 *  returning a stand-in, which the evaluation would group as a real style. */
const char* encodingStyleName(EncodingStyle s);

class EncodingProfile {
public:
    const std::string&           id() const noexcept { return id_; }
    const std::vector<PassSpec>& pipeline() const noexcept { return pipeline_; }
    const Fidelity&              minFidelity() const noexcept { return min_fidelity_; }
    EncodingStyle                style() const noexcept { return style_; }

    /** Stable 16-hex-digit digest of id, pipeline and floor. Goes into
     *  Provenance so a result row can be traced back to a configuration. */
    std::string contentHash() const;

    /** Returns nullptr for an unknown id. Callers must not fall back to
     *  "default" silently: a result row would then misreport its profile. */
    static std::shared_ptr<const EncodingProfile> builtin(std::string_view id);
    static std::vector<std::string> builtinIds();

    static std::shared_ptr<const EncodingProfile> make(
        std::string id,
        std::vector<PassSpec> pipeline,
        Fidelity min_fidelity,
        EncodingStyle style = EncodingStyle::UNSPECIFIED);

private:
    std::string           id_;
    std::vector<PassSpec> pipeline_;
    Fidelity              min_fidelity_;
    EncodingStyle         style_ = EncodingStyle::UNSPECIFIED;
    mutable std::string   cached_hash_;
};

} // namespace SOMTParser::Uir

#endif /* SOMTPARSER_TRANSLATION_PROFILE_HEADER */
