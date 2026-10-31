/* -*- Header -*-
 *
 * Pass and PassManager — feature elimination with a pre-flight check.
 *
 * Encodings depend on one another in a partial order: a bitmask encoding of
 * alldifferent presupposes that integers have already become bit-vectors.
 * PassTraits states that as requires_absent, and PassManager::validate replays
 * the pipeline symbolically over the model's actual features before running
 * anything. A misordered profile is therefore rejected up front rather than
 * producing a silently wrong SMT file that then hides inside a batch.
 *
 * That check is the main reason this design has a pass pipeline at all rather
 * than one large lowering function.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#ifndef SOMTPARSER_TRANSLATION_PASS_HEADER
#define SOMTPARSER_TRANSLATION_PASS_HEADER

#include "somtparser/translation/diagnostic.h"
#include "somtparser/hir/feature.h"
#include "somtparser/hir/hir.h"
#include "somtparser/translation/profile.h"
#include "somtparser/translation/report.h"

#include <memory>
#include <string>
#include <unordered_map>
#include <vector>

namespace SOMTParser::Uir {

struct PassTraits {
    /** These features must already be gone when the pass runs. */
    std::vector<Feature> requires_absent;
    std::vector<Feature> eliminates;
    std::vector<Feature> introduces;

    /** Whether this pass reads EncodingProfile::style() and behaves differently
     *  for GROUND than for QUANTIFIED.
     *
     *  Declaring it is what stops the two style profiles from being decorative.
     *  A profile can name a style, but if nothing in its pipeline consumes the
     *  name then selecting it changes nothing, and the user gets output
     *  identical to the other style with no indication -- the failure class
     *  docs/known-defects-2026-08-11.md §4 is entirely about. translate()
     *  therefore warns when a profile declares a style and no pass claims it.
     *  No pass sets this today; cluster A's decomposition pass will. */
    bool reads_encoding_style = false;
    /** True only when run() leaves compact variable ranges and packed clauses
     *  semantically unchanged. */
    bool preserves_packed_clauses = false;
    /** Leaves packed numeric rows and the declaration indices they reference
     * semantically intact; declaration bounds may change with reported fidelity. */
    bool preserves_packed_linear_rows = false;
    /** Preserves finite scalar ranges, ordinary declaration indices, and the
     * meaning/signature of every function referenced by packed applications. */
    bool preserves_packed_scalar_calls = false;
};

struct LowerContext {
    TranslationReport* report = nullptr;
    Diagnostics*       diagnostics = nullptr;
    const PassSpec*    spec = nullptr;    // this pass's parameters
    /** The profile being run. A pass needs it for policy that is profile-level
     *  rather than per-pass -- EncodingProfile::style() is the one such policy
     *  today, and it is profile-level because several passes must answer the
     *  same question identically within one translation. */
    const EncodingProfile* profile = nullptr;
};

class Pass {
public:
    virtual ~Pass() = default;
    virtual std::string id() const = 0;
    virtual PassTraits  traits() const = 0;
    /** Returns false on an unrecoverable failure, having recorded a diagnostic. */
    virtual bool run(Hir::ConstraintModel& model, LowerContext& ctx) = 0;
};

using PassPtr = std::shared_ptr<Pass>;

class PassRegistry {
public:
    /** Process-wide registry the built-in passes install themselves into. */
    static PassRegistry& instance();

    void  add(PassPtr p);
    Pass* get(const std::string& id) const;
    std::vector<std::string> ids() const;

private:
    std::unordered_map<std::string, PassPtr> passes_;
};

/**
 * Does any pass in @p profile's pipeline declare that it reads the encoding
 * style?
 *
 * Extracted from translate() so that both answers are testable. Inline in
 * translate() it was not: translate() resolves profiles by id and only builtin
 * ids exist, so no test could hand it a pipeline whose pass consumes the style,
 * and the "warning retires" half went unchecked -- a check that cannot fail,
 * which is the defect class docs/known-defects-2026-08-11.md §4 is about. A
 * breakage probe caught exactly that and this is the fix.
 */
bool encodingStyleIsConsumed(const EncodingProfile& profile,
                             const PassRegistry& registry);

class PassManager {
public:
    /**
     * Replay the pipeline symbolically over the model's features. Checks that
     * every pass exists, that its requires_absent holds at that point, and that
     * the pipeline ends with no high-level feature left. Runs no pass.
     *
     * A feature that survives the replay is reported under the code that names
     * the actual cause, because ErrorCode is the denominator of the
     * evaluation's failure-cause breakdown (see diagnostic.h):
     *
     *  - E_UNSUPPORTED_CONSTRUCT when the feature came from the input and no
     *    pass in @p registry eliminates it at all. Thin construct coverage;
     *    no profile could have translated this input. Names the feature.
     *  - E_PASS_PIPELINE when some registered pass does eliminate it but this
     *    profile does not run it (or runs it too early), or when a pass in the
     *    profile introduced a feature nothing consumes. A configuration
     *    problem. Names the profile, plus the passes that could have lowered
     *    it or the pass that introduced it.
     */
    static bool validate(const Hir::ConstraintModel& model,
                         const EncodingProfile& profile,
                         const PassRegistry& registry,
                         Diagnostics& diagnostics);

    /**
     * validate(), then execute in order, then check the accumulated fidelity
     * against the profile floor. Executes nothing if validation fails.
     */
    static bool run(Hir::ConstraintModel& model,
                    const EncodingProfile& profile,
                    const PassRegistry& registry,
                    TranslationReport& report,
                    Diagnostics& diagnostics);
};

} // namespace SOMTParser::Uir

#endif /* SOMTPARSER_TRANSLATION_PASS_HEADER */
