/* -*- Header -*-
 *
 * TranslationReport — the audit trail for one translation.
 *
 * The research question is how SMT performs across domains. Answering it
 * requires separating "SMT is slow here" from "we translated this domain
 * badly", so every translation records which encoding was chosen at each site,
 * how faithful it was, what the input actually looked like, and enough
 * provenance to rebuild the exact configuration months later.
 *
 * The aggregate fidelity is the lattice meet over every choice, so a single
 * approximation anywhere downgrades the whole instance -- which is precisely
 * what the results tables must stratify on.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#ifndef SOMTPARSER_TRANSLATION_REPORT_HEADER
#define SOMTPARSER_TRANSLATION_REPORT_HEADER

#include "somtparser/translation/diagnostic.h"
#include "somtparser/translation/fidelity.h"

#include <cstddef>
#include <map>
#include <optional>
#include <string>
#include <utility>
#include <vector>

namespace SOMTParser::Uir {

struct EncodingChoice {
    std::string site;         // source location or constraint id
    std::string unified_op;   // e.g. "alldifferent"
    std::string strategy;     // e.g. "pairwise-distinct"
    Fidelity    fidelity;
    std::string rationale;
    /** Required when this local choice claims count preservation. */
    std::optional<CountEvidence> count_evidence{};
};

/** Everything needed to reproduce this translation later. Without it an
 *  experiment row cannot be traced back to a configuration. */
struct Provenance {
    std::string somtparser_version;
    std::string language_id;
    std::string language_version;
    std::string ops_schema_version;
    std::string ops_content_hash;
    std::string profile_id;
    std::string profile_content_hash;
    std::string target_dialect;
};

struct Stats {
    std::size_t num_vars = 0;
    std::size_t num_constraints = 0;
    std::size_t num_objectives = 0;
    std::size_t num_smt_nodes = 0;
    /**
     * The maximum number of quantifier *alternations* on any path through the
     * model: consecutive quantifiers of the same kind count once, so `forall
     * exists` is 1 and `forall forall exists` is also 1.
     *
     * Reported because it is the parameter QBF difficulty is organised around
     * -- the polynomial hierarchy's levels ARE alternation counts, and QBF
     * solvers are engineered against the prefix structure. Without it a result
     * comparing an SMT solver to a QBF solver cannot be stratified, and
     * "SMT is slower on QBF" is not a finding
     * (docs/languages/qdimacs.md §4.3).
     *
     * Zero for a quantifier-free model, which is every language outside
     * cluster C.
     */
    std::size_t max_quantifier_alternations = 0;
    double      translate_ms = 0.0;

    /**
     * Where `translate_ms` went, by pipeline stage. Reported because a total
     * cannot be optimised against: a sweep that found translation growing
     * super-linearly in clause count could say only that it did, not which of
     * the four stages was responsible.
     *
     * They sum to slightly less than `translate_ms`, which also covers
     * registry lookup, option validation and report assembly.
     */
    double      parse_ms = 0.0;
    double      typecheck_ms = 0.0;
    double      passes_ms = 0.0;
    double      lower_ms = 0.0;
    /** The contract/fidelity accounting after lowering: building the
     *  relational->SMT contract, meeting the fidelity over every choice the
     *  target stage recorded, and validating the stage chain. */
    double      semantics_ms = 0.0;
};

class TranslationReport {
public:
    void setDetailsEnabled(bool enabled) { details_enabled_ = enabled; }
    bool detailsEnabled() const noexcept { return details_enabled_; }
    // Fidelity gates remain active when optional audit records are disabled.
    void beginPhase() { phase_active_ = true; phase_has_choice_ = false; }
    Fidelity phaseFidelity() const { return phase_has_choice_ ? phase_fidelity_ : Fidelity::exact(); }
    /** Record a choice and fold its fidelity into the aggregate. */
    void addChoice(EncodingChoice c);

    /** Fold a frontend's report into this one.
     *
     *  A frontend owns its encoding choices and its warnings, and nothing else.
     *  Provenance, stats, feature counts and theory usage are filled by
     *  translate() from the model *after* parsing, so anything a frontend wrote
     *  into them would be overwritten without a word. Rather than let that be a
     *  silent loss, this refuses it: a frontend writing one of those fields has
     *  the ownership wrong, and should hear about it on its first run rather
     *  than on the day someone reads the experiment database and finds a
     *  provenance that is not the configuration that ran.
     *
     *  Choices go through addChoice, so the aggregate fidelity *meets* rather
     *  than being copied -- a frontend approximation downgrades the instance
     *  exactly as a pass approximation does. */
    void mergeFrontend(const TranslationReport& frontend);

    const Fidelity&                    fidelity() const noexcept { return fidelity_; }
    const std::vector<EncodingChoice>& choices()  const noexcept { return choices_; }

    const Provenance& provenance() const noexcept { return provenance_; }
    Provenance&       mutableProvenance() noexcept { return provenance_; }

    const Stats& stats() const noexcept { return stats_; }
    Stats&       mutableStats() noexcept { return stats_; }

    /** Domain fingerprint: which high-level constructs the input used. */
    const std::map<std::string, std::size_t>& featureCounts() const noexcept { return feature_counts_; }
    std::map<std::string, std::size_t>&       mutableFeatureCounts() noexcept { return feature_counts_; }

    const std::map<std::string, std::size_t>& theoryUsage() const noexcept { return theory_usage_; }
    std::map<std::string, std::size_t>&       mutableTheoryUsage() noexcept { return theory_usage_; }

    void addWarning(Diagnostic d) { if (details_enabled_) warnings_.push_back(std::move(d)); }
    const std::vector<Diagnostic>& warnings() const noexcept { return warnings_; }

    /** Serialised for the evaluation database. JSON lives only in the .cpp. */
    std::string toJson() const;

private:
    bool details_enabled_ = true, phase_active_ = false, phase_has_choice_ = false;
    Fidelity phase_fidelity_;
    Fidelity                           fidelity_;   // conservative unknown until evidence/choices
    bool                               has_choice_ = false;
    std::vector<EncodingChoice>        choices_;
    Provenance                         provenance_;
    Stats                              stats_;
    std::map<std::string, std::size_t> feature_counts_;
    std::map<std::string, std::size_t> theory_usage_;
    std::vector<Diagnostic>            warnings_;
};

} // namespace SOMTParser::Uir

#endif /* SOMTPARSER_TRANSLATION_REPORT_HEADER */
