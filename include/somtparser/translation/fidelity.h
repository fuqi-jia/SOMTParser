/* -*- Header -*-
 *
 * Fidelity — how faithfully a translation preserves the original problem.
 *
 * Soundness, completeness, optimum preservation, and model-count preservation
 * are independent guarantees. Under- and over-approximation are incomparable:
 * one keeps SAT answers trustworthy while losing UNSAT, the other does the
 * reverse, and a single translation can suffer both. Count status also has an
 * explicit unassessed state; lack of evidence is not a claim of count loss.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#ifndef SOMTPARSER_TRANSLATION_FIDELITY_HEADER
#define SOMTPARSER_TRANSLATION_FIDELITY_HEADER

#include <cstdint>
#include <string>
#include <vector>

namespace SOMTParser::Uir {

enum class EvidenceKind { PENDING, BY_CONSTRUCTION, TESTED, MACHINE_CHECKED };

enum class CountStatus : std::uint8_t {
    UNASSESSED,
    PRESERVED,
    NO_GUARANTEE,
};

const char* countStatusName(CountStatus status);
const char* evidenceKindName(EvidenceKind kind);

struct CountEvidence {
    EvidenceKind kind = EvidenceKind::PENDING;
    std::string rationale;
    std::vector<std::string> references;

    bool recorded() const noexcept {
        if (kind != EvidenceKind::BY_CONSTRUCTION
            && kind != EvidenceKind::TESTED
            && kind != EvidenceKind::MACHINE_CHECKED) {
            return false;
        }
        if (rationale.empty() || references.empty()) { return false; }
        for (const std::string& reference : references) {
            if (!reference.empty()) { return true; }
        }
        return false;
    }
};

struct Fidelity {
    /** Translated formula SAT implies original SAT: a found solution is real. */
    bool sound = true;
    /** Original SAT implies translated SAT: no solution is lost, so UNSAT carries over. */
    bool complete = true;
    /** OMT only: the optimum value is preserved. */
    bool preserves_optimum = true;

    /** Count-preservation assessment. PRESERVED means every source model has
     *  exactly one target extension (and vice versa). UNASSESSED is the
     *  conservative default. NO_GUARANTEE means this translation makes no
     *  count-preservation promise; it does not itself assert a measured
     *  numerical mismatch.
     *
     *  Stronger than equisatisfiability and independent of
     *  `preserves_optimum`: optimisation asks for an extremum over the model
     *  set and counting asks for its cardinality, so an encoding can keep one
     *  and destroy the other. A one-sided (Plaisted-Greenbaum) auxiliary
     *  leaves its variable free whenever the constraint it guards holds, which
     *  multiplies the count while preserving satisfiability in both
     *  directions -- perfectly `sound`, perfectly `complete`, and useless to
     *  someone counting. */
    CountStatus count_status = CountStatus::UNASSESSED;

    bool preservesCount() const noexcept {
        return count_status == CountStatus::PRESERVED;
    }

    /** A limit outside which the conclusion does not hold. */
    struct Bound {
        /** PLAN_HORIZON is NOT a BMC depth, and the two are separate because a
         *  results table that conflated them would compare a planning bound
         *  with a model-checking one. Both count steps; they count steps of
         *  different things, and the question each answers differs -- "is there
         *  a plan of length <= k" against "is there a trace to a bad state
         *  within k". */
        enum Kind {
            BMC_DEPTH,
            BV_WIDTH,
            DOMAIN_CUT,
            HORN_UNROLL,
            PLAN_HORIZON,
            /** Maximum number of method-expansion levels in bounded HTN/HDDL. */
            DECOMPOSITION_DEPTH,
            /** Maximum grammar derivation depth in bounded syntax-guided synthesis. */
            GRAMMAR_RESTRICTION,
            /** Maximum state/gate budget for a bounded reactive strategy. */
            STRATEGY_SIZE,
        };
        Kind        kind = BV_WIDTH;
        int64_t     value = 0;
        std::string site;      // constraint or variable that introduced it
    };
    std::vector<Bound> bounds;

    /** Lattice meet: field-wise conjunction plus union of bounds. Count
     *  preservation is positive only when every component is preserved. */
    static Fidelity meet(const Fidelity& a, const Fidelity& b);

    bool isExact() const noexcept {
        return sound && complete && preserves_optimum
            && count_status == CountStatus::PRESERVED
            && bounds.empty();
    }

    /** Whether this fidelity satisfies every guarantee required by @p floor.
     * Bounds describe why a guarantee is conditional; they are retained in
     * reports but are not themselves Boolean requirements of a floor. */
    bool meets(const Fidelity& floor) const noexcept {
        return (!floor.sound || sound)
            && (!floor.complete || complete)
            && (!floor.preserves_optimum || preserves_optimum)
            && (floor.count_status != CountStatus::PRESERVED
                || count_status == CountStatus::PRESERVED);
    }

    /** Exact on the pre-count fidelity axes; count status remains UNASSESSED.
     *  Use explicit count evidence at the contract/choice site to claim
     *  PRESERVED. */
    static Fidelity exact();
    static Fidelity equisat();
    static Fidelity underApprox(Bound b);
    /** Takes no site: see the implementation for why an over-approximation
     *  carries no Bound, and EncodingChoice::site for where the site is
     *  recorded instead. A parameter this function cannot store would let a
     *  caller pass a site that silently vanishes. */
    static Fidelity overApprox();
};

} // namespace SOMTParser::Uir

#endif /* SOMTPARSER_TRANSLATION_FIDELITY_HEADER */
