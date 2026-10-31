/* -*- Source -*-
 * Fidelity lattice implementation.
 * Copyright (C) 2026 Fuqi Jia
 */

#include "somtparser/translation/fidelity.h"

#include <algorithm>
#include <tuple>

namespace SOMTParser::Uir {

const char* countStatusName(CountStatus status) {
    switch (status) {
    case CountStatus::UNASSESSED:   return "unassessed";
    case CountStatus::PRESERVED:    return "preserved";
    case CountStatus::NO_GUARANTEE: return "no_guarantee";
    }
    return "invalid";
}

const char* evidenceKindName(EvidenceKind kind) {
    switch (kind) {
    case EvidenceKind::PENDING: return "PENDING";
    case EvidenceKind::BY_CONSTRUCTION: return "BY_CONSTRUCTION";
    case EvidenceKind::TESTED: return "TESTED";
    case EvidenceKind::MACHINE_CHECKED: return "MACHINE_CHECKED";
    }
    return "INVALID";
}

Fidelity Fidelity::meet(const Fidelity& a, const Fidelity& b) {
    Fidelity r;
    r.sound             = a.sound && b.sound;
    r.complete          = a.complete && b.complete;
    r.preserves_optimum = a.preserves_optimum && b.preserves_optimum;
    if (a.count_status == CountStatus::NO_GUARANTEE
        || b.count_status == CountStatus::NO_GUARANTEE) {
        r.count_status = CountStatus::NO_GUARANTEE;
    } else if (a.count_status == CountStatus::PRESERVED
               && b.count_status == CountStatus::PRESERVED) {
        r.count_status = CountStatus::PRESERVED;
    } else {
        r.count_status = CountStatus::UNASSESSED;
    }
    r.bounds = a.bounds;
    // Union of bounds: only insert bounds from b if not already present
    for (const auto& bbound : b.bounds) {
        bool found = false;
        for (const auto& rbound : r.bounds) {
            if (rbound.kind == bbound.kind && rbound.value == bbound.value && rbound.site == bbound.site) {
                found = true;
                break;
            }
        }
        if (!found) {
            r.bounds.push_back(bbound);
        }
    }
    // Sorted, so that meet really is commutative in the one component anybody
    // can observe. The header promises commutativity; the flags were, but the
    // bound *order* was not -- meet(x-bound, s-bound) produced [x, s] and the
    // reverse produced [s, x] -- and report.cpp serialises bounds in vector
    // order, so two runs that differed only in pass order emitted different
    // JSON for the same translation.
    std::sort(r.bounds.begin(), r.bounds.end(),
              [](const Bound& x, const Bound& y) {
                  return std::tie(x.kind, x.value, x.site)
                       < std::tie(y.kind, y.value, y.site);
              });
    return r;
}

Fidelity Fidelity::exact() {
    return Fidelity{};
}

Fidelity Fidelity::equisat() {
    // Equisatisfiable, and nothing more. The name is the contract, so this
    // does NOT claim count preservation: an auxiliary variable preserves
    // satisfiability in both directions whether it is functionally determined
    // or only one-sidedly implied, and only the first preserves the count.
    //
    // Two callers, and both are the second kind. The OPB WBO threshold
    // relaxation leaves `r_i` free whenever `C_i` holds, so the count is
    // multiplied by 2^k. The XCSP3 `circuit` encoding pins its position
    // witnesses only up to a cyclic rotation, so one source model extends to
    // `actual_size` target models -- and `actual_size` varies per model, so it
    // is not even a constant factor. An encoding that IS count-preserving
    // should say so explicitly at its own site rather than inherit it here.
    Fidelity f;
    f.count_status = CountStatus::NO_GUARANTEE;
    return f;
}

Fidelity Fidelity::underApprox(Bound b) {
    Fidelity f;
    f.complete = false;
    f.preserves_optimum = false;
    // A bound can remove source models; no count-preservation promise
    // follows, even when the bounded problem still has infinite domains.
    f.count_status = CountStatus::NO_GUARANTEE;
    f.bounds.push_back(std::move(b));
    return f;
}

Fidelity Fidelity::overApprox() {
    // No Bound is attached, and that is the point. A Bound means "the
    // conclusion holds only within this limit", which is the *under*-
    // approximation direction: it is what makes a relaxed-domain SAT answer
    // trustworthy only inside the limit. An over-approximation is the mirror
    // image -- its UNSAT is globally valid, with no limit qualifying it -- so
    // a fabricated Bound here would tell the eval pipeline, which stratifies
    // on exactly this field, the opposite of what happened.
    //
    // Nothing here can therefore store a site, which is why this takes none:
    // a site parameter that the body discards would let a future caller hand
    // over the one piece of provenance it cared about and watch it disappear.
    // The site belongs on the EncodingChoice that records this fidelity
    // (EncodingChoice::site), where it is read back.
    Fidelity f;
    f.sound = false;
    f.preserves_optimum = false;
    // A relaxed domain admits models the source does not have.
    f.count_status = CountStatus::NO_GUARANTEE;
    return f;
}

} // namespace SOMTParser::Uir
