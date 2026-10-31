/* -*- Source -*-
 * BoundIntsPass and registerBuiltinPasses.
 * Copyright (C) 2026 Fuqi Jia
 */

#include "somtparser/lowering/bound_ints_pass.h"
#include "somtparser/lowering/decompose_globals_pass.h"

#include <limits>
#include <memory>
#include <string>

namespace SOMTParser::Lower {

using Uir::EncodingChoice;
using Uir::Fidelity;
using Uir::Hir::ConstraintModel;
using Uir::Hir::SortKind;
using Uir::LowerContext;
using Uir::PassRegistry;

bool BoundIntsPass::run(ConstraintModel& model, LowerContext& ctx) {
    const long long w = ctx.spec->intParam("width", 32);

    // A width outside this range is not a domain this pass can express, and
    // `1LL << (w - 1)` is undefined behaviour for every value outside it. The
    // measured results were not merely wrong but plausible-looking: width 65
    // pinned every integer to the two values [-1, 0], width 96 produced a
    // 32-bit range, and widths 0 and 128 produced the full int64 range -- each
    // while recording the *requested* width as the Bound, so the experiment
    // data would have said "under-approximated to 96 bits" about a variable
    // restricted to 32.
    if (w < 1 || w > 64) {
        ctx.diagnostics->error(Uir::ErrorCode::E_PASS_PIPELINE,
                               "bound-ints: width " + std::to_string(w)
                                   + " is out of range; it must be between 1 and 64");
        return false;
    }

    long long lo = 0;
    long long hi = 0;
    if (w == 64) {
        // 1LL << 63 overflows a signed 64-bit integer, so the general form
        // below cannot compute this case; it is also exactly "no bound at all".
        lo = std::numeric_limits<long long>::min();
        hi = std::numeric_limits<long long>::max();
    } else {
        const long long half = 1LL << (w - 1);
        lo = -half;
        hi = half - 1;
    }

    for (auto& d : model.decls) {
        if (d.sort.kind != SortKind::INT) {
            continue;                     // Bool and Real are not this pass's business
        }
        if (d.lower_bound || d.upper_bound) {
            // Already bounded in at least one direction: this pass changes
            // nothing about it, so it must not record a choice either -- that
            // would put a false under-approximation into the experiment data
            // for a variable that lost nothing.
            continue;
        }

        d.lower_bound = Uir::Hir::mkInt(lo);
        d.upper_bound = Uir::Hir::mkInt(hi);

        EncodingChoice c;
        c.site       = d.name;
        c.unified_op = "int-var";
        c.strategy   = "bound-ints";
        c.fidelity   = Fidelity::underApprox({Fidelity::Bound::BV_WIDTH, w, d.name});
        ctx.report->addChoice(c);
    }
    return true;
}

void registerBuiltinPasses(PassRegistry& registry) {
    if (registry.get("bound-ints") == nullptr) {
        registry.add(std::make_shared<BoundIntsPass>());
    }
    registerDecompositionPasses(registry);
}

} // namespace SOMTParser::Lower
