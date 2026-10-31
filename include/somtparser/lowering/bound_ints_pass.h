/* -*- Header -*-
 *
 * BoundIntsPass — gives unbounded Int variables a finite domain.
 *
 * This is deliberately not the real int-to-bv pass: that needs a bit-vector
 * Sort in HIR, which is core surface belonging to Plan 6. This pass stays
 * within the existing Int sort and only clamps the domain, which is enough to
 * exercise the fidelity pipeline end to end without waiting on that work.
 *
 * Clamping a domain is an under-approximation, not equisat: a variable that
 * was genuinely unbounded may have had solutions outside [-(2^(w-1)),
 * 2^(w-1)-1], and those are now unreachable. A variable that already carried
 * a bound in either direction loses nothing -- this pass leaves it untouched
 * and records no choice for it, because recording one would misreport a
 * variable this pass never affected as an approximation.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#ifndef SOMTPARSER_LOWERING_BOUND_INTS_PASS_HEADER
#define SOMTPARSER_LOWERING_BOUND_INTS_PASS_HEADER

#include "somtparser/translation/pass.h"

#include <string>

namespace SOMTParser::Lower {

class BoundIntsPass : public Uir::Pass {
public:
    std::string id() const override { return "bound-ints"; }

    /** Neither a precondition nor an effect on the feature vocabulary: the
     *  variable stays Int (no BV sort exists yet to move it to), so nothing
     *  is eliminated or introduced. */
    Uir::PassTraits traits() const override {
        Uir::PassTraits t;
        // Only declaration bounds change; packed row indices and arithmetic
        // remain exact, with the ordinary bound-fidelity report still applied.
        t.preserves_packed_linear_rows = true;
        t.preserves_packed_scalar_calls = true;
        return t;
    }

    /** For every Int VarDecl with both bounds absent, sets
     *  [-(2^(w-1)), 2^(w-1)-1] where w = ctx.spec->intParam("width", 32) and
     *  records a matching under-approximation EncodingChoice. A VarDecl that
     *  already carries a bound in either direction is left untouched and gets
     *  no choice. Always returns true: there is no failure mode here that
     *  isn't already an invariant violation elsewhere. */
    bool run(Uir::Hir::ConstraintModel& model, Uir::LowerContext& ctx) override;
};

/** Registers every pass built into libsomtparser. Idempotent, so it is safe
 *  to call on every translate(): a static initializer would be dropped by the
 *  linker in a static build (see registerAllLanguages for the same reasoning
 *  on the language side), so registration must be this explicit function
 *  instead. */
void registerBuiltinPasses(Uir::PassRegistry& registry);

} // namespace SOMTParser::Lower

#endif /* SOMTPARSER_LOWERING_BOUND_INTS_PASS_HEADER */
