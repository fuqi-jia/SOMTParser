/* -*- Header -*-
 *
 * DecomposeGlobalsPass — cluster A's shared decomposition, and the pass that
 * gives EncodingProfile::style() something to mean.
 *
 * A global constraint has no single SMT encoding; it has several, and which is
 * better is an empirical question rather than a design one. This pass is where
 * that question becomes measurable:
 *
 *     alldifferent(a, lo, hi)
 *       GROUND      distinct(select(a,lo), ..., select(a,hi-1))
 *       QUANTIFIED  forall i,j. lo<=i<j<hi -> select(a,i) != select(a,j)
 *
 * Both are Fidelity::exact() -- the models are the same -- so the fidelity
 * floor cannot separate them and only an experiment can. CP and SAT toolchains
 * emit ground encodings because their targets cannot do better; an SMT solver
 * takes either. See docs/hir-design-decisions-2026-08-12.md §3.2.
 *
 * The two are not interchangeable in one respect, and it is a real asymmetry
 * rather than an implementation limit: **ground expansion needs the index range
 * to be a constant**, because it has to enumerate it. The quantified form does
 * not. A model whose bounds are variables can therefore be translated under
 * `quantified` and not under `ground`, and the pass reports that as
 * E_UNSUPPORTED_CONSTRUCT rather than silently guessing a range.
 *
 * `circuit(start, successor1, ..., successorN)` describes a single Hamiltonian
 * cycle on consecutive Int labels starting at a constant `start`, without
 * self loops. The empty list holds; the singleton list is false. A local
 * existential rank array excludes disconnected cycles and preserves Boolean
 * polarity. No free auxiliary symbols are added. This encoding is shared by
 * every frontend constructing this HIR global, under either encoding style.
 *
 * `cumulative(capacity, start, duration, demand, ...)` requires Int arguments
 * and nonnegative capacity, durations and demands. It bounds load on half-open
 * intervals [start,start+duration) at every integer time, including negative
 * start times. Checking every task start is exact and introduces no horizon.
 * Empty task lists require capacity >= 0. Source frontends with a different
 * empty-list convention must elaborate that case explicitly.
 *
 * `count_value(length, sought, terms...)` yields Int and lowers to a sum of
 * equality indicators. It is a value, so uses in objectives and nested
 * arithmetic do not require free auxiliary symbols or extra assertions.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#ifndef SOMTPARSER_LOWERING_DECOMPOSE_GLOBALS_PASS_HEADER
#define SOMTPARSER_LOWERING_DECOMPOSE_GLOBALS_PASS_HEADER

#include "somtparser/translation/pass.h"

namespace SOMTParser::Lower {

class DecomposeGlobalsPass : public Uir::Pass {
public:
    std::string id() const override { return "decompose-globals"; }

    Uir::PassTraits traits() const override {
        Uir::PassTraits t;
        t.eliminates = {Uir::feat::globalConstraint()};
        // The quantified encoding introduces quantifiers the input did not
        // have. Declaring it is what lets PassManager::validate notice a
        // profile that puts this pass before something requiring them absent --
        // and it is honest even under GROUND, where none are introduced,
        // because traits() describes the pass rather than one run of it.
        t.introduces = {Uir::feat::quantifier()};
        t.reads_encoding_style = true;
        // The pass rewrites only ordinary Constraint::formula roots. It neither
        // inspects nor mutates the compact range/clause storage.
        t.preserves_packed_clauses = true;
        t.preserves_packed_linear_rows = true;
        t.preserves_packed_scalar_calls = true;
        return t;
    }

    bool run(Uir::Hir::ConstraintModel& model, Uir::LowerContext& ctx) override;
};

/** Registers this pass and bound-ints. Idempotent. */
void registerDecompositionPasses(Uir::PassRegistry& registry);

} // namespace SOMTParser::Lower

#endif /* SOMTPARSER_LOWERING_DECOMPOSE_GLOBALS_PASS_HEADER */
