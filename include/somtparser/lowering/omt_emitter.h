/* -*- Header -*-
 *
 * OMT dialect emission.
 *
 * GOMT names the SMT 2025 OMT proposal, the latest syntax confirmed against
 * its authors' published specification. It is a proposal, not an adopted
 * SMT-LIB standard. Z3 and OptiMathSAT retain their vendor interfaces.
 *
 * The layer is deliberately thin: SOMTParser's existing objective commands map
 * almost one-to-one onto the proposal, down to MINMAX/MAXMIN, so a revision to
 * the proposal touches only this file.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#ifndef SOMTPARSER_LOWERING_OMT_EMITTER_HEADER
#define SOMTPARSER_LOWERING_OMT_EMITTER_HEADER

#include "somtparser/lowering/hir_to_parser.h"
#include "somtparser/translation/diagnostic.h"
#include "somtparser/hir/hir.h"

#include <string>
#include <optional>
#include <vector>

namespace SOMTParser::Lower {

enum class OmtDialect {
    SmtLib2025,   // compatibility spelling for the SMT 2025 GOMT proposal
    Z3,           // (minimize t) / (maximize t)
    OptiMathSAT,
    None,         // feasibility-only SMT; requires a floor that permits objective loss
    Gomt = SmtLib2025, // preferred proposal name; preserve the existing enum value
};

enum class RenderedObjectiveKind { Minimize, Maximize, Soft };

/** A source-ordered objective event whose term is already printed SMT-LIB.
 * Soft groups take their priority at first occurrence; later members update
 * that same cost. group/name are SMT symbol spellings, or empty for generated
 * names. already_emitted marks a legacy module's soft group: term is then
 * unused and the caller has already printed every assertion in that group. */
struct RenderedObjective {
    RenderedObjectiveKind kind = RenderedObjectiveKind::Minimize;
    std::string term;
    std::string name;
    std::string weight = "1";
    std::string group;
    bool already_emitted = false;
};

struct RenderedOmt {
    std::string preamble;
    std::string commands;
    std::string query;
    /** GOMT leaf objective symbols, in optimization order, for get-value. */
    std::vector<std::string> objective_names;
};

/** Shared native/HIR dialect writer. On success query contains check-sat or
 * optimize-sat, but never exit; callers must not append another check-sat.
 * With no goals, it supplies the ordinary check-sat query. Errors return an
 * empty result and diagnostics; no partial script may be consumed.
 * reserved_symbols prevents generated objective names capturing body symbols. */
RenderedOmt emitRenderedObjectives(
    const std::vector<RenderedObjective>& events,
    Uir::Hir::ObjectiveCombination combination,
    OmtDialect dialect,
    Uir::Diagnostics& diagnostics,
    const std::vector<std::string>& reserved_symbols = {});

/** Throws (via condAssert) on a value outside the enum. Never returns a
 *  stand-in name: the evaluation groups results by this string. */
const char* omtDialectName(OmtDialect d);

/** OMT command text for @p model's objectives, to be appended after the SMT
 *  body. Returns "" when there is nothing to emit. A caller that releases soft
 *  constraint records during consuming lowering passes their cached group count.
 *  GOMT/OptiMathSAT callers must emit a hard-only body when soft records exist:
 *  this function emits the soft assertions with collision-free objective labels.
 *  If preamble is supplied, solver options are returned separately there and
 *  must be emitted before declarations; otherwise they prefix the returned text. */
std::string emitObjectives(const Uir::Hir::ConstraintModel& model,
                           OmtDialect dialect,
                           HirToParser& lowered,
                           Uir::Diagnostics& diagnostics,
                           std::optional<std::size_t> soft_objective_count = std::nullopt,
                           std::vector<std::string>* objective_names = nullptr,
                           std::string* preamble = nullptr);

/**
 * Can every objective in @p model be rendered at all?
 *
 * Deliberately dialect-free. translate() proves emission works while it still
 * has a Diagnostics to report into, so that toSmt2() -- which returns a bare
 * string and has no error channel -- may assert instead of silently handing
 * back a model with its objectives missing. Asking emitObjectives() to do that
 * proof made it vacuous under OmtDialect::None, which returns "" before
 * rendering anything: `--dialect none` therefore validated an objective it had
 * never looked at, and the documented re-emit path (translate with None, then
 * toSmt2(Z3)) tripped that assert at runtime.
 *
 * Renderability is a property of the objective and the lowered model, not of
 * the dialect, so it is checked here for every dialect including None.
 */
bool validateObjectives(const Uir::Hir::ConstraintModel& model,
                        HirToParser& lowered,
                        Uir::Diagnostics& diagnostics);

} // namespace SOMTParser::Lower

#endif /* SOMTPARSER_LOWERING_OMT_EMITTER_HEADER */
