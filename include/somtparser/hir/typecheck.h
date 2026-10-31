/* -*- Header -*-
 *
 * HIR type checking.
 *
 * The HIR was never checked. mkOp() gives every connective and comparison the
 * Bool sort without looking at its arguments, and nothing between a frontend
 * and Parser re-derived it, so an ill-sorted model reached lowering intact and
 * came out the other side as an SMT-LIB script no solver accepts:
 *
 *     var int: x;  constraint x;       ->  (assert x)      exit 0, fidelity exact
 *     var bool: b; constraint b + 1;   ->  SIGABRT inside the Parser builders
 *
 * Neither is a defect of any one frontend. A frontend hands over an HIR model;
 * whether that model is well-sorted is a property of the model, so it is
 * checked once here rather than 22 times, once per language. translate() runs
 * this between parsing and the pass pipeline: a model that fails is reported as
 * E_TYPE against the input, which is what it is, and no pass or lowering ever
 * sees it.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#ifndef SOMTPARSER_HIR_TYPECHECK_HEADER
#define SOMTPARSER_HIR_TYPECHECK_HEADER

#include "somtparser/translation/diagnostic.h"
#include "somtparser/hir/hir.h"

namespace SOMTParser::Uir::Hir {

/** Name of a sort as it appears in diagnostics ("Bool", "Int", "Real"). */
const char* sortName(SortKind k);

/**
 * Is @p model well-sorted and internally consistent?
 *
 * Checks, in order: every declaration is unique and its bounds are numeric and
 * of its own sort; every expression's operator agrees with its arguments' sorts
 * and arity, and carries the result sort that operator actually yields; every
 * identifier resolves to a declaration with the sort it claims; every
 * constraint formula is Bool; every objective term is numeric; and objective
 * names collide with neither each other nor a declaration.
 *
 * Reports *every* violation it finds, not just the first: a batch run reads the
 * diagnostics to decide what a language's frontend still gets wrong, and
 * stopping at the first would understate that by an unknown factor.
 *
 * @return true when the model is clean. Otherwise false, having recorded at
 *         least one ERROR diagnostic in @p diagnostics.
 */
bool typeCheck(const ConstraintModel& model, Diagnostics& diagnostics);

/** A term and the source location to use when it has none of its own. */
struct LocatedExpr {
    ExprPtr expression;
    SourceLoc loc;
};

/** Check a model and additional terms without asserting those terms.
 *
 * Frontends use this for source nodes that may be unreachable from the final
 * constraints. Terms may have any sort. Successful shared-node checks can be
 * reused across batch roots in the same lexical scope. The model and all
 * expressions must remain unchanged for this synchronous call; the cache
 * never survives the call. When a term location has no file name,
 * defaultFile supplies it while preserving that term's line and column.
 * Large single-file batches can thus store the file name only once.
 */
bool typeCheckTerms(const ConstraintModel& model,
                    const std::vector<LocatedExpr>& terms,
                    Diagnostics& diagnostics,
                    const std::string& defaultFile = {});

} // namespace SOMTParser::Uir::Hir

#endif /* SOMTPARSER_HIR_TYPECHECK_HEADER */
