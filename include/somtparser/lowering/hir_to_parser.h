/* -*- Header -*-
 *
 * HirToParser — the thin lowering step.
 *
 * Runs only after the pass pipeline has eliminated every high-level feature, so
 * each HIR construct maps one-to-one onto the existing Parser builders. Any
 * construct reaching here that cannot be mapped is an internal error, not a
 * translation decision: decisions belong in passes.
 *
 * Objectives are deliberately not handled here. They are emitted as text by the
 * OMT dialect emitter, because their syntax differs per target solver while the
 * SMT body does not.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#ifndef SOMTPARSER_LOWERING_HIR_TO_PARSER_HEADER
#define SOMTPARSER_LOWERING_HIR_TO_PARSER_HEADER

#include "somtparser/frontend/parser.h"
#include "somtparser/translation/diagnostic.h"
#include "somtparser/hir/hir.h"
#include "somtparser/translation/report.h"

#include <cstddef>
#include <functional>
#include <memory>
#include <string>
#include <unordered_map>
#include <unordered_set>

namespace SOMTParser::Lower {

class HirToParser {
public:
    explicit HirToParser(ParserPtr parser) : parser_(std::move(parser)) {}

    /** Declare every variable, then assert every constraint and bound.
     *  Returns false with a diagnostic recorded on the first failure. */
    bool lower(const Uir::Hir::ConstraintModel& model,
               Uir::TranslationReport& report,
               Uir::Diagnostics& diagnostics);

    /** Lower only declarations, bounds, ordinary constraints and objectives of
     *  a packed numeric model, without copying its declaration containers.
     *  The resulting Parser is a preamble, not the complete source relation:
     *  callers must separately emit the validated packed rows. Ordinary lower()
     *  still rejects packed storage instead of silently omitting its rows.
     *  With stream_literal_bounds, callers must also emit the numeric bounds
     *  using writePackedLinearBoundsSmt2. The default preserves the complete
     *  ordinary preamble for existing direct callers. With
     *  stream_unused_declarations, numeric columns absent from ordinary HIR
     *  also require writePackedLinearDeclarationsSmt2; their names still pass
     *  through this lowerer's complete collision mapping. */
    bool lowerPackedLinearPreamble(const Uir::Hir::ConstraintModel& model,
                                    Uir::TranslationReport& report,
                                    Uir::Diagnostics& diagnostics,
                                    bool stream_literal_bounds = false,
                                    bool stream_unused_declarations = false);

    /** Lower a privately owned container, releasing each successfully lowered
     *  constraint formula and function body. Signature, soft-constraint and
     *  objective metadata remain available for contracts and OMT emission.
     *  A hard top-level conjunction releases its HIR children incrementally.
     *  If a child fails, its completed prefix is asserted and the formula is
     *  replaced by the unlowered remainder. Other failed formulas stay intact. */
    bool lowerConsuming(Uir::Hir::ConstraintModel& model,
                        Uir::TranslationReport& report,
                        Uir::Diagnostics& diagnostics);

    /** Translator-only consuming mode. In addition to successfully lowered
     *  expression roots, release declaration/constraint metadata as soon as
     *  its lowering phase has finished. Callers must have already captured
     *  any contracts that depend on the complete model. */
    bool lowerConsumingForTranslation(Uir::Hir::ConstraintModel& model,
                                      Uir::TranslationReport& report,
                                      Uir::Diagnostics& diagnostics);

    ParserPtr parser() const noexcept { return parser_; }

    /** Reuse the established symbol-hygiene mapping for compact emitters. */
    const std::string& emittedSymbolName(const std::string& name,
                                         Uir::Diagnostics& diagnostics) {
        return emitName(name, diagnostics);
    }

    const std::unordered_map<std::string, std::shared_ptr<DAGNode>>&
    varMap() const noexcept { return vars_; }

    /** Actual alpha-renamings selected during lowering; identity names are
     * absent. Semantic target metadata must use the same emitted symbols. */
    const std::unordered_map<std::string, std::string>&
    emittedNames() const noexcept { return emit_names_; }

    /** Finish a translator-owned lowering environment. The parser retains all
     *  declarations, definitions and assertions; keep variable lookups only for
     *  the supplied objectives. Afterward lowerTerm is restricted to those
     *  objectives. Name hygiene and sort state remain intact for re-emission. */
    void retainObjectiveBindings(const Uir::Hir::ConstraintModel& model);

    /**
     * Lower one expression to an engine node, after lower() has run.
     *
     * The OMT emitter needs this. It could print an IDENT and an integer
     * literal and refused everything else, which made a summed objective --
     * every OPB/WBO instance with one, and every MaxSAT cost function --
     * unemittable. Its own header comment says it "never re-implements
     * printing"; the two special cases were exactly that, and this is the
     * general form. Declarations must already exist, which is why it is a
     * method on a lowered instance and not a free function.
     */
    std::shared_ptr<DAGNode> lowerTerm(const Uir::Hir::ExprPtr& e,
                                       Uir::Diagnostics& diagnostics) {
        return lowerExpr(e, diagnostics);
    }

private:
    bool lowerImpl(const Uir::Hir::ConstraintModel& model,
                   Uir::Hir::ConstraintModel* consumed,
                   bool release_metadata,
                   Uir::TranslationReport& report,
                   Uir::Diagnostics& diagnostics,
                   bool packed_linear_preamble = false,
                   bool stream_literal_bounds = false,
                   bool stream_unused_declarations = false);
    /** Returns nullptr and records a diagnostic when @p e cannot be lowered. */
    std::shared_ptr<DAGNode> lowerExpr(const Uir::Hir::ExprPtr& e,
                                       Uir::Diagnostics& diagnostics);
    std::shared_ptr<DAGNode> lowerExprUncached(const Uir::Hir::ExprPtr& e,
                                               Uir::Diagnostics& diagnostics);
    std::shared_ptr<DAGNode> loweredOperand(const Uir::Hir::ExprPtr& e,
                                            Uir::Diagnostics& diagnostics) const;
    /** An HIR sort as one the Parser understands, with iterative child lowering. */
    std::shared_ptr<Sort> lowerSort(const Uir::Hir::Sort& s,
                                    Uir::Diagnostics& diagnostics);
    std::shared_ptr<Sort> lowerSortUncached(const Uir::Hir::Sort& s,
                                            Uir::Diagnostics& diagnostics);
    std::shared_ptr<Sort> loweredSortOperand(const Uir::Hir::Sort& s,
                                             Uir::Diagnostics& diagnostics) const;
    std::unordered_map<const Uir::Hir::Sort*, std::shared_ptr<Sort>> sort_cache_;

    /** DIV_TRUNC / MOD_TRUNC / DIV_FLOOR / MOD_FLOOR as a correction around
     *  SMT-LIB's Euclidean div and mod, which are the only ones the target
     *  language has. @p op must be one of those four. */
    std::shared_ptr<DAGNode> lowerCorrectedDivision(Uir::Hir::Op op,
                                                    const std::shared_ptr<DAGNode>& a,
                                                    const std::shared_ptr<DAGNode>& b);

    /**
     * The name to emit for an HIR symbol, renaming one SMT-LIB reserves.
     *
     * A source language is free to call a predicate `not`. TPTP's LCL problems
     * do exactly that -- `is_a_theorem(implies(not(X),X))` encodes a logic
     * calculus, where `not` is an uninterpreted function symbol and nothing
     * more -- and passing that name to `declare-fun` made the ENGINE reject it,
     * with the rejection escaping the frontend as E_INTERNAL: the bucket
     * reserved for a broken invariant, reported for a perfectly legal input.
     *
     * Renaming is safe in a way most rewrites are not: the symbols involved are
     * uninterpreted, so consistently renaming one is an alpha-conversion and
     * changes no model. What it must not do is COLLIDE, which is why the
     * replacement is checked against every identifier the model mentions --
     * `taken_names_`, seeded before the first declaration -- rather than
     * against the declarations alone.
     *
     * Almost every model leaves this map empty. Non-const because it memoises,
     * which is what makes the renaming consistent across declaration and use.
     */
    const std::string& emitName(const std::string& hir_name, Uir::Diagnostics& diagnostics);

    ParserPtr parser_;
    /** Reserved HIR name -> replacement. Identity names are not cached. */
    std::unordered_map<std::string, std::string> emit_names_;
    /** Source names that could collide with generated spellings, plus every
     *  generated replacement so far. A generated name must be in neither. */
    std::unordered_set<std::string> taken_names_;
    /** Next fresh function-parameter spelling, shared across models lowered by this instance. */
    std::size_t next_function_parameter_suffix_ = 0;
    /** Sort parameters of the parametric datatype currently being lowered.
     *  A `par`-bound name must resolve for its selectors and must not become a
     *  `declare-sort`: see the UNINTERPRETED branch of lowerSort. */
    std::unordered_set<std::string> dt_params_in_scope_;
    std::unordered_map<std::string, std::shared_ptr<DAGNode>> vars_;
    /** Quantifier-bound variables in scope, pushed and popped by lowerExpr.
     *  Kept apart from vars_ because a bound variable is not a free variable of
     *  the model and must never be found by an IDENT lookup. */
    std::unordered_map<std::string, std::shared_ptr<DAGNode>> bound_;
    struct ExprCacheKey {
        const Uir::Hir::Expr* expression;
        std::size_t scope_epoch;
        bool operator==(const ExprCacheKey& other) const noexcept {
            return expression == other.expression && scope_epoch == other.scope_epoch;
        }
    };
    struct ExprCacheHash {
        std::size_t operator()(const ExprCacheKey& key) const noexcept {
            return std::hash<const Uir::Hir::Expr*>{}(key.expression)
                ^ (std::hash<std::size_t>{}(key.scope_epoch) << 1);
        }
    };
    // Memoize ordinary operands for bottom-up lowering until the next root.
    // Scope epochs keep shared BOUND_VARs distinct across binder environments.
    std::unordered_map<ExprCacheKey, std::shared_ptr<DAGNode>, ExprCacheHash> expr_cache_;
    std::size_t lower_expr_depth_ = 0;
    std::size_t lower_scope_epoch_ = 0;
    std::size_t next_lower_scope_epoch_ = 0;
};

} // namespace SOMTParser::Lower

#endif /* SOMTPARSER_LOWERING_HIR_TO_PARSER_HEADER */
