/* -*- Header -*-
 *
 * ParserToHir — lift a parsed SMT-LIB script back into the HIR.
 *
 * The inverse direction of HirToParser, and the piece the architecture was
 * missing. `Lang::Language` requires a frontend's product to be HIR: a frontend
 * may borrow the SMT-LIB parser internally, but it must not put DAGNode into a
 * ParseOutcome, or the encoding decisions the pass pipeline exists to centralise
 * leak back into every frontend. CHC-COMP and the SMT-LIB baseline are both
 * SMT-LIB syntax, so both need exactly this and neither could be written
 * without it.
 *
 * Two properties are load-bearing.
 *
 * **The input is a DAG, not a tree.** NodeManager hash-conses, so structurally
 * equal subterms ARE the same shared_ptr, and a naive recursive walk revisits
 * them once per path -- exponential on a formula with shared structure, which
 * is every formula a Tseitin transformation ever touched. The memo is not an
 * optimisation.
 *
 * **An unrecognised kind is refused by name, never dropped.** The HIR covers
 * less than the engine's 326 node kinds, and the gap is real. A lift that
 * silently skipped what it did not recognise would produce a smaller model that
 * type-checks, translates, and answers a different question -- which is the
 * failure this whole project is organised against. Unknown kinds produce
 * E_UNSUPPORTED_CONSTRUCT naming the kind, so a coverage gap reads as a
 * coverage gap.
 *
 * Copyright (C) 2026 Fuqi Jia
 */

#ifndef SOMTPARSER_LOWERING_PARSER_TO_HIR_HEADER
#define SOMTPARSER_LOWERING_PARSER_TO_HIR_HEADER

#include "somtparser/frontend/parser.h"
#include "somtparser/translation/diagnostic.h"
#include "somtparser/hir/hir.h"

#include <map>
#include <memory>
#include <utility>
#include <string>
#include <unordered_set>
#include <unordered_map>

namespace SOMTParser::Lower {

class ParserToHir {
public:
    explicit ParserToHir(ParserPtr parser);

    /** Every declared variable and every assertion, as HIR. Returns false and
     *  records a diagnostic on the first construct it cannot lift; the model is
     *  then incomplete and must not be used, which is why this is a bool rather
     *  than a best effort. */
    bool lift(Uir::Hir::ConstraintModel& out, Uir::Diagnostics& diagnostics);

    /** Keep acyclic define-fun bodies as HIR definitions when requested. This
     *  avoids introducing quantified axioms for executable syntax evaluators
     *  and witness renderers. Recursive equations keep their existing policy. */
    bool lift(Uir::Hir::ConstraintModel& out, Uir::Diagnostics& diagnostics,
              bool retain_nonrecursive_definitions);

    /** One term. Public because a frontend that reads the script itself -- CHC
     *  walks the clause structure before lifting the parts -- needs to lift
     *  subterms without going through the whole script. */
    Uir::Hir::ExprPtr liftExpr(const std::shared_ptr<DAGNode>& n,
                               Uir::Diagnostics& diagnostics);

    /** An engine Sort as an HIR one. Returns a Bool sort and records a
     *  diagnostic for a sort the HIR has no counterpart for, rather than
     *  guessing -- a wrong sort survives type-checking and changes the
     *  question. */
    bool liftSort(const std::shared_ptr<Sort>& s, Uir::Hir::Sort& out,
                  Uir::Diagnostics& diagnostics);

private:
    std::string freshBoundName(const std::string& source, bool parameter = false);
    Uir::Hir::ExprPtr liftExprUncached(const std::shared_ptr<DAGNode>& n,
                                       Uir::Diagnostics& diagnostics);
    Uir::Hir::ExprPtr liftConst(const std::shared_ptr<DAGNode>& n,
                                Uir::Diagnostics& diagnostics);
    /** Lift an overloaded SMT-LIB numeral using the sort its parent resolved.
     *  Bare numerals carry the engine's IntOrReal sort; the HIR deliberately
     *  has no ambiguous sort, so the context must choose Int or Real here. */
    Uir::Hir::ExprPtr liftNumericChild(const std::shared_ptr<DAGNode>& n,
                                      const Uir::Hir::Sort* expected,
                                      Uir::Diagnostics& diagnostics);
    Uir::Hir::ExprPtr liftQuantifier(const std::shared_ptr<DAGNode>& n,
                                     Uir::Diagnostics& diagnostics);
    Uir::Hir::ExprPtr liftLet(const std::shared_ptr<DAGNode>& n,
                              Uir::Diagnostics& diagnostics);
    /** Apply @p op to @p args, expanding SMT-LIB's `:chainable` and
     *  `:right-assoc` argument lists, which the HIR's binary operators do not
     *  carry. `(= a b c)` and `(=> a b c)` are legal scripts. */
    Uir::Hir::ExprPtr mkNary(Uir::Hir::Op op, std::vector<Uir::Hir::ExprPtr> args,
                             Uir::Diagnostics& diagnostics);
    /** Is @p name a constructor, selector or tester a datatype declaration
     *  brought with it? Those are carried by the DatatypeDecl, and declaring
     *  them again beside it makes the emitted script a redeclaration. */
    bool isDatatypeMember(const std::string& name) const;

    /** Constructor, selector and tester names from every datatype lifted. */
    std::unordered_set<std::string> datatype_members_;

    ParserPtr parser_;
    /** Keyed by the node pointer AND the scope it was lifted in.
     *
     *  The pointer alone is not enough. Hash-consing can make the `x` of an
     *  outer `forall ((x Int))` and of an inner `forall ((x (_ BitVec 8)))` the
     *  same node, so a memo keyed by pointer returns the outer lift inside the
     *  inner scope -- and the model then applies a predicate to an argument of
     *  the wrong sort. The scope id changes on every push and pop, so sharing
     *  is reused within a scope and re-lifted across one.
     *
     *  The pointer is stable because the parser owns the nodes for the lift's
     *  lifetime. */
    std::map<std::pair<const DAGNode*, unsigned>, Uir::Hir::ExprPtr> memo_;
    /** Let values captured before entering the body. A reference to a binding
     *  must keep this value even when a later quantifier shadows a name in its
     *  right-hand side. Entries are restored on leaving each let scope. */
    std::unordered_map<const DAGNode*, Uir::Hir::ExprPtr> let_values_;
    /** Bumped on entering and leaving every binder scope. */
    unsigned scope_id_ = 0;
    /** Quantifier-bound names in scope: the SOURCE name to the name the HIR
     *  uses and the binder's sort.
     *
     *  The two names differ when the script shadows. SMT-LIB permits
     *  `(forall ((x Int)) ... (forall ((x (_ BitVec 8))) ...))`; the HIR does
     *  not -- Uir::Hir::typeCheck rejects a quantifier that binds a name
     *  already in scope -- so an inner binder is alpha-renamed on the way in.
     *  Renaming is the only lossless option: refusing would turn a legal script
     *  into an unsupported one, and lifting it unchanged would produce a model
     *  the checker rejects. */
    struct Binding { std::string hir_name; Uir::Hir::Sort sort; };
    std::unordered_map<std::string, Binding> bound_;
    /** Canonical global/generated names and currently active HIR binders.
     *  Fresh names must not capture a global or another renamed binder. */
    std::unordered_set<std::string> reserved_names_;
    std::unordered_set<std::string> active_bound_names_;
    /** Counter for minted binder names, so a renamed binder is reproducible
     *  within one lift rather than depending on allocation order. */
    unsigned rename_seq_ = 0;
};

} // namespace SOMTParser::Lower

#endif /* SOMTPARSER_LOWERING_PARSER_TO_HIR_HEADER */
