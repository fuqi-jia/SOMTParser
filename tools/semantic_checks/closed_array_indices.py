"""Normalize closed Int indices without simplifying unrelated formula terms."""
from dataclasses import dataclass

from .finite_quantifiers import _closed_int_index


@dataclass(frozen=True)
class ClosedArrayIndexNormalization:
    formula: object
    rewritten_index_positions: int


def _may_have_closed_arithmetic_index(formula):
    """Conservatively detect any index the exact evaluator could rewrite.

    The common scalar-reference and numeral-indexed-array cases need no term
    updates. Walk their complete DAG through native AST handles without
    constructing Python expressions for every child twice. The original root
    stays alive throughout this read-only walk and owns every reachable AST;
    IDs and borrowed handles are confined to this call and its one context.

    Only a supported arithmetic application can change in _closed_int_index.
    Finding one is sufficient to fall back to the existing exact rewriter;
    symbolic arithmetic and zero divisors are deliberately not ruled out here.
    Quantifier bodies are traversed without opening their binders. Patterns
    are left alone, exactly as in the original normalizer.
    """
    import z3

    arithmetic = {z3.Z3_OP_ADD, z3.Z3_OP_SUB, z3.Z3_OP_MUL, z3.Z3_OP_UMINUS,
                  z3.Z3_OP_IDIV, z3.Z3_OP_MOD, z3.Z3_OP_REM}
    context = formula.ctx_ref()
    pending = [formula.as_ast()]
    seen = set()
    index_candidates = {}
    while pending:
        ast = pending.pop()
        key = z3.Z3_get_ast_id(context, ast)
        if key in seen:
            continue
        seen.add(key)
        kind = z3.Z3_get_ast_kind(context, ast)
        if kind == z3.Z3_QUANTIFIER_AST:
            pending.append(z3.Z3_get_quantifier_body(context, ast))
        elif kind == z3.Z3_APP_AST:
            app = z3.Z3_to_app(context, ast)
            arity = z3.Z3_get_app_num_args(context, app)
            if not arity:
                continue
            children = [z3.Z3_get_app_arg(context, app, i) for i in range(arity)]
            operation = z3.Z3_get_decl_kind(context, z3.Z3_get_app_decl(context, app))
            if operation == z3.Z3_OP_SELECT:
                indices = children[1:]
            elif operation == z3.Z3_OP_STORE:
                indices = children[1:-1]
            else:
                indices = ()
            for index in indices:
                index_id = z3.Z3_get_ast_id(context, index)
                if index_id not in index_candidates:
                    possible = False
                    if z3.Z3_get_ast_kind(context, index) == z3.Z3_APP_AST:
                        index_app = z3.Z3_to_app(context, index)
                        declaration = z3.Z3_get_app_decl(context, index_app)
                        possible = z3.Z3_get_decl_kind(context, declaration) in arithmetic
                    index_candidates[index_id] = possible
                if index_candidates[index_id]:
                    return True
            pending.extend(children)
    return False


def normalize_closed_int_array_indices(formula):
    """Replace provably closed arithmetic select/store indices by numerals.

    Macro expansion can produce ``Select(a, 1 + 17)`` outside any quantifier.
    Z3's exact Int arithmetic evaluator is shared with finite instantiation;
    variables, uninterpreted applications, division by zero and non-numeral
    results stay unchanged. Only index positions are normalized: an identical
    arithmetic term elsewhere in the DAG is not globally substituted.

    This iterative DAG walk retains source ASTs in its memo. Native term
    updates preserve quantifier declarations, de Bruijn indices and annotations
    while replacing its body; no binder is opened or recreated by name.
    """
    import z3

    if not _may_have_closed_arithmetic_index(formula):
        return ClosedArrayIndexNormalization(formula, 0)

    memo, index_cache = {}, {}
    pending = [(formula, False)]
    rewritten = 0
    while pending:
        expression, ready = pending.pop()
        key = expression.get_id()
        if key in memo:
            continue
        if z3.is_quantifier(expression):
            old_children = [expression.body()]
        elif z3.is_app(expression):
            old_children = expression.children()
        else:
            memo[key] = (expression, expression)
            continue
        if not ready and old_children:
            pending.append((expression, True))
            pending.extend((child, False) for child in old_children)
            continue
        children = [memo[child.get_id()][1] for child in old_children]
        if z3.is_select(expression):
            indices = range(1, len(children))
        elif z3.is_store(expression):
            indices = range(1, len(children) - 1)
        else:
            indices = ()
        for position in indices:
            index = children[position]
            normalized = _closed_int_index(z3, index, index_cache)
            if not normalized.eq(index):
                children[position] = normalized
                rewritten += 1
        result = expression
        if any(not before.eq(after) for before, after in zip(old_children, children)):
            # Z3_update_term accepts the original arity for applications and
            # exactly one body for quantifiers (z3_api.h's modifier contract).
            arguments = (z3.Ast * len(children))(*[child.as_ast() for child in children])
            result = z3.z3._to_expr_ref(z3.Z3_update_term(
                expression.ctx_ref(), expression.as_ast(), len(children), arguments), expression.ctx)
        memo[key] = (expression, result)
    return ClosedArrayIndexNormalization(memo[formula.get_id()][1], rewritten)
