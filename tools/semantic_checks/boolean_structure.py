"""Sufficient structural proof for Boolean formulas, including quantifiers.

This does not decide satisfiability. Both complete formulas are hash-consed in
one table using exact tuple equality (not digest equality). Bound variables
keep their de Bruijn indices; free symbols keep their Z3 declaration identity.
The rewrites are alpha-renaming, Boolean AND/OR associativity,
commutativity, idempotence and identities, double-negation elimination,
symmetry of equality, permutation of all DISTINCT operands,
commutativity of exact Int/Real addition, and
reversal of exact Int/Real comparisons (a >= b iff b <= a).
Arithmetic duplicates are retained; addition is not Boolean idempotence.
Failure to match is inconclusive and must never be reported as inequivalence.
"""
import z3


def structural_equivalence(left, right):
    if left.ctx != right.ctx:
        raise ValueError("structural comparison needs one Z3 context")
    if not z3.is_bool(left) or not z3.is_bool(right):
        raise ValueError("structural comparison requires Boolean formulas")
    interned, records, memo = {}, [], {}

    def intern(record):
        found = interned.get(record)
        if found is None:
            found = len(records)
            interned[record] = found
            records.append(record)
        return found

    false, true = intern(('bool', False)), intern(('bool', True))

    # Both complete roots own all raw AST pointers below. The memo is local
    # to their common context; no pointer or AST identity survives this call.
    context = left.ctx_ref()
    core = z3.z3core

    def sort_id(node):
        return core.Z3_get_sort_id(context, core.Z3_get_sort(context, node))

    def sort_kind(node):
        return core.Z3_get_sort_kind(context, core.Z3_get_sort(context, node))

    def canonical(root):
        # Materialize child pointers and operator metadata only on the first
        # postorder visit, rather than wrapping every child twice as ExprRef.
        pending = [(root.as_ast(), None)]
        while pending:
            node, ready = pending.pop()
            key = core.Z3_get_ast_id(context, node)
            if key in memo:
                continue
            if ready is None:
                ast_kind = core.Z3_get_ast_kind(context, node)
                if ast_kind == z3.Z3_VAR_AST:
                    memo[key] = intern(('bound', core.Z3_get_index_value(context, node),
                                        sort_id(node)))
                    continue
                quantified = ast_kind == z3.Z3_QUANTIFIER_AST
                if quantified:
                    if core.Z3_is_lambda(context, node):
                        raise ValueError("lambda is outside Boolean circuit structure")
                    children = [core.Z3_get_quantifier_body(context, node)]
                    quantifier = ('forall' if core.Z3_is_quantifier_forall(context, node)
                                  else 'exists',
                                  tuple(core.Z3_get_sort_id(context,
                                            core.Z3_get_quantifier_bound_sort(context, node, i))
                                        for i in range(core.Z3_get_quantifier_num_bound(context, node))))
                    kind, declaration, arithmetic = None, None, False
                else:
                    app = core.Z3_to_app(context, node)
                    children = [core.Z3_get_app_arg(context, app, i)
                                for i in range(core.Z3_get_app_num_args(context, app))]
                    decl = core.Z3_get_app_decl(context, app)
                    kind = core.Z3_get_decl_kind(context, decl)
                    declaration = core.Z3_get_func_decl_id(context, decl)
                    quantifier = None
                    if kind in (z3.Z3_OP_LE, z3.Z3_OP_GE, z3.Z3_OP_LT, z3.Z3_OP_GT):
                        arithmetic = len(children) == 2 and all(
                            sort_kind(child) in (z3.Z3_INT_SORT, z3.Z3_REAL_SORT)
                            for child in children)
                    else:
                        arithmetic = (kind == z3.Z3_OP_ADD and sort_kind(node)
                                      in (z3.Z3_INT_SORT, z3.Z3_REAL_SORT))
                child_ids = tuple(core.Z3_get_ast_id(context, child) for child in children)
                pending.append((node, (kind, declaration, arithmetic, quantifier, child_ids)))
                pending.extend((child, None) for child, identity in zip(children, child_ids)
                               if identity not in memo)
                continue
            kind, declaration, arithmetic, quantifier, child_ids = ready
            args = tuple(memo[identity] for identity in child_ids)
            if quantifier is not None:
                # Names/triggers do not affect meaning. Preserve binder kind,
                # order, count and exact sort identities, as before.
                result = intern((*quantifier, args[0]))
            elif kind == z3.Z3_OP_TRUE:
                result = true
            elif kind == z3.Z3_OP_FALSE:
                result = false
            elif kind in (z3.Z3_OP_AND, z3.Z3_OP_OR):
                op = 'and' if kind == z3.Z3_OP_AND else 'or'
                identity, absorbing = (true, false) if op == 'and' else (false, true)
                flat = set()
                for child in args:
                    record = records[child]
                    flat.update(record[1] if record[0] == op else (child,))
                flat.discard(identity)
                if absorbing in flat:
                    result = absorbing
                elif not flat:
                    result = identity
                elif len(flat) == 1:
                    result = next(iter(flat))
                else:
                    result = intern((op, tuple(sorted(flat))))
            elif kind == z3.Z3_OP_NOT:
                child = args[0]
                record = records[child]
                if child in (true, false):
                    result = false if child == true else true
                elif record[0] == 'not':
                    result = record[1]
                else:
                    result = intern(('not', child))
            else:
                if (kind in (z3.Z3_OP_LE, z3.Z3_OP_GE, z3.Z3_OP_LT, z3.Z3_OP_GT)
                        and arithmetic):
                    if kind in (z3.Z3_OP_GE, z3.Z3_OP_GT):
                        args = args[::-1]
                    op = 'le' if kind in (z3.Z3_OP_LE, z3.Z3_OP_GE) else 'lt'
                    memo[key] = intern(('arithmetic-order', op, args))
                    continue
                # Keep arithmetic and DISTINCT multiplicities. Other function
                # declarations and argument orders are exact, with no new law.
                if (kind == z3.Z3_OP_DISTINCT
                        or kind == z3.Z3_OP_EQ and len(args) == 2
                        or kind == z3.Z3_OP_ADD and arithmetic):
                    args = tuple(sorted(args))
                result = intern(('app', declaration, args))
            memo[key] = result
        return memo[root.get_id()]

    a, b = canonical(left), canonical(right)
    return {'equivalent': a == b, 'visited_nodes': len(memo),
            'canonical_nodes': len(records),
            'method': 'alpha-aware Boolean DAG correspondence'}
