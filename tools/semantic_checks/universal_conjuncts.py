"""Sufficient full-relation certificate for conjunctions with universal clauses.

The complete quantifier-free conjunctions are first proved equivalent. For each pair of
universal clauses, an UNSAT query proves their bodies equal at arbitrary fresh
values of every bound variable, under a subset of those shared conjuncts.
Consequently the complete conjunctions are equivalent. A failed obligation is
only inconclusive; it is never reported as a counterexample to the full models.
"""
import z3
from .boolean_structure import structural_equivalence
from .full_relation_certificate import prove_complete_relation


def _conjuncts(expression):
    out, todo = [], [expression]
    while todo:
        node = todo.pop()
        if z3.is_and(node):
            todo.extend(node.children())
        elif not z3.is_true(node):
            out.append(node)
    return out


class _QuantifierFreeIndex:
    """Classify a shared expression DAG once, retaining its complete AST owners.

    This cache is local to one certificate and one context. Retaining every
    tested root is essential: instantiated universal bodies are temporary Z3
    expressions whose AST IDs could otherwise be recycled between calls.
    """
    def __init__(self, context):
        self.context = context
        self.roots = []
        self.memo = {}

    def contains_no_binder(self, expression):
        if expression.ctx != self.context:
            raise ValueError('quantifier-free classification needs one Z3 context')
        self.roots.append(expression)
        ctx = self.context.ref()
        core = z3.z3core
        pending = [(expression.as_ast(), False)]
        while pending:
            node, ready = pending.pop()
            identity = core.Z3_get_ast_id(ctx, node)
            if identity in self.memo:
                continue
            kind = core.Z3_get_ast_kind(ctx, node)
            if kind in (z3.Z3_QUANTIFIER_AST, z3.Z3_VAR_AST):
                self.memo[identity] = False
                continue
            if kind == z3.Z3_NUMERAL_AST:
                self.memo[identity] = True
                continue
            if kind != z3.Z3_APP_AST:
                self.memo[identity] = False
                continue
            app = core.Z3_to_app(ctx, node)
            children = [core.Z3_get_app_arg(ctx, app, i)
                        for i in range(core.Z3_get_app_num_args(ctx, app))]
            if not ready:
                pending.append((node, True))
                pending.extend((child, False) for child in children
                               if core.Z3_get_ast_id(ctx, child) not in self.memo)
                continue
            self.memo[identity] = all(self.memo[core.Z3_get_ast_id(ctx, child)]
                                      for child in children)
        return self.memo[expression.get_id()]


def _quantifier_free(expression):
    return _QuantifierFreeIndex(expression.ctx).contains_no_binder(expression)


def _scalar_bound(node):
    if not z3.is_app(node) or node.decl().kind() not in (
        z3.Z3_OP_LE, z3.Z3_OP_GE, z3.Z3_OP_LT, z3.Z3_OP_GT, z3.Z3_OP_EQ
    ) or node.num_args() != 2:
        return False
    a, b = node.children()
    def scalar(x):
        return (z3.is_const(x) and x.decl().kind() == z3.Z3_OP_UNINTERPRETED
                and x.sort().kind() in (z3.Z3_INT_SORT, z3.Z3_REAL_SORT))
    def numeral(x):
        return z3.is_int_value(x) or z3.is_rational_value(x)
    return (scalar(a) and numeral(b)) or (scalar(b) and numeral(a))


def _expanded_scalar_equalities(conjuncts):
    """Equality to a numeral is exactly the conjunction of its closed bounds.

    This is an identity of Int/Real order, not inference from model feasibility.
    Bool/BV equality, symbolic RHSs, coercions and arbitrary expression equality
    are unchanged. All original constraints remain represented in the proof.
    """
    out, count = [], 0
    for node in conjuncts:
        if z3.is_eq(node) and _scalar_bound(node):
            a, b = node.children()
            out.extend([a <= b, a >= b])
            count += 1
        else:
            out.append(node)
    return out, count


def _free_signature(expression):
    """Pairing heuristic only: acceptance always needs a complete UNSAT proof."""
    todo, seen, result = [expression], set(), set()
    while todo:
        node = todo.pop()
        if node.get_id() in seen:
            continue
        seen.add(node.get_id())
        if z3.is_app(node):
            if node.decl().kind() == z3.Z3_OP_UNINTERPRETED:
                result.add(node.decl().get_id())
            todo.extend(node.children())
    return frozenset(result)


def prove_universal_conjunctions(left, right):
    """Return equivalent=True only after covering every original conjunct.

    Supports top-level universal clauses with quantifier-free bodies. Exists,
    nested binders and quantifiers inside arbitrary Boolean contexts are
    explicitly inconclusive. No domain or resource bound is invented.
    """
    if left.ctx != right.ctx:
        raise ValueError('universal conjunctions need one Z3 context')
    if not z3.is_bool(left) or not z3.is_bool(right):
        raise ValueError('universal conjunctions require Boolean formulas')
    result = dict(equivalent=None, solver_queries=0, obligations=[],
                  method='equivalent complete plain conjunctions and universal-body XOR certificates',
                  all_original_conjuncts_retained=True)
    sides = []
    classification = _QuantifierFreeIndex(left.ctx)
    for expression in (left, right):
        plain, universal = [], []
        for node in _conjuncts(expression):
            if z3.is_quantifier(node):
                if not node.is_forall():
                    return dict(result, reason='non-universal top-level binder')
                sorts = [node.var_sort(i) for i in range(node.num_vars())]
                fresh = [z3.FreshConst(s, prefix='universal_probe') for s in sorts]
                body = z3.substitute_vars(node.body(), *reversed(fresh))
                if not classification.contains_no_binder(body):
                    return dict(result, reason='nested quantifier in universal body')
                universal.append(node)
            elif classification.contains_no_binder(node):
                plain.append(node)
            else:
                return dict(result, reason='quantifier outside top-level conjunction')
        sides.append((plain, universal))
    (lp, lq), (rp, rq) = sides
    result.update(left_plain_conjuncts=len(lp), right_plain_conjuncts=len(rp),
                  left_universal_conjuncts=len(lq), right_universal_conjuncts=len(rq))
    normalized_left, lc = _expanded_scalar_equalities(lp)
    normalized_right, rc = _expanded_scalar_equalities(rp)
    result['plain_scalar_equalities_expanded'] = dict(left=lc, right=rc)
    if len(lq) != len(rq):
        return dict(result, reason='unmatched universal binder count')
    def conjunction(nodes):
        return z3.And(*nodes) if nodes else z3.BoolVal(True, ctx=left.ctx)
    plain_left, plain_right = map(conjunction, (normalized_left, normalized_right))
    common = structural_equivalence(plain_left, plain_right)
    result['plain_conjunction_structural'] = common
    if not common['equivalent']:
        # Prove the entire unconditional part first. Universal clauses are
        # absent from this obligation: a body proof cannot justify its own
        # premises. A sufficient positive certificate lets either equivalent
        # plain conjunction supply original bounds to the body obligations.
        plain = prove_complete_relation(plain_left, plain_right)
        result['plain_conjunction_certificate'] = plain
        result['solver_queries'] += plain['solver_queries']
        if plain['equivalent'] is not True:
            return dict(result, reason='unproved complete plain conjunction')
    # These are original unconditional conjuncts, not guessed source domains.
    # Using a subset makes the body proof stronger while avoiding unrelated
    # model search. The entire plain conjunction is still matched above.
    context = [node for node in lp if _scalar_bound(node)]
    result['original_scalar_bound_conjuncts'] = len(context)
    # Index original unary bounds once. A body proof may use any subset of the
    # common full conjunction, so bounds on declarations absent from that body
    # are unnecessary. Omitting even an inconsistent unrelated domain only
    # strengthens the obligation; it cannot produce a false positive. This
    # avoids adding every model variable's bounds to every small body query.
    context_index = {}
    for ordinal, bound in enumerate(context):
        scalar = next(x for x in bound.children()
                      if z3.is_const(x) and x.decl().kind() == z3.Z3_OP_UNINTERPRETED)
        context_index.setdefault(scalar.decl().get_id(), []).append((ordinal, bound))
    result['body_context_strategy'] = 'original scalar bounds on free body declarations'
    # Build candidate buckets once: rewalking every remaining body for every
    # source binder is quadratic in the number of clauses. Signatures only
    # select candidates; every accepted pair still needs its complete UNSAT
    # body obligation. Ordered dictionaries preserve the original candidate
    # order and each occurrence, including duplicate binders.
    remaining = {}
    for ri, binder in enumerate(rq):
        key = (tuple(binder.var_sort(i).get_id() for i in range(binder.num_vars())),
               _free_signature(binder.body()))
        remaining.setdefault(key, {})[ri] = binder
    for li, a in enumerate(lq):
        sorts = [a.var_sort(i) for i in range(a.num_vars())]
        signature = _free_signature(a.body())
        selected = [entry for key in signature for entry in context_index.get(key, ())]
        selected.sort(key=lambda entry: entry[0])
        body_context = [bound for _, bound in selected]
        key = (tuple(sort.get_id() for sort in sorts), signature)
        candidates = remaining.get(key, {})
        proved = None
        for ri, b in candidates.items():
            values = [z3.FreshConst(s, prefix='universal_probe') for s in sorts]
            aa = z3.substitute_vars(a.body(), *reversed(values))
            bb = z3.substitute_vars(b.body(), *reversed(values))
            solver = z3.Solver(ctx=left.ctx)
            solver.add(*body_context, z3.Xor(aa, bb))
            answer = solver.check()
            record = dict(left=li, right=ri, answer=str(answer),
                          bound_variables=len(values), complete_bodies=True,
                          original_scalar_bounds_used=len(body_context))
            if answer == z3.unknown:
                record['reason_unknown'] = solver.reason_unknown()
            result['obligations'].append(record)
            result['solver_queries'] += 1
            if answer == z3.unsat:
                proved = ri
                break
        if proved is None:
            return dict(result, reason='unproved universal body correspondence')
        # Remove only the proved occurrence; identical binders are distinct
        # obligations and cannot be collapsed by AST identity.
        del candidates[proved]
    assert all(not candidates for candidates in remaining.values())
    return dict(result, equivalent=True, reason='all complete conjuncts covered')
