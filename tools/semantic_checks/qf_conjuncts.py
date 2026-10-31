"""Sufficient equivalence certificate for complete quantifier-free conjunctions.

Write each input as C and its remaining conjunct groups, where C consists only
of syntactically identical original conjuncts. For every group, prove equality
under a subset of C, plus unary groups already proved equivalent. Induction
over the accepted groups therefore retains equivalence of both accumulated
conjunctions. All groups must pass, including groups absent on one side.
Conjoining these implications proves the original complete formulas equivalent.
SAT/unknown for a local obligation is only inconclusive for the full formulas.
"""
import z3
from z3 import z3core

from ._integer_compat import bit_count
from .boolean_structure import structural_equivalence
from .renamed_unsat_cache import RenamedUnsatCache


def _signatures(roots):
    """Exact free declarations for the requested roots in one retained DAG.

    Internal nodes use compact ordinal sets. Broad, sufficiently dense sets
    use bit masks; sparse sets remain sparse even in million-variable models.
    Only requested roots materialize declaration-ID frozensets. Neither the
    grouping keys nor any proof obligation changes.
    """
    roots = tuple(roots)  # Own every AST until the raw-pointer traversal ends.
    if not roots:
        return {}
    if any(root.ctx != roots[0].ctx for root in roots):
        raise ValueError('declaration signatures need one Z3 context')
    context = roots[0].ctx_ref()
    # A top-level universal already makes a QF certificate inapplicable. Do
    # not scan all earlier large conjunct DAGs before noticing that binder.
    if any(z3core.Z3_get_ast_kind(context, root.as_ast())
           in (z3.Z3_QUANTIFIER_AST, z3.Z3_VAR_AST) for root in roots):
        return None
    memo, ordinals, declarations = {}, {}, []
    empty = frozenset()

    def members(value):
        if isinstance(value, frozenset):
            yield from value
        else:
            while value:
                bit = value & -value
                yield bit.bit_length() - 1
                value ^= bit

    def mask(values):
        # Filling bytes avoids repeated growing-bigint copies for wide sums.
        data = bytearray((max(values) + 8) // 8)
        for value in values:
            data[value >> 3] |= 1 << (value & 7)
        return int.from_bytes(data, 'little')

    def combine(values):
        nonempty = [value for value in values if value]
        if not nonempty:
            return empty
        if len(nonempty) == 1:
            return nonempty[0]
        dense, sparse = 0, set()
        for value in nonempty:
            if isinstance(value, int):
                dense |= value
            else:
                sparse.update(value)
        if not sparse:
            return dense
        width = max(dense.bit_length(), max(sparse) + 1)
        count_bound = bit_count(dense) + len(sparse)
        # A high ordinal alone must not allocate a huge mostly empty bitmask.
        if count_bound >= 64 and width <= 128 * count_bound:
            return dense | mask(sparse)
        sparse.update(members(dense))
        return frozenset(sparse)

    for root in roots:
        todo = [(root.as_ast(), False)]
        while todo:
            node, ready = todo.pop()
            key = z3core.Z3_get_ast_id(context, node)
            if key in memo:
                continue
            kind = z3core.Z3_get_ast_kind(context, node)
            if kind in (z3.Z3_QUANTIFIER_AST, z3.Z3_VAR_AST):
                return None
            if kind != z3.Z3_APP_AST:
                memo[key] = empty
                continue
            app = z3core.Z3_to_app(context, node)
            children = [z3core.Z3_get_app_arg(context, app, index)
                        for index in range(z3core.Z3_get_app_num_args(context, app))]
            if not ready:
                todo.append((node, True))
                todo.extend((child, False) for child in children
                            if z3core.Z3_get_ast_id(context, child) not in memo)
                continue
            values = [memo[z3core.Z3_get_ast_id(context, child)] for child in children]
            decl = z3core.Z3_get_app_decl(context, app)
            if z3core.Z3_get_decl_kind(context, decl) == z3.Z3_OP_UNINTERPRETED:
                identity = z3core.Z3_get_func_decl_id(context, decl)
                if identity not in ordinals:
                    ordinals[identity] = len(declarations)
                    declarations.append(identity)
                values.append(frozenset((ordinals[identity],)))
            memo[key] = combine(values)
    return {root.get_id(): frozenset(declarations[index]
                                    for index in members(memo[root.get_id()]))
            for root in roots}


def _conjuncts(root):
    result, todo = [], [root]
    while todo:
        node = todo.pop()
        if z3.is_and(node):
            todo.extend(node.children())
        elif z3.is_not(node) and z3.is_or(node.arg(0)):
            # De Morgan exposes conjuncts hidden by a packed negated OR. This
            # visits each disjunct once, without distributing any other OR or
            # growing a Cartesian product. Not(Or()) contributes true.
            todo.extend(z3.Not(child) for child in node.arg(0).children())
        elif not z3.is_true(node):
            result.append(node)
    return result


def _unary_numeric_bound(node):
    if node.decl().kind() not in (
        z3.Z3_OP_LE, z3.Z3_OP_GE, z3.Z3_OP_LT, z3.Z3_OP_GT, z3.Z3_OP_EQ
    ) or node.num_args() != 2:
        return False
    def scalar(value):
        return (z3.is_const(value)
                and value.decl().kind() == z3.Z3_OP_UNINTERPRETED
                and value.sort().kind() in (z3.Z3_INT_SORT, z3.Z3_REAL_SORT))
    def numeral(value):
        return z3.is_int_value(value) or z3.is_rational_value(value)
    a, b = node.children()
    return ((scalar(a) and numeral(b)) or (scalar(b) and numeral(a)))


def prove_qf_conjunctions(left, right, *, progress_callback=None):
    """Cover every conjunct or return inconclusive; never assert guessed bounds.

    Grouping by exact free declarations is a scheduling heuristic, not a proof.
    A group can be accepted only by an exact structural certificate or UNSAT.
    Quantifiers (including lambdas) and loose bound variables are unsupported.
    The optional progress callback observes sparse phase/group counters; its
    return value is ignored. UNSAT reuse compares each complete context and XOR
    under a sort-preserving bijection, never just its grouped conclusions.
    """
    if left.ctx != right.ctx:
        raise ValueError('conjunction comparison needs one Z3 context')
    if not z3.is_bool(left) or not z3.is_bool(right):
        raise ValueError('conjunction comparison requires Boolean formulas')
    result = dict(equivalent=None, solver_queries=0, unsat_reuses=0, obligations=[],
                  method='complete QF conjunction groups under shared original bounds',
                  all_original_conjuncts_retained=True)
    def phase(label, **details):
        if progress_callback is not None:
            progress_callback(dict(phase=label, solver_queries=result['solver_queries'],
                                   unsat_reuses=result['unsat_reuses'], **details))
    phase('qf-conjunct-extraction')
    # Hold the normalized nodes while indexing their actual AST identities:
    # negated-OR splitting can create Not nodes absent from the original DAG.
    lp, rp = _conjuncts(left), _conjuncts(right)
    phase('qf-signatures', left_conjuncts=len(lp), right_conjuncts=len(rp))
    signatures = _signatures((*lp, *rp))
    if signatures is None:
        return dict(result, reason='quantifier or loose bound variable')
    phase('qf-grouping')
    # AND is idempotent. AST identities are compared in the same Z3 context.
    lu = {node.get_id(): node for node in lp}
    ru = {node.get_id(): node for node in rp}
    common = lu.keys() & ru.keys()
    result.update(left_conjuncts=len(lp), right_conjuncts=len(rp),
                  left_unique_conjuncts=len(lu), right_unique_conjuncts=len(ru),
                  shared_original_conjuncts=len(common))
    bounds = {}
    for key in common:
        node = lu[key]
        if _unary_numeric_bound(node):
            signature = signatures[key]
            assert len(signature) == 1
            bounds.setdefault(next(iter(signature)), []).append(node)
    groups = []
    for unique in (lu, ru):
        side = {}
        for key, node in unique.items():
            if key not in common:
                side.setdefault(signatures[key], []).append(node)
        groups.append(side)
    lg, rg = groups
    keys = sorted(lg.keys() | rg.keys(), key=lambda key: (len(key), tuple(sorted(key))))
    result['groups'] = len(keys)
    result['original_bound_conjuncts'] = sum(map(len, bounds.values()))
    def conjunction(nodes):
        return z3.And(*nodes) if nodes else z3.BoolVal(True, ctx=left.ctx)
    shared_index = {}
    for identity in common:
        for declaration in signatures[identity]:
            shared_index.setdefault(declaration, set()).add(identity)
    proved_unary = {}
    result['proved_unary_context_groups'] = 0
    unsat_cache = RenamedUnsatCache(left.ctx)
    phase('qf-groups-ready', groups=len(keys))
    for group_index, key in enumerate(keys, 1):
        report_progress = group_index == 1 or group_index % 100 == 0 or group_index == len(keys)
        if report_progress:
            phase('qf-group-start', group=group_index, groups=len(keys), declarations=len(key))
        la, ra = lg.get(key, []), rg.get(key, [])
        a, b = conjunction(la), conjunction(ra)
        record = dict(declarations=sorted(key), left_conjuncts=len(la),
                      right_conjuncts=len(ra))
        if structural_equivalence(a, b)['equivalent']:
            record['answer'] = 'structural'
        else:
            # Shared equations such as y = table(x) are as much original
            # context as bounds. Limit to clauses over this group's symbols;
            # excluding other clauses strengthens the sufficient obligation.
            candidates = {identity for declaration in key
                          for identity in shared_index.get(declaration, ())}
            shared = {identity: lu[identity] for identity in candidates
                      if signatures[identity].issubset(key)}
            established = {node.get_id(): node for declaration in key
                           for node in proved_unary.get(declaration, [])}
            context = list((shared | established).values())
            record.update(shared_context_conjuncts=len(shared),
                          certified_unary_context_conjuncts=len(established))
            # Cache the entire sufficient obligation, including every selected
            # original/shared clause and every already-certified unary clause.
            # Matching just Xor(a, b) would be unsound when domains differ.
            obligation = z3.And(*context, z3.Xor(a, b))
            candidate = unsat_cache.prepare(obligation,
                (len(shared), len(established), len(la), len(ra)))
            reused = unsat_cache.lookup(candidate)
            if reused is not None:
                answer = z3.unsat
                result['unsat_reuses'] += 1
            else:
                if report_progress:
                    phase('qf-solver-check', group=group_index, groups=len(keys))
                solver = z3.Solver(ctx=left.ctx)
                solver.add(obligation)
                answer = solver.check()
                result['solver_queries'] += 1
                if answer == z3.unsat:
                    unsat_cache.remember_unsat(candidate, result['solver_queries'])
            record.update(answer=str(answer), original_context_conjuncts=len(context),
                          solver_executed=reused is None, unsat_reuse=reused)
            if answer == z3.unknown:
                record['reason_unknown'] = solver.reason_unknown()
            if answer != z3.unsat:
                result['obligations'].append(record)
                phase('qf-inconclusive', group=group_index, groups=len(keys), answer=str(answer))
                return dict(result, reason='unproved local group; full relation undecided')
        result['obligations'].append(record)
        if report_progress:
            phase('qf-group-complete', group=group_index, groups=len(keys), answer=record['answer'])
        if len(key) == 1:
            # Only AFTER this group's complete equivalence is established may
            # either side's original unary clauses constrain later obligations.
            # They occur in the full conjunctions; nothing is assumed from an
            # unproved candidate group or from solver models.
            proved_unary[next(iter(key))] = la + ra
            result['proved_unary_context_groups'] += 1
    phase('qf-complete', groups=len(keys))
    return dict(result, equivalent=True, reason='all complete conjuncts covered')
