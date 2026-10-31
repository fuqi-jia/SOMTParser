"""Exact existential parameterization of proved finite Int sets.

This is a solver-query transformation, not a claim of open-formula equality.
Only independently proved hard Map(and, S, D) carriers allow fresh memberships.
Complete formulas (including costs) are rewritten without candidate values.
Array-of-set cells require literal reads or independently proved finite index
domains. Arbitrary values of distinct cells extend to a total SMT array.
"""
from dataclasses import dataclass
import itertools
import math

import z3

from .finite_set_representation import prove_finite_set_representations


@dataclass(frozen=True)
class FiniteSetBooleanProjection:
    formula: object
    eliminated_variables: tuple
    boolean_witnesses: tuple
    substitutions: tuple
    carriers: tuple
    index_domains: tuple = ()


def _int_set(sort):
    return (sort.kind() == z3.Z3_ARRAY_SORT
            and sort.domain().kind() == z3.Z3_INT_SORT
            and sort.range().kind() == z3.Z3_BOOL_SORT)


def _constant(term):
    return z3.is_const(term) and term.decl().kind() == z3.Z3_OP_UNINTERPRETED


def _coordinate(term):
    if _constant(term) and _int_set(term.sort()):
        return ('set', term.get_id()), term
    if (z3.is_select(term) and _constant(term.arg(0))
            and term.arg(0).sort().domain().kind() == z3.Z3_INT_SORT
            and _int_set(term.sort())):
        index = z3.simplify(term.arg(1))
        if z3.is_int_value(index):
            return ('cell', term.arg(0).get_id(), index.as_long()), term.arg(0)
    return None


def _normalize_boolean_arrays(formula):
    """Exact K/Store/Map/If interpretation, preserving defaults and full support."""
    views = {}
    integer_supports = {}

    def finite_integer_values(term):
        """A structural overapproximation; unsupported arithmetic stays opaque."""
        todo = [(term, False)]
        while todo:
            current, expanded = todo.pop()
            key = current.get_id()
            if key in integer_supports:
                continue
            if z3.is_int_value(current):
                integer_supports[key] = (current, (current.as_long(),))
                continue
            kind = current.decl().kind()
            if kind == z3.Z3_OP_ITE and current.sort().kind() == z3.Z3_INT_SORT:
                children = current.children()[1:]
            elif kind in (z3.Z3_OP_ADD, z3.Z3_OP_MUL, z3.Z3_OP_SUB, z3.Z3_OP_UMINUS):
                children = current.children()
            else:
                integer_supports[key] = (current, None)
                continue
            if not expanded:
                todo.append((current, True))
                todo.extend((child, False) for child in children
                            if child.get_id() not in integer_supports)
                continue
            supports = [integer_supports[child.get_id()][1] for child in children]
            result = None
            if all(values is not None for values in supports):
                if kind == z3.Z3_OP_ITE:
                    result = set().union(*supports)
                elif kind == z3.Z3_OP_ADD:
                    result = {sum(values) for values in itertools.product(*supports)}
                elif kind == z3.Z3_OP_MUL:
                    result = {math.prod(values) for values in itertools.product(*supports)}
                elif kind == z3.Z3_OP_UMINUS:
                    result = {-value for value in supports[0]}
                else:
                    result = {values[0] - sum(values[1:])
                              for values in itertools.product(*supports)}
            integer_supports[key] = (current, None if result is None else tuple(sorted(result)))
        return integer_supports[term.get_id()][1]

    def view(term):
        key = term.get_id()
        if key in views:
            return views[key][1]
        value = None
        if not _int_set(term.sort()):
            pass
        elif z3.is_const_array(term):
            value = (term.arg(0), {})
        elif z3.is_store(term):
            base = view(term.arg(0))
            index = z3.simplify(term.arg(1))
            possible = finite_integer_values(index)
            if base is not None and possible is not None:
                support = dict(base[1])
                for i in possible:
                    support[i] = (term.arg(2) if z3.is_int_value(index) else
                                  z3.If(index == i, term.arg(2), base[1].get(i, base[0])))
                value = (base[0], support)
        elif z3.is_app(term) and term.decl().kind() == z3.Z3_OP_ARRAY_MAP:
            arguments = [view(x) for x in term.children()]
            if all(x is not None for x in arguments):
                function = z3.get_map_func(term)
                if function.range().kind() == z3.Z3_BOOL_SORT:
                    support = set().union(*(set(x[1]) for x in arguments))
                    value = (function(*[x[0] for x in arguments]),
                             {i: function(*[x[1].get(i, x[0]) for x in arguments])
                              for i in support})
        elif z3.is_app(term) and term.decl().kind() in (
                z3.Z3_OP_SET_UNION, z3.Z3_OP_SET_INTERSECT,
                z3.Z3_OP_SET_DIFFERENCE, z3.Z3_OP_SET_COMPLEMENT):
            arguments = [view(x) for x in term.children()]
            if all(x is not None for x in arguments):
                kind = term.decl().kind()
                def combine(values):
                    if kind == z3.Z3_OP_SET_UNION:
                        return z3.Or(*values)
                    if kind == z3.Z3_OP_SET_INTERSECT:
                        return z3.And(*values)
                    if kind == z3.Z3_OP_SET_DIFFERENCE:
                        return z3.And(values[0], z3.Not(values[1]))
                    return z3.Not(values[0])
                support = set().union(*(set(x[1]) for x in arguments))
                value = (combine([x[0] for x in arguments]),
                         {i: combine([x[1].get(i, x[0]) for x in arguments])
                          for i in support})
        elif z3.is_app(term) and term.decl().kind() == z3.Z3_OP_ITE:
            condition, left, right = term.children()
            a, b = view(left), view(right)
            if a is not None and b is not None:
                support = a[1].keys() | b[1].keys()
                value = (z3.If(condition, a[0], b[0]),
                         {i: z3.If(condition, a[1].get(i, a[0]), b[1].get(i, b[0]))
                          for i in support})
        # Keep term alive: Z3 IDs are only stable while their ASTs are alive.
        views[key] = (term, value)
        return value

    def equality(a, b):
        support = a[1].keys() | b[1].keys()
        return z3.And(a[0] == b[0],
                      *[a[1].get(i, a[0]) == b[1].get(i, b[0]) for i in sorted(support)])

    memo = {}
    todo = [(formula, False)]
    while todo:
        term, expanded = todo.pop()
        key = term.get_id()
        if key in memo:
            continue
        if z3.is_quantifier(term):
            raise ValueError('finite-set Boolean projection requires a quantifier-free formula')
        if not expanded and term.num_args():
            todo.append((term, True))
            todo.extend((child, False) for child in reversed(term.children())
                        if child.get_id() not in memo)
            continue
        children = [memo[x.get_id()][1] for x in term.children()]
        result = term.decl()(*children) if children else term
        if z3.is_select(result) and _int_set(result.arg(0).sort()):
            array = view(result.arg(0))
            if array is not None:
                index = z3.simplify(result.arg(1))
                if z3.is_int_value(index):
                    result = array[1].get(index.as_long(), array[0])
                else:
                    result = array[0]
                    for i in sorted(array[1], reverse=True):
                        result = z3.If(index == i, array[1][i], result)
        elif z3.is_eq(result) and _int_set(result.arg(0).sort()):
            a, b = view(result.arg(0)), view(result.arg(1))
            if a is not None and b is not None:
                result = equality(a, b)
        memo[key] = (term, result)
    return z3.simplify(memo[formula.get_id()][1])



def _set_free_premises(assertions):
    """Extract only actual hard conjuncts, never conditional assumptions."""
    def contains_set_sort(sort):
        while sort.kind() == z3.Z3_ARRAY_SORT:
            if _int_set(sort):
                return True
            sort = sort.range()
        return False

    cache = {}
    def set_free(term):
        todo = [(term, False)]
        while todo:
            current, expanded = todo.pop()
            key = current.get_id()
            if key in cache:
                continue
            if z3.is_quantifier(current) or contains_set_sort(current.sort()):
                cache[key] = (current, False)
                continue
            if not expanded and current.num_args():
                todo.append((current, True))
                todo.extend((child, False) for child in current.children()
                            if child.get_id() not in cache)
                continue
            cache[key] = (current, all(cache[c.get_id()][1] for c in current.children()))
        return cache[term.get_id()][1]

    pending = list(assertions)
    premises = []
    seen = set()
    while pending:
        term = pending.pop()
        if term.get_id() in seen:
            continue
        seen.add(term.get_id())
        if z3.is_and(term):
            pending.extend(term.children())
        elif set_free(term):
            premises.append(term)
    return premises, set_free

def project_finite_sets_to_booleans(assertions, record):
    """Preserve the existentially closed complete conjunction.

    ``record`` receives every independent carrier-representation proof from
    prove_finite_set_representations. No domain is borrowed from a negated or
    conditional assertion. Unsupported coordinates remain exactly as supplied.
    The returned substitutions reconstruct each eliminated set or array cell.
    """
    assertions = tuple(assertions)
    if not assertions or any(not z3.is_bool(x) for x in assertions):
        raise ValueError('expected a nonempty complete Boolean assertion sequence')
    context = assertions[0].ctx
    if any(x.ctx != context for x in assertions):
        raise ValueError('mixed Z3 contexts')
    original = z3.And(*assertions)
    nodes, pending = {}, [original]
    names = set()
    while pending:
        term = pending.pop()
        if term.get_id() in nodes:
            continue
        if z3.is_quantifier(term):
            raise ValueError('finite-set Boolean projection requires a quantifier-free formula')
        nodes[term.get_id()] = term
        if _constant(term):
            names.add(str(term.decl().name()))
        pending.extend(term.children())
    carriers, bases = {}, {}
    for lemma in prove_finite_set_representations(assertions, record):
        selected, representation = lemma.children()
        coordinate = _coordinate(selected)
        if coordinate is None:
            continue
        key, base = coordinate
        support = []
        while z3.is_store(representation):
            support.append(representation.arg(1).as_long())
            representation = representation.arg(0)
        assert z3.is_const_array(representation) and z3.is_false(representation.arg(0))
        carriers.setdefault(key, tuple(sorted(set(support))))
        bases[base.get_id()] = base
    array_bases = {key[1] for key in carriers if key[0] == 'cell'}
    invalid, occurrences, dynamic = set(), {}, {}
    index_proofs = {}
    index_domains = []
    integer_premises, set_free = _set_free_premises(assertions)
    pending, seen = [original], set()
    while pending:
        term = pending.pop()
        if term.get_id() in seen:
            continue
        seen.add(term.get_id())
        if term.get_id() in array_bases:
            invalid.add(term.get_id())
        if z3.is_select(term) and term.arg(0).get_id() in array_bases:
            coordinate = _coordinate(term)
            base_id = term.arg(0).get_id()
            if coordinate is not None and coordinate[0] in carriers:
                occurrences[term.get_id()] = (term, coordinate[0])
            elif coordinate is None and set_free(term.arg(1)):
                index = z3.simplify(term.arg(1))
                cells = tuple(sorted(key[2] for key in carriers
                                     if key[0] == 'cell' and key[1] == base_id))
                proof_key = (base_id, index.get_id())
                if proof_key not in index_proofs:
                    coverage = z3.Or(*[index == i for i in cells])
                    checker = z3.Solver(ctx=context)
                    checker.add(*integer_premises, z3.Not(coverage))
                    query = checker.sexpr() + '\n(check-sat)\n'
                    answer = checker.check()
                    record(z3.And(*integer_premises), coverage, str(answer), query)
                    index_proofs[proof_key] = (index, answer == z3.unsat)
                if index_proofs[proof_key][1]:
                    dynamic[term.get_id()] = (term, base_id, index, cells)
                    index_domains.append((term, cells))
                else:
                    invalid.add(base_id)
            else:
                invalid.add(base_id)
            pending.append(term.arg(1))
        else:
            pending.extend(term.children())
    carriers = {key: domain for key, domain in carriers.items()
                if key[0] == 'set' or key[1] not in invalid}
    values, witnesses = {}, []
    for key, support in carriers.items():
        value = z3.K(z3.IntSort(ctx=context), z3.BoolVal(False, ctx=context))
        for index in support:
            member = z3.FreshConst(z3.BoolSort(ctx=context), 'finite_set_member')
            while str(member.decl().name()) in names:
                member = z3.FreshConst(z3.BoolSort(ctx=context), 'finite_set_member')
            names.add(str(member.decl().name()))
            witnesses.append(member)
            value = z3.Store(value, index, member)
        values[key] = value
    substitutions = [(nodes[key[1]], values[key]) for key in carriers if key[0] == 'set']
    substitutions.extend((term, values[key]) for term, key in occurrences.values() if key in values)
    for term, base_id, index, cells in dynamic.values():
        if base_id in invalid:
            continue
        value = values[('cell', base_id, cells[-1])]
        for i in reversed(cells[:-1]):
            value = z3.If(index == i, values[('cell', base_id, i)], value)
        substitutions.append((term, value))
    eliminated = tuple(bases[key] for key in sorted({key[1] for key in carriers}))
    rewritten = z3.substitute(original, *substitutions) if substitutions else original
    if substitutions:
        rewritten = _normalize_boolean_arrays(rewritten)
    return FiniteSetBooleanProjection(rewritten, eliminated, tuple(witnesses),
                                      tuple(substitutions), tuple(carriers.items()),
                                      tuple((term, cells) for term, cells in index_domains
                                            if term.arg(0).get_id() not in invalid))
