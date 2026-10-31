"""Prove linear WBO auxiliary encodings by domains and unique extensions.

No auxiliary-name convention or production encoder is used. Binary auxiliaries
are recognized by their complete domains, and each pair of inequalities is
checked under both binary values against a source comparison and its negation.
Unbounded cost variables must have acyclic, unit-coefficient definitions. The
remaining hard constraints, strict threshold and exact cost must all match.
"""
from collections import defaultdict, deque

try:
    from .pb_certificate import (CertificateError, TRUE, FALSE, add, accumulate,
                                 constant, conjunction, negate, relation)
except ImportError:
    from pb_certificate import (CertificateError, TRUE, FALSE, add, accumulate,
                                constant, conjunction, negate, relation)


def variable(name):
    return {('v:' + name,): 1}


def names(poly):
    result = set()
    for monomial in poly:
        if monomial:
            if len(monomial) != 1 or not monomial[0].startswith('v:'):
                raise CertificateError('projected WBO certificate requires integer linear rows')
            result.add(monomial[0][2:])
    return result


def row_poly(row):
    if row[0] not in ('>=', '='):
        raise CertificateError('unsupported projected WBO comparison')
    poly = dict(row[1])
    names(poly)
    return poly


def simplify_in_binary_box(row, public):
    if row in (TRUE, FALSE):
        return row
    if row[0] == '!=':
        return negate(simplify_in_binary_box(('=', row[1]), public))
    poly = row_poly(row)
    if not names(poly) <= public:
        raise CertificateError('private symbol remains in source comparison')
    lo = hi = poly.get((), 0)
    for monomial, coefficient in poly.items():
        if monomial:
            lo += min(coefficient, 0)
            hi += max(coefficient, 0)
    if row[0] == '>=':
        return TRUE if lo >= 0 else FALSE if hi < 0 else row
    return TRUE if lo == hi == 0 else FALSE if lo > 0 or hi < 0 else row


def substitute_one(poly, name, definition):
    result = poly.copy()
    factor = result.pop(('v:' + name,), 0)
    accumulate(result, definition, factor)
    return result


def certify_projected_wbo(source, declarations, hard, objective, context):
    if objective is None or not source.variables < declarations:
        raise CertificateError('missing WBO cost or invalid source coordinate inclusion')
    public = source.variables
    private = declarations - public
    remaining = set(hard)
    # Establish public Boolean domains before using any box-bound argument.
    for name in public:
        for row in (relation('>=', variable(name), {}), relation('<=', variable(name), constant(1))):
            if row not in remaining:
                raise CertificateError('missing public Boolean domain')

    binary = set()
    for name in private:
        bounds = {relation('>=', variable(name), {}), relation('<=', variable(name), constant(1))}
        if bounds <= remaining:
            binary.add(name)
            remaining.difference_update(bounds)
    costs = private - binary
    if not binary:
        raise CertificateError('no fully bounded private violation indicator')
    # The ordinary encoder uses (= (= r 0) predicate), whereas the packed
    # encoder uses two linear implications. Both are checked under each
    # binary value, including any additional constraints on that indicator.
    zero_one_tests = {}
    for name in binary:
        for value in (0, 1):
            zero_one_tests[relation('=', variable(name), constant(value))] = (name, value)
    reifications = defaultdict(list)
    for row in list(remaining):
        if row[0] != 'iff':
            continue
        left, right = row[1]
        if right in zero_one_tests:
            left, right = right, left
        if left not in zero_one_tests:
            raise CertificateError('Boolean reification lacks a binary equality')
        name, value = zero_one_tests[left]
        if right not in (TRUE, FALSE) and not names(row_poly(
                ('=', right[1]) if right[0] == '!=' else right)) <= public:
            raise CertificateError('Boolean reification is not a public source predicate')
        reifications[name].append((value, right))
        remaining.remove(row)
    for row in remaining:
        if row not in (TRUE, FALSE):
            row_poly(row)
    names(objective)

    # Extract a triangular system without expanding all prefix sums. Defining
    # c_k from earlier c_i is a unique integer extension only for coefficient
    # +/-1. Every unused equation remains a hard obligation below.
    equations, dependencies, occurrences = {}, {}, defaultdict(set)
    for row in remaining:
        if row[0] != '=':
            continue
        poly = row_poly(row)
        unknown = names(poly) & costs
        if unknown:
            equations[row] = poly
            dependencies[row] = set(unknown)
            for name in unknown:
                occurrences[name].add(row)
    queue = deque(row for row, unknown in dependencies.items() if len(unknown) == 1)
    definitions, order = {}, []
    while queue:
        row = queue.popleft()
        unknown = dependencies[row]
        if len(unknown) != 1 or row not in remaining:
            continue
        name = next(iter(unknown))
        coefficient = equations[row][('v:' + name,)]
        if abs(coefficient) != 1:
            continue
        definition = {m: -c // coefficient for m, c in equations[row].items()
                      if m != ('v:' + name,)}
        # Subtracting a dict_keys view scans every earlier definition.
        # Probe only this row's cost dependencies to keep sparse chains linear.
        if any(dependency not in definitions for dependency in names(definition) & costs):
            raise CertificateError('cyclic cost definition')
        definitions[name] = definition
        order.append(name)
        remaining.remove(row)
        for other in occurrences[name]:
            dependencies[other].discard(name)
            if len(dependencies[other]) == 1:
                queue.append(other)
    if definitions.keys() != costs:
        raise CertificateError('private cost coordinate lacks a unique integral acyclic definition')

    def expand(poly):
        # Domains and violation implications already contain no cost symbols.
        # Scanning every prefix for each such row is quadratic in large WBOs.
        if not (names(poly) & costs):
            return poly.copy()
        # Backwards substitution visits each definition once for this root;
        # retaining an expanded polynomial for every prefix would be quadratic.
        result = poly.copy()
        for name in reversed(order):
            coefficient = result.pop(('v:' + name,), 0)
            if coefficient:
                accumulate(result, definitions[name], coefficient)
        if names(result) & costs:
            raise CertificateError('uneliminated cost coordinate')
        return result

    actual_cost = expand(objective)
    expanded = set()
    for row in remaining:
        expanded.add(row if row in (TRUE, FALSE) else relation(row[0], expand(dict(row[1])), {}))
    remaining = expanded
    threshold = None if source.top is None else relation('<', actual_cost, constant(source.top))
    residual_weight = sum(weight for weight in source.soft.values()
                          if source.top is None or weight < source.top)
    if threshold is not None:
        if source.top <= residual_weight and threshold != TRUE and threshold not in remaining:
            raise CertificateError('missing exact strict WBO threshold')
        remaining.discard(threshold)

    expected_hard = set(source.hard)
    if source.top is not None and source.top <= sum(source.soft.values()):
        expected_hard.discard(relation('<', source.objective, constant(source.top)))
    soft_comparisons, direct_equalities = [], []
    zero_cost_comparisons = set()
    for row, weight in source.soft.items():
        if source.top is not None and weight >= source.top:
            expected_hard.add(row)
        # A source can repeat one predicate as both a mandatory and a soft
        # row. The target may keep the latter's uniquely defined indicator,
        # although its cost is zero on the mandatory relation. Keep checking
        # its two branches; only erase its cost after matching all hard rows.
        forced = row in expected_hard
        if row[0] == '=':
            # For an integer p, [p!=0] = [p<0]+[p>0]; these events are disjoint.
            poly = dict(row[1])
            parts = (relation('>=', poly, {}), relation('<=', poly, {}))
            soft_comparisons.extend((part, weight) for part in parts)
            direct_equalities.append((row, parts))
            if forced:
                zero_cost_comparisons.update(parts)
        elif row[0] in ('>=', 'bool'):
            soft_comparisons.append((row, weight))
            if forced:
                zero_cost_comparisons.add(row)
        else:
            raise CertificateError('unsupported source soft relation for projection')

    def violation_cost(comparison):
        if comparison in zero_cost_comparisons:
            return {}
        return add(constant(1), context.indicator(
            simplify_in_binary_box(comparison, public)), -1)

    expected = {}
    branch_pairs = {}
    for comparison, weight in soft_comparisons:
        yes = simplify_in_binary_box(comparison, public)
        no = simplify_in_binary_box(negate(comparison), public)
        cost = violation_cost(comparison)
        branch_pairs[(yes, no)] = cost
        accumulate(expected, cost, weight)
    for comparison, parts in direct_equalities:
        cost = {}
        for part in parts:
            accumulate(cost, violation_cost(part))
        # The single Boolean equivalence and the disjoint below/above pair
        # have the same violation cost for every integer-valued polynomial.
        branch_pairs[(simplify_in_binary_box(comparison, public),
                      simplify_in_binary_box(negate(comparison), public))] = cost

    by_indicator = defaultdict(list)
    pure = set()
    for row in remaining:
        if row in (TRUE, FALSE):
            pure.add(row)
            continue
        mentioned = names(dict(row[1])) & binary
        if not mentioned:
            pure.add(row)
        elif len(mentioned) == 1 and row[0] == '>=':
            by_indicator[next(iter(mentioned))].append(row)
        else:
            raise CertificateError('extra coupled/private constraint is not a reification pair')
    expected_hard.discard(TRUE)
    pure.discard(TRUE)
    if pure != expected_hard:
        raise CertificateError('source hard relation changed under WBO projection')
    meanings = {}
    for name in binary:
        rows = by_indicator[name]
        if len(rows) != 2 and not reifications[name]:
            raise CertificateError('violation indicator needs both implications')
        branches = []
        for value in (0, 1):
            conditions = [simplify_in_binary_box(
                relation('>=', substitute_one(dict(row[1]), name, constant(value)), {}), public)
                for row in rows]
            conditions.extend(simplify_in_binary_box(
                predicate if value == truth_value else negate(predicate), public)
                for truth_value, predicate in reifications[name])
            branches.append(conjunction(conditions))
        pair = tuple(branches)
        if pair not in branch_pairs:
            raise CertificateError('binary branches do not define a source violation exactly')
        meanings[name] = branch_pairs[pair]
    projected_cost = actual_cost.copy()
    for name, definition in meanings.items():
        coefficient = projected_cost.pop(('v:' + name,), 0)
        accumulate(projected_cost, definition, coefficient)
    if projected_cost != expected:
        raise CertificateError('projected signed WBO cost differs from source violated weight')
    return dict(public_variables=len(public), binary_violation_indicators=len(binary),
                uniquely_defined_cost_coordinates=len(costs),
                domains_and_all_constraints_checked=True, both_indicator_branches_checked=True,
                strict_threshold_checked=source.top is not None, exact_signed_cost=True,
                projection='every source assignment has exactly one target auxiliary extension')
