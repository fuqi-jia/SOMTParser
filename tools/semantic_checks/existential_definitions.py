"""Exact substitution of explicitly defined existential witnesses.

All original conjuncts remain in the substituted body. Definitions must be
unconditional, supplied under both polarities of the same Boolean guard, or
selected by mutually exclusive guards in an original disjunction.
No domains, bounds, candidate answers, or solver results are assumed.
"""
from dataclasses import dataclass
import z3
from z3 import z3core

from ._integer_compat import bit_count


@dataclass(frozen=True)
class DefinitionProjection:
    formula: object
    direct_definitions: int = 0
    conditional_definitions: int = 0
    scalarized_arrays: int = 0
    indicator_products: int = 0


def _conjuncts(formula):
    pending = [formula]
    while pending:
        node = pending.pop()
        if z3.is_and(node):
            pending.extend(reversed(node.children()))
        else:
            yield node


class _WitnessDependencyIndex:
    """Exact witness occurrence sets shared by one elimination round.

    Only the supplied constant identities are indexed; free and bound names
    have no significance. Root ASTs own every memoized child until the index
    is discarded, including newly simplified expressions queried later.
    """
    def __init__(self, variables):
        self.variables = tuple(variables.values())
        if not self.variables:
            raise ValueError('dependency index needs witnesses')
        self.ctx = self.variables[0].ctx
        if any(value.ctx != self.ctx for value in self.variables):
            raise ValueError('dependency index needs one Z3 context')
        if any(not z3.is_const(value) or value.num_args() for value in self.variables):
            raise ValueError('dependency witnesses must be constants')
        self.identities = tuple(value.get_id() for value in self.variables)
        self.ordinals = {identity: i for i, identity in enumerate(self.identities)}
        self.roots = {}
        self.memo = {}
        # An exact frozenset cannot change after validation. Retaining it
        # prevents identity reuse; mutable inputs are always checked afresh.
        self.validated_selectors = {}

    @staticmethod
    def _members(value):
        if isinstance(value, frozenset):
            yield from value
        else:
            while value:
                bit = value & -value
                yield bit.bit_length() - 1
                value ^= bit

    @staticmethod
    def _mask(values):
        data = bytearray((max(values) + 8) // 8)
        for value in values:
            data[value >> 3] |= 1 << (value & 7)
        return int.from_bytes(data, 'little')

    @classmethod
    def _combine(cls, values):
        values = [value for value in values if value]
        if not values:
            return frozenset()
        if len(values) == 1:
            return values[0]
        dense, sparse = 0, set()
        for value in values:
            if isinstance(value, int):
                dense |= value
            else:
                sparse.update(value)
        if not sparse:
            return dense
        width = max(dense.bit_length(), max(sparse) + 1)
        count_bound = bit_count(dense) + len(sparse)
        # A high ordinal alone must never allocate a mostly empty bit mask.
        if count_bound >= 64 and width <= 128 * count_bound:
            return dense | cls._mask(sparse)
        sparse.update(cls._members(dense))
        return frozenset(sparse)

    def mentions(self, expression, identities):
        if expression.ctx != self.ctx:
            raise ValueError('dependency query has a different Z3 context')
        immutable = type(identities) is frozenset
        if not immutable or id(identities) not in self.validated_selectors:
            if any(key not in self.ordinals for key in identities):
                raise ValueError('dependency query contains an unindexed witness')
            if immutable:
                self.validated_selectors[id(identities)] = identities
        root_key = expression.get_id()
        self.roots.setdefault(root_key, expression)
        context = self.ctx.ref()
        todo = [(expression.as_ast(), None)]
        while todo:
            node, children = todo.pop()
            key = z3core.Z3_get_ast_id(context, node)
            if key in self.memo:
                continue
            if key in self.ordinals:
                self.memo[key] = frozenset((self.ordinals[key],))
                continue
            if children is None:
                kind = z3core.Z3_get_ast_kind(context, node)
                if kind == z3.Z3_QUANTIFIER_AST:
                    children = [z3core.Z3_get_quantifier_body(context, node)]
                elif kind == z3.Z3_APP_AST:
                    app = z3core.Z3_to_app(context, node)
                    children = [z3core.Z3_get_app_arg(context, app, i)
                                for i in range(z3core.Z3_get_app_num_args(context, app))]
                else:
                    children = []
                todo.append((node, children))
                todo.extend((child, None) for child in children
                            if z3core.Z3_get_ast_id(context, child) not in self.memo)
            else:
                self.memo[key] = self._combine(
                    [self.memo[z3core.Z3_get_ast_id(context, child)] for child in children])
        value = self.memo[root_key]
        if isinstance(value, frozenset):
            return {self.identities[i] for i in value if self.identities[i] in identities}
        if len(identities) < bit_count(value):
            return {key for key in identities if value & (1 << self.ordinals[key])}
        return {self.identities[i] for i in self._members(value)
                if self.identities[i] in identities}


def _mentions(expression, identities, dependencies=None):
    if dependencies is not None:
        return dependencies.mentions(expression, identities)
    found = set()
    pending, seen = [expression], set()
    while pending:
        node = pending.pop()
        key = node.get_id()
        if key in seen:
            continue
        seen.add(key)
        if key in identities:
            found.add(key)
        pending.extend([node.body()] if z3.is_quantifier(node) else node.children())
    return found


def _number(expression):
    if z3.is_int_value(expression):
        return expression.as_long()
    if z3.is_rational_value(expression):
        return expression.as_fraction()
    return None


def _equality_definition(clause, variables, dependencies=None, selector=None):
    """Yield exact v=term equations; Bool disequality is also a definition."""
    if selector is None:
        selector = frozenset(variables)
    negated = z3.is_not(clause)
    atom = clause.arg(0) if negated else clause
    if not z3.is_eq(atom):
        return
    left, right = atom.children()
    if negated and not z3.is_bool(left):
        return
    for variable, value in ((left, right), (right, left)):
        key = variable.get_id()
        if key in variables and not _mentions(value, {key}, dependencies):
            yield key, z3.Not(value) if negated else value
    if negated or not z3.is_arith(left):
        return
    # Isolate only exact unit coefficients. In particular, 2*v=t is not
    # replaced with integer division, and nonlinear occurrences are retained.
    difference = z3.simplify(left - right)
    terms = list(difference.children()) if z3.is_add(difference) else [difference]
    # Classify each summand once. Traversing every summand for every witness
    # repeats whole shared ITE trees in compiler-generated linear equations.
    # Any occurrence outside a scalar multiple blocks isolation of that
    # witness; all such terms remain in other witnesses' exact remainders.
    coefficients, linear_keys, blocked = {}, [], set()
    for term in terms:
        key, coefficient = None, None
        if term.get_id() in variables and z3.is_arith(term):
            key, coefficient = term.get_id(), 1
        elif z3.is_mul(term) and term.num_args() == 2:
            a, b = term.children()
            if _number(a) is not None and b.get_id() in variables and z3.is_arith(b):
                key, coefficient = b.get_id(), _number(a)
            elif _number(b) is not None and a.get_id() in variables and z3.is_arith(a):
                key, coefficient = a.get_id(), _number(b)
        linear_keys.append(key)
        if key is None:
            blocked.update(_mentions(term, selector, dependencies))
        else:
            coefficients[key] = coefficients.get(key, 0) + coefficient
    for key, coefficient in coefficients.items():
        if key not in blocked and coefficient in (-1, 1):
            variable = variables[key]
            remainder = [term for term, linear_key in zip(terms, linear_keys)
                         if linear_key != key]
            zero = z3.RealVal(0, ctx=variable.ctx) if z3.is_real(variable) else z3.IntVal(0, ctx=variable.ctx)
            rest = z3.Sum(*remainder) if remainder else zero
            value = z3.simplify(-rest if coefficient == 1 else rest)
            if value.sort().eq(variable.sort()):
                yield key, value


def _direct(clause, variables, dependencies=None, selector=None):
    key = clause.get_id()
    if key in variables and z3.is_bool(clause):
        yield key, z3.BoolVal(True, ctx=clause.ctx)
    elif z3.is_not(clause) and clause.arg(0).get_id() in variables:
        yield clause.arg(0).get_id(), z3.BoolVal(False, ctx=clause.ctx)
    yield from _equality_definition(clause, variables, dependencies, selector)


def _conditional(clauses, variables, *, all_definitions=False, dependencies=None, selector=None):
    branches = {}
    definitions = {}
    if selector is None:
        selector = frozenset(variables)

    def remember(guard, choices):
        guard = z3.simplify(guard)
        positive = not z3.is_not(guard)
        base = guard if positive else guard.arg(0)
        if z3.is_and(base):
            # AND(g_i) is NOT(OR(NOT(g_i))). Normalize only this outer
            # connective so a flattened opposite clause shares its guard;
            # large arithmetic/ITE sub-DAGs remain unchanged.
            base = z3.Or(*(z3.simplify(z3.Not(atom)) for atom in base.children()))
            positive = not positive
        if z3.is_or(base):
            # Disjunction order is immaterial. Retain the canonical AST with
            # its identity; no arm ordering establishes complementarity.
            base = z3.Or(*sorted(base.children(), key=lambda node: node.get_id()))
        for key, value in choices:
            if _mentions(base, {key}, dependencies):
                continue
            pair = branches.setdefault((key, base.get_id()), {})
            previous = pair.get(positive)
            if previous is None or len(_mentions(value, selector, dependencies)) < len(
                    _mentions(previous[1], selector, dependencies)):
                # Every candidate is an exact consequence under this guard.
                # Prefer independent definitions to inverse aggregate equations;
                # all competing equations remain in the substituted body.
                pair[positive] = (base, value)
            if True in pair and False in pair:
                yes, no = pair[True], pair[False]
                replacement = z3.If(yes[0], yes[1], no[1])
                if not all_definitions:
                    return key, replacement
                previous = definitions.get(key)
                if previous is None or len(_mentions(replacement, selector, dependencies)) < len(
                        _mentions(previous, selector, dependencies)):
                    definitions[key] = replacement
        return None

    flattened = []
    for clause in clauses:
        if z3.is_implies(clause):
            arms = [(clause.arg(0), clause.arg(1))]
        elif z3.is_or(clause) and clause.num_args() == 2:
            arms = [(z3.Not(clause.arg(0)), clause.arg(1)),
                    (z3.Not(clause.arg(1)), clause.arg(0))]
        else:
            if z3.is_or(clause) and clause.num_args() > 2:
                flattened.append(clause)
            continue
        for guard, consequence in arms:
            choices = (entry for atom in _conjuncts(consequence)
                       for entry in _direct(atom, variables, dependencies, selector))
            found = remember(guard, choices)
            if found is not None:
                return found

    # OR(g1, ..., gn, v=t) means NOT(OR(g1, ..., gn)) => v=t.
    # Its complementary positive OR guard must already occur explicitly in
    # another implication/binary clause. Scan those first, independently of
    # input order. This also avoids expanding every member of large domain
    # disjunctions into a quadratic family of unused guards.
    eligible = {key: variables[key] for (key, _), pair in branches.items()
                if True in pair and z3.is_or(pair[True][0])}
    eligible_selector = frozenset(eligible)
    for clause in flattened:
        if not eligible:
            break
        literals = clause.children()
        mentions = [_mentions(atom, eligible_selector, dependencies) for atom in literals]
        counts = {}
        for keys in mentions:
            for key in keys:
                counts[key] = counts.get(key, 0) + 1
        for index, literal in enumerate(literals):
            candidates = {key: eligible[key] for key in mentions[index]
                          if counts[key] == 1}
            if not candidates:
                continue
            candidate_selector = frozenset(candidates)
            choices = [entry for atom in _conjuncts(literal)
                       for entry in _direct(atom, candidates, dependencies, candidate_selector)]
            if not choices:
                continue
            others = literals[:index] + literals[index + 1:]
            found = remember(z3.Not(z3.Or(*others)), choices)
            if found is not None:
                return found
    return definitions if all_definitions else None


def _disjunctive(clauses, variables, dependencies=None):
    """Extract choices fixed by mutually exclusive guards, keeping the OR.

    From OR_i(v=t_i AND g_i), choose the first true guard. This is a definition
    only if overlapping guards have equal values. Here distinct values require
    an exact complementary pair of guard conjuncts after integer-order
    normalization. No solver call, finite-domain assumption, or exhaustive
    guard assumption is needed: the original OR remains after substitution.
    """
    from .integer_order import normalize_integer_order

    definitions, normalized = {}, {}

    def guard_literals(guard):
        positive, negative = set(), set()
        for atom in _conjuncts(guard):
            key = atom.get_id()
            if key not in normalized:
                # Retain original and normalized ASTs to prevent id reuse.
                normalized[key] = (atom, normalize_integer_order(atom).formula,
                                   normalize_integer_order(z3.Not(atom)).formula)
            _, value, inverse = normalized[key]
            if z3.is_false(value):
                return None
            positive.add(value.get_id())
            negative.add(inverse.get_id())
        return positive, negative

    for clause in clauses:
        if not z3.is_or(clause):
            continue
        arms, pending = [], list(clause.children())
        while pending:
            arm = pending.pop()
            if z3.is_or(arm):
                pending.extend(arm.children())
            elif not z3.is_false(arm):
                arms.append(list(_conjuncts(arm)))
        candidates = []
        for atoms in arms:
            choices = {}
            for index, atom in enumerate(atoms):
                if not z3.is_eq(atom):
                    continue
                left, right = atom.children()
                for variable, value in ((left, right), (right, left)):
                    key = variable.get_id()
                    if key not in variables or _mentions(value, {key}, dependencies):
                        continue
                    rest = atoms[:index] + atoms[index + 1:]
                    guard = z3.And(*rest) if rest else z3.BoolVal(True, ctx=clause.ctx)
                    if not _mentions(guard, {key}, dependencies):
                        choices.setdefault(key, (guard, value))
            candidates.append(choices)
        if not candidates:
            continue
        common = set(candidates[0]).intersection(*(set(row) for row in candidates[1:]))
        for key in sorted(common):
            choices = [row[key] for row in candidates]
            literals = [guard_literals(guard) for guard, _ in choices]
            valid = True
            for i, (_, value) in enumerate(choices):
                for j in range(i):
                    if value.eq(choices[j][1]) or literals[i] is None or literals[j] is None:
                        continue
                    if not (literals[i][0] & literals[j][1]
                            or literals[j][0] & literals[i][1]):
                        valid = False
                        break
                if not valid:
                    break
            if valid:
                value = choices[-1][1]
                for guard, alternative in reversed(choices[:-1]):
                    value = z3.If(guard, alternative, value)
                definitions.setdefault(key, value)
                break
    return definitions



def _direct_batch(clauses, variables, dependencies=None, selector=None):
    """Resolve an acyclic set of witnessed equations before one body rewrite.

    Each equation is an original unconditional conjunct. All equations remain
    in the final substituted body, so incompatible definitions still reject.
    A dependency cycle is left bound; no cyclic or self-referential expansion
    is used as a definition. Replacement terms share their Z3 DAGs.
    """
    definitions = {}
    if selector is None:
        selector = frozenset(variables)
    for clause in clauses:
        # Use at most one direction of an equation in this batch. In
        # particular x=y must not create both x->y and y->x from one clause.
        entry = next(_direct(clause, variables, dependencies, selector), None)
        if entry is not None:
            key, value = entry
            definitions.setdefault(key, value)
    return _resolve_definition_batch(definitions, variables, dependencies)


def _resolve_definition_batch(definitions, variables, dependencies=None):
    """Expand only acyclic witnessed definitions; unresolved cycles remain."""
    from collections import deque

    if not definitions:
        return ()
    selected = frozenset(definitions)
    dependencies = {key: _mentions(value, selected, dependencies)
                    for key, value in definitions.items()}
    followers = {key: [] for key in definitions}
    pending_count = {}
    for key, depends in dependencies.items():
        pending_count[key] = len(depends)
        for dependency in depends:
            followers[dependency].append(key)
    ready = deque(key for key in definitions if not pending_count[key])
    resolved = {}
    while ready:
        key = ready.popleft()
        value = definitions[key]
        pairs = [(variables[dependency], resolved[dependency])
                 for dependency in dependencies[key]]
        if pairs:
            value = z3.substitute(value, *pairs)
        resolved[key] = value
        for follower in followers[key]:
            pending_count[follower] -= 1
            if not pending_count[follower]:
                ready.append(follower)
    return tuple((key, value) for key, value in resolved.items())

def _closed_store_reads(body):
    """Expand read-over-write only for terms with no bound variable.

    Substitution below may enter binders. Restricting its pairs to closed
    terms prevents a read from escaping the binder that owns its index.
    """
    memo, pairs = {}, []
    pending = [(body, False)]
    while pending:
        term, ready = pending.pop()
        key = term.get_id()
        if key in memo:
            continue
        if z3.is_var(term):
            memo[key] = (term, True)
            continue
        children = ([term.body()] if z3.is_quantifier(term)
                    else term.children())
        if not ready and children:
            pending.append((term, True))
            pending.extend((child, False) for child in children)
            continue
        bound = any(memo[child.get_id()][1] for child in children)
        memo[key] = (term, bound)
        if (bound or not z3.is_select(term) or term.num_args() != 2
                or not z3.is_store(term.arg(0)) or term.arg(0).num_args() != 3):
            continue
        array, index = term.children()
        stores = []
        while z3.is_store(array):
            base, position, value = array.children()
            stores.append((position, value))
            array = base
        value = z3.Select(array, index)
        for position, stored in reversed(stores):
            value = z3.If(index == position, stored, value)
        pairs.append((term, z3.simplify(value)))
    return z3.substitute(body, *pairs) if pairs else body


def _defined_array_witness(body, variables):
    """Eliminate one array whose used cells have original definitions.

    Different concrete Int cells can be extended to a total array, including
    array-valued cells. Symbolic reads are eligible only if the original
    unconditional bounds prove that their index reaches defined ground cells.
    All original equations and bounds remain after substitution. A whole-array
    occurrence, bound index, missing cell, or self-dependent definition retains
    the original witness. No value for an unobserved cell is asserted.
    """
    from .symbolic_array_projection import _bounded_read_definitions

    arrays = {key: value for key, value in variables.items()
              if z3.is_array(value) and value.sort().domain().kind() == z3.Z3_INT_SORT}
    if not arrays:
        return None
    prepared = _closed_store_reads(body)
    clauses = list(_conjuncts(prepared))
    definitions = {}
    for clause in clauses:
        if not z3.is_eq(clause):
            continue
        left, right = clause.children()
        for cell, value in ((left, right), (right, left)):
            if (not z3.is_select(cell) or cell.num_args() != 2
                    or not z3.is_int_value(cell.arg(1))):
                continue
            root = cell.arg(0)
            key = root.get_id()
            if key in arrays and not _mentions(value, {key}):
                definitions.setdefault(key, {}).setdefault(cell.arg(1).as_long(), (cell, value))
    for key, known in definitions.items():
        root = arrays[key]
        reads, pending, seen, invalid = {}, [prepared], set(), False
        while pending and not invalid:
            term = pending.pop()
            identity = term.get_id()
            if identity in seen:
                continue
            seen.add(identity)
            if identity == key:
                invalid = True
                break
            if z3.is_select(term) and term.arg(0).get_id() == key:
                if term.num_args() != 2:
                    invalid = True
                    break
                index = term.arg(1)
                todo, visited, bound = [index], set(), False
                while todo:
                    node = todo.pop()
                    if node.get_id() in visited:
                        continue
                    visited.add(node.get_id())
                    if z3.is_var(node) or z3.is_quantifier(node) or node.get_id() == key:
                        bound = True
                        break
                    todo.extend(node.children())
                if bound:
                    invalid = True
                    break
                if z3.is_int_value(index) and index.as_long() not in known:
                    invalid = True
                    break
                reads[identity] = (root, index, term)
                pending.append(index)
            elif z3.is_quantifier(term):
                pending.append(term.body())
                # Patterns have no truth conditions, but still must not retain
                # a removed witness or a binder-relative read replacement.
                for i in range(term.num_patterns()):
                    pending.extend(term.pattern(i).children())
                for i in range(term.num_no_patterns()):
                    pending.append(term.no_pattern(i))
            else:
                pending.extend(term.children())
        if invalid:
            continue
        bounded = _bounded_read_definitions(prepared, tuple(reads.values()))
        covered = {term.get_id() for term, _ in bounded}
        if any(not z3.is_int_value(index) and cell.get_id() not in covered
               for _, index, cell in reads.values()):
            continue
        ground = tuple(known.values())
        replacements = list(ground)
        replacements.extend((cell, z3.substitute(value, *ground))
                            for cell, value in bounded)
        candidate = z3.substitute(prepared, *replacements)
        if _mentions(candidate, {key}):
            continue
        return key, candidate
    return None


def _scalar_array_witnesses(body, variables):
    """Project remaining scalar arrays while retaining unrelated binders.

    The scalar-array projector handles a complete QF body. A conjunct with a
    quantifier can be left outside that projection precisely when it contains
    none of the projected arrays, including in binder patterns. Other private
    scalar variables retain their original outer existential scope. Whole-array
    uses or quantified array reads leave the entire projection unchanged.
    """
    from .ground_array_projection import UnsupportedArrayProjection
    from .symbolic_array_projection import scalarize_symbolic_array_reads

    arrays = {key: value for key, value in variables.items()
              if z3.is_array(value) and value.sort().domain().kind() == z3.Z3_INT_SORT
              and value.sort().range().kind() != z3.Z3_ARRAY_SORT}
    if not arrays:
        return None
    independent, qf = [], []
    for clause in _conjuncts(body):
        pending, seen, quantified, dependent = [clause], set(), False, False
        while pending:
            term = pending.pop()
            key = term.get_id()
            if key in seen:
                continue
            seen.add(key)
            dependent |= key in arrays
            if z3.is_quantifier(term):
                quantified = True
                pending.append(term.body())
                for i in range(term.num_patterns()):
                    pending.extend(term.pattern(i).children())
                for i in range(term.num_no_patterns()):
                    pending.append(term.no_pattern(i))
            else:
                pending.extend(term.children())
        if quantified:
            if dependent:
                return None
            independent.append(clause)
        else:
            qf.append(clause)
    complete_qf = z3.And(*qf) if qf else z3.BoolVal(True, ctx=body.ctx)
    try:
        result = scalarize_symbolic_array_reads(complete_qf, tuple(arrays.values()))
    except UnsupportedArrayProjection:
        return None
    rewritten = z3.And(result.body, *independent) if independent else result.body
    remaining = {key: value for key, value in variables.items() if key not in arrays}
    remaining.update((value.get_id(), value) for value in result.private_variables)
    return rewritten, remaining, len(result.eliminated_arrays)


def _aig_indicator_formula(formula):
    """Fold the Boolean circuit exposed by exact indicator normalization.

    AIG rewriting reconstructs formulas from their original theory atoms; it
    does not run a satisfiability check. Apply it only to a complete QF formula,
    and retain the already exact input if the tactic refuses, splits a goal or
    introduces a declaration. Existing quantifier scopes stay with the caller.
    """
    def declarations(expression):
        pending, seen, result = [expression], set(), set()
        while pending:
            node = pending.pop()
            key = node.get_id()
            if key in seen:
                continue
            seen.add(key)
            if z3.is_quantifier(node) or z3.is_var(node):
                return None
            if node.decl().kind() == z3.Z3_OP_UNINTERPRETED:
                result.add(node.decl().get_id())
            pending.extend(node.children())
        return result

    original = declarations(formula)
    if original is None:
        return formula
    try:
        goal = z3.Goal(ctx=formula.ctx)
        goal.add(formula)
        rewritten = z3.Tactic('aig', ctx=formula.ctx)(goal)
        if len(rewritten) != 1:
            return formula
        result = z3.simplify(rewritten[0].as_expr())
        if not z3.is_bool(result) or result.ctx != formula.ctx:
            return formula
        updated = declarations(result)
        if updated is None or not updated <= original:
            return formula
        return result
    except z3.Z3Exception:
        return formula


def _normalize_indicator_conjuncts(body):
    # The arithmetic helper deliberately does not enter binders. One QF body
    # shares its complete DAG; a retained nested binder is kept verbatim while
    # normalization applies to its sibling conjuncts in the same outer scope.
    from .boolean_indicator_products import normalize_boolean_indicator_products

    result = normalize_boolean_indicator_products(body)
    if result.product_nodes:
        return _aig_indicator_formula(result.formula), result.product_nodes
    if result.complete_scan:
        return result.formula, 0
    clauses, products = [], 0
    for clause in _conjuncts(body):
        normalized = normalize_boolean_indicator_products(clause)
        clauses.append(_aig_indicator_formula(normalized.formula)
                       if normalized.product_nodes else normalized.formula)
        products += normalized.product_nodes
    if not products:
        return body, 0
    return z3.simplify(z3.And(*clauses)), products


def eliminate_existential_definitions(formula):
    """Eliminate only witnessed outer existential variables, exactly.

    Opening with fresh constants and rebuilding the residual binder avoids
    capture, including when the body contains a nested quantifier. Each chosen
    definition excludes its own variable. Cycles therefore retain at least one
    bound variable; inconsistent or competing definitions remain constraints.
    """
    if not z3.is_quantifier(formula) or not formula.is_exists():
        return DefinitionProjection(formula)
    opened = [z3.FreshConst(formula.var_sort(i), prefix='definition_witness')
              for i in range(formula.num_vars())]
    body = z3.substitute_vars(formula.body(), *reversed(opened))
    remaining = {value.get_id(): value for value in opened}
    direct_count = conditional_count = scalarized_count = indicator_count = 0
    normalize = True
    while remaining:
        if normalize:
            body, count = _normalize_indicator_conjuncts(body)
            indicator_count += count
            normalize = False
        array = _defined_array_witness(body, remaining)
        if array is not None:
            key, body = array
            del remaining[key]
            direct_count += 1
            normalize = True
            continue
        clauses = list(_conjuncts(body))
        dependencies = _WitnessDependencyIndex(remaining)
        selector = frozenset(remaining)
        batch = _direct_batch(clauses, remaining, dependencies, selector)
        if batch:
            pairs = [(remaining.pop(key), value) for key, value in batch]
            body = z3.simplify(z3.substitute(body, *pairs))
            direct_count += len(pairs)
            normalize = True
            continue
        guarded = _conditional(clauses, remaining, all_definitions=True, dependencies=dependencies, selector=selector)
        for key, value in _disjunctive(clauses, remaining, dependencies).items():
            guarded.setdefault(key, value)
        conditional_batch = _resolve_definition_batch(guarded, remaining, dependencies)
        if conditional_batch:
            pairs = [(remaining.pop(key), value) for key, value in conditional_batch]
            body = z3.simplify(z3.substitute(body, *pairs))
            conditional_count += len(pairs)
            normalize = True
            continue
        found = next((entry for clause in clauses
                      for entry in _direct(clause, remaining, dependencies, selector)), None)
        conditional = found is None
        if found is None:
            found = _conditional(clauses, remaining, dependencies=dependencies, selector=selector)
        if found is None:
            # Existing scalar definitions simplify indices before the array
            # projector can introduce any read-congruence obligations.
            projected = _scalar_array_witnesses(body, remaining)
            if projected is None:
                break
            body, remaining, count = projected
            scalarized_count += count
            normalize = True
            continue
        key, replacement = found
        variable = remaining.pop(key)
        body = z3.simplify(z3.substitute(body, (variable, replacement)))
        direct_count += not conditional
        conditional_count += conditional
        normalize = True
    if normalize:
        body, count = _normalize_indicator_conjuncts(body)
        indicator_count += count
    if not (direct_count or conditional_count or scalarized_count or indicator_count):
        return DefinitionProjection(formula)
    result = z3.Exists(list(remaining.values()), body) if remaining else body
    # Arithmetic normalization can make an original witness unused. Let Z3
    # simplify its binder capture-safely, including retained nested scopes.
    if indicator_count:
        result = z3.simplify(result)
    return DefinitionProjection(result, direct_count, conditional_count,
                                scalarized_count, indicator_count)
