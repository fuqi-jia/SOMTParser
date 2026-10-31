"""Proof-gated compression of a narrow finite pairwise uniqueness quantifier.

The projection path applies this rule to top-level conjunctions before
finite quantifier expansion.
It recognizes only a four-Int-variable forall of the form

    guard(row_a, row_b) and i in [lo, hi) and i < j and j < hi
      => not same-row-value(row_a, row_b, i)
         or not same-row-value(row_a, row_b, j)

where ``same`` compares reads from one two-dimensional array at the same
row pair and index. It replaces pairwise-index clauses with one finite
sum-at-most-one constraint. Every unsupported shape and every budget refusal
returns the identical original AST. This is a generic two-dimensional array
pattern, not a model- or benchmark-specific rule.
"""
from dataclasses import dataclass
from typing import Optional


@dataclass(frozen=True)
class AtMostOneRewrite:
    formula: object
    rewritten: bool
    reason: str
    index_lower: Optional[int] = None
    index_upper: Optional[int] = None
    generated_node_estimate: int = 0

    @property
    def week_lower(self):
        """Backward-compatible alias; these are generic array indices."""
        return self.index_lower

    @property
    def week_upper(self):
        """Backward-compatible alias; these are generic array indices."""
        return self.index_upper


@dataclass(frozen=True)
class ConjunctRewrite:
    formula: object
    rewrite_count: int
    estimated_generated_nodes: int
    budget_exhausted: bool


class _Refuse(Exception):
    pass


def _is_int_sort(z3, sort):
    return sort.kind() == z3.Z3_INT_SORT


def _bound_index(z3, expression):
    return z3.get_var_index(expression) if z3.is_var(expression) else None


def _contains_bound_index(z3, expression, indexes):
    stack = [expression]
    seen = set()
    while stack:
        node = stack.pop()
        node_id = node.get_id()
        if node_id in seen:
            continue
        seen.add(node_id)
        if z3.is_var(node) and z3.get_var_index(node) in indexes:
            return True
        if z3.is_quantifier(node):
            # Nested binders complicate index shifting; this rewrite does not
            # inspect or cross a nested quantifier.
            raise _Refuse("nested quantifier in recognized scope")
        if z3.is_app(node):
            stack.extend(node.children())
    return False


def _assert_no_outer_bound_vars(z3, expression, own_var_count):
    stack = [expression]
    seen = set()
    while stack:
        node = stack.pop()
        node_id = node.get_id()
        if node_id in seen:
            continue
        seen.add(node_id)
        if z3.is_quantifier(node):
            raise _Refuse("nested quantifier in recognized scope")
        if z3.is_var(node) and z3.get_var_index(node) >= own_var_count:
            raise _Refuse("outer de Bruijn reference would escape rewritten binder")
        if z3.is_app(node):
            stack.extend(node.children())


def _conjuncts(z3, expression):
    if z3.is_and(expression):
        result = []
        for child in expression.children():
            result.extend(_conjuncts(z3, child))
        return result
    return [expression]


def _dag_size(z3, expressions):
    seen = set()
    stack = list(expressions)
    while stack:
        node = stack.pop()
        node_id = node.get_id()
        if node_id in seen:
            continue
        seen.add(node_id)
        if z3.is_quantifier(node):
            stack.append(node.body())
        elif z3.is_app(node):
            stack.extend(node.children())
    return len(seen)


def _uninterpreted_decl_names(z3, expression):
    """Collect every uninterpreted declaration name, including functions."""
    names = set()
    stack = [expression]
    seen = set()
    while stack:
        node = stack.pop()
        node_id = node.get_id()
        if node_id in seen:
            continue
        seen.add(node_id)
        if z3.is_quantifier(node):
            # The accepted rewrite rejects nested quantifiers; traversing its
            # body here also keeps this collector correct when used earlier.
            stack.append(node.body())
        elif z3.is_app(node):
            decl = node.decl()
            if decl.kind() == z3.Z3_OP_UNINTERPRETED:
                names.add(str(decl.name()))
            stack.extend(node.children())
    return names


def _fresh_const_avoiding_names(z3, sort, prefix, reserved_names):
    """Create a fresh binder whose printed symbol cannot shadow input names."""
    # FreshConst uses a monotonically fresh suffix, so among |reserved|+1
    # candidates at least one spelling is unused. Include the successful
    # spelling immediately so the next generated binder cannot reuse it.
    for _ in range(len(reserved_names) + 1):
        candidate = z3.FreshConst(sort, prefix=prefix)
        name = str(candidate.decl().name())
        if name not in reserved_names:
            reserved_names.add(name)
            return candidate
    raise _Refuse("could not allocate a capture-safe fresh binder name")


def _normalize_bound_atom(z3, atom, variable_index):
    """Return (kind, integer) for x >= k, x > k, x <= k, or x < k."""
    if not z3.is_app(atom) or atom.num_args() != 2:
        return None
    op = atom.decl().kind()
    lhs, rhs = atom.children()
    li, ri = _bound_index(z3, lhs), _bound_index(z3, rhs)
    lv = lhs.as_long() if z3.is_int_value(lhs) else None
    rv = rhs.as_long() if z3.is_int_value(rhs) else None

    relation = {
        z3.Z3_OP_LT: "lt",
        z3.Z3_OP_LE: "le",
        z3.Z3_OP_GT: "gt",
        z3.Z3_OP_GE: "ge",
    }.get(op)
    if relation is None:
        return None
    if li == variable_index and rv is not None:
        return relation, rv
    if lv is not None and ri == variable_index:
        reverse = {"lt": "gt", "le": "ge", "gt": "lt", "ge": "le"}
        return reverse[relation], lv
    return None


def _read_pair(z3, disequality):
    """Parse a two-dimensional array disequality and return (root, i, j, t)."""
    operands = None
    if z3.is_distinct(disequality) and disequality.num_args() == 2:
        operands = list(disequality.children())
    elif z3.is_not(disequality) and z3.is_eq(disequality.arg(0)):
        eq = disequality.arg(0)
        operands = list(eq.children())
    if operands is None or len(operands) != 2:
        raise _Refuse("body is not a binary array-read disequality")

    parsed = []
    for term in operands:
        if not z3.is_select(term) or term.num_args() != 2:
            raise _Refuse("disequality operand is not a rank-two array read")
        row, index = term.children()
        if not z3.is_select(row) or row.num_args() != 2:
            raise _Refuse("disequality operand is not a rank-two array read")
        root, row_index = row.children()
        index_binder = _bound_index(z3, index)
        row_binder = _bound_index(z3, row_index)
        if index_binder is None or row_binder is None:
            raise _Refuse("array indices must be bound Int variables")
        if not _is_int_sort(z3, index.sort()) or not _is_int_sort(z3, row_index.sort()):
            raise _Refuse("array indices must have Int sort")
        if not z3.is_const(root) or root.sort().kind() != z3.Z3_ARRAY_SORT:
            raise _Refuse("array root must be a scalar constant")
        parsed.append((root, row_binder, index_binder))

    first, second = parsed
    if not first[0].eq(second[0]):
        raise _Refuse("disequality reads use different array roots")
    if first[1] == second[1] or first[2] != second[2]:
        raise _Refuse("reads must use two distinct rows at the same index")
    return first[0], first[1], second[1], first[2]


def rewrite_finite_pairwise_at_most_one(quantifier, *,
                                        max_week_terms=256,
                                        max_generated_nodes=20000):
    """Compress one exact pairwise-uniqueness forall, or return it unchanged.

    The accepted finite-index guard is intentionally narrow: one explicit
    lower and upper bound for the first index, one explicit upper bound for
    the second index with the same exclusive endpoint, and strict ordering
    from first to second. The second index's lower bound follows from the
    first index lower bound and strict ordering. Additional conjuncts are
    allowed only when they contain neither index binder; all are retained as
    the rewritten outer guard.

    ``max_week_terms`` bounds the finite sum width. The conservative node
    estimate is checked before building any replacement nodes; a refusal
    returns ``quantifier`` exactly, with no partially weakened formula.
    """
    import z3

    if min(max_week_terms, max_generated_nodes) < 0:
        raise ValueError("resource limits must be nonnegative")
    original = quantifier
    try:
        if not z3.is_quantifier(quantifier) or not quantifier.is_forall():
            raise _Refuse("input is not a forall quantifier")
        if quantifier.num_vars() != 4:
            raise _Refuse("expected exactly four bound variables")
        if any(not _is_int_sort(z3, quantifier.var_sort(i)) for i in range(4)):
            raise _Refuse("all four bound variables must have Int sort")

        body = quantifier.body()
        _assert_no_outer_bound_vars(z3, body, quantifier.num_vars())
        if not z3.is_implies(body) or body.num_args() != 2:
            raise _Refuse("forall body must be a direct implication")
        guard, consequence = body.children()
        if not z3.is_or(consequence) or consequence.num_args() != 2:
            raise _Refuse("consequent must be a binary disjunction")

        first = _read_pair(z3, consequence.arg(0))
        second = _read_pair(z3, consequence.arg(1))
        root, row_a, row_b, index_a = first
        root2, row_c, row_d, index_b = second
        if not root.eq(root2):
            raise _Refuse("consequent reads use different array roots")
        if {row_a, row_b} != {row_c, row_d}:
            raise _Refuse("consequent reads do not use the same row pair")
        if index_a == index_b or {index_a, index_b} != set(range(4)) - {row_a, row_b}:
            raise _Refuse("expected the two remaining binders to be array indices")
        index_vars = {index_a, index_b}
        if len(index_vars) != 2 or len({row_a, row_b}) != 2:
            raise _Refuse("expected four distinct binder roles")

        # Each disjunct must assert that its two reads differ. Therefore the
        # disjunction is exactly not (same-at-index-a and same-at-index-b).
        # _read_pair rejects equalities and all other body operators.
        atoms = _conjuncts(z3, guard)
        lower_by_var = {index_a: [], index_b: []}
        upper_by_var = {index_a: [], index_b: []}
        has_order = False
        outer_atoms = []
        for atom in atoms:
            if z3.is_app(atom) and atom.num_args() == 2:
                op = atom.decl().kind()
                left, right = _bound_index(z3, atom.arg(0)), _bound_index(z3, atom.arg(1))
                if ((op == z3.Z3_OP_LT and left == index_a and right == index_b)
                        or (op == z3.Z3_OP_GT and left == index_b and right == index_a)):
                    has_order = True
                    continue
            indexes = {i for i in range(4)
                       if _contains_bound_index(z3, atom, {i})}
            if not indexes.intersection(index_vars):
                outer_atoms.append(atom)
                continue
            recognized = False
            for variable in index_vars:
                normalized = _normalize_bound_atom(z3, atom, variable)
                if normalized is None:
                    continue
                relation, value = normalized
                if relation in {"ge", "gt"}:
                    # The first index lower bound is explicit; a lower bound
                    # on the later index is deliberately rejected.
                    lower_by_var[variable].append(
                        value if relation == "ge" else value + 1)
                    recognized = True
                elif relation in {"lt", "le"}:
                    upper_by_var[variable].append(
                        value if relation == "lt" else value + 1)
                    recognized = True
            if not recognized:
                raise _Refuse("unsupported index-dependent guard conjunct")
        if not has_order:
            raise _Refuse("missing strict index-order guard")

        # The first disequality's index is the summed index. The second is the
        # later index. Only this orientation is accepted by the guard matcher.
        if len(lower_by_var[index_a]) != 1 or len(upper_by_var[index_a]) != 1:
            raise _Refuse("first index needs one explicit lower and upper bound")
        lower = lower_by_var[index_a][0]
        upper = upper_by_var[index_a][0]
        if upper_by_var[index_b] != [upper]:
            raise _Refuse("second index needs the same upper bound")
        if lower_by_var[index_b]:
            raise _Refuse("explicit lower bound on second index is unsupported")

        width = max(0, upper - lower)
        if width > max_week_terms:
            raise _Refuse("finite-index sum width exceeds configured budget")
        # Two copies of the retained guard DAG conservatively cover the
        # original DAG plus substitution rebuilding; 16 nodes per index safely
        # covers two array reads, equality, ite, and n-ary sum construction.
        reserved_names = _uninterpreted_decl_names(z3, body)
        estimate = (16 + 16 * width + 2 * _dag_size(z3, outer_atoms)
                    + len(reserved_names))
        if estimate > max_generated_nodes:
            raise _Refuse("generated AST estimate exceeds configured budget")

        # All non-index guard atoms are preserved. Make a fresh two-variable
        # quantifier and substitute only those atoms; index variables cannot be
        # present here by the classification above.
        ctx = quantifier.ctx
        row_terms = {
            row_a: _fresh_const_avoiding_names(
                z3, z3.IntSort(ctx=ctx), "pair_left", reserved_names),
            row_b: _fresh_const_avoiding_names(
                z3, z3.IntSort(ctx=ctx), "pair_right", reserved_names),
        }
        replacement_by_index = [z3.IntVal(0, ctx=ctx) for _ in range(4)]
        for binder_index, term in row_terms.items():
            replacement_by_index[binder_index] = term
        outer_guard = z3.And(*[
            z3.substitute_vars(atom, *replacement_by_index)
            for atom in outer_atoms
        ]) if outer_atoms else z3.BoolVal(True, ctx=ctx)

        array_sort = root.sort()
        if array_sort.domain().kind() != z3.Z3_INT_SORT:
            raise _Refuse("outer array index sort must be Int")
        row_sort = array_sort.range()
        if row_sort.kind() != z3.Z3_ARRAY_SORT or row_sort.domain().kind() != z3.Z3_INT_SORT:
            raise _Refuse("array must have two Int-indexed dimensions")
        row_left = row_terms[row_a]
        row_right = row_terms[row_b]
        one = z3.IntVal(1, ctx=ctx)
        zero = z3.IntVal(0, ctx=ctx)
        indicators = []
        for index_value in range(lower, upper):
            index_literal = z3.IntVal(index_value, ctx=ctx)
            read_left = z3.Select(z3.Select(root, row_left), index_literal)
            read_right = z3.Select(z3.Select(root, row_right), index_literal)
            indicators.append(z3.If(read_left == read_right, one, zero))
        total = z3.Sum(*indicators) if indicators else zero
        compact_body = z3.Implies(outer_guard, total <= one)
        rewritten = z3.ForAll([row_terms[row_a], row_terms[row_b]], compact_body)
        return AtMostOneRewrite(rewritten, True, "rewritten", lower, upper, estimate)
    except _Refuse as refusal:
        return AtMostOneRewrite(original, False, str(refusal))


def rewrite_top_level_and_conjuncts(formula, *, max_week_terms=256,
                                    max_generated_nodes=200000):
    """Rewrite eligible root-forall conjuncts under And nodes only.

    Traversal enters conjunction children and applies the root quantifier rule
    above. It does not cross Not, Or, Implies, or any other connective. If the
    aggregate node budget is exceeded, the exact original formula is returned
    with zero reported rewrites.
    """
    import z3

    if min(max_week_terms, max_generated_nodes) < 0:
        raise ValueError("resource limits must be nonnegative")
    memo = {}

    def visit(expression, remaining_budget):
        expression_id = expression.get_id()
        cached = memo.get(expression_id)
        if cached is not None and cached[0].eq(expression):
            cached_result = cached[1]
            # A cached result was charged when first visited. It can be shared
            # safely, but the caller counts each conjunct occurrence.
            if cached_result[3]:
                return expression, 0, 0, True
            if cached_result[2] > remaining_budget:
                return expression, 0, 0, True
            return cached_result

        if z3.is_and(expression):
            children = []
            total_count = 0
            total_estimate = 0
            for child in expression.children():
                rewritten, count, estimate, exhausted = visit(
                    child, remaining_budget - total_estimate)
                if exhausted:
                    result = (expression, 0, 0, True)
                    memo[expression_id] = (expression, result)
                    return result
                children.append(rewritten)
                total_count += count
                total_estimate += estimate
            result_expr = (z3.And(*children)
                           if total_count else expression)
            result = (result_expr, total_count, total_estimate, False)
        elif z3.is_quantifier(expression) and expression.is_forall():
            rewritten = rewrite_finite_pairwise_at_most_one(
                expression,
                max_week_terms=max_week_terms,
                max_generated_nodes=remaining_budget,
            )
            if not rewritten.rewritten:
                if "budget" in rewritten.reason:
                    result = (expression, 0, 0, True)
                else:
                    result = (expression, 0, 0, False)
            else:
                result = (rewritten.formula, 1,
                          rewritten.generated_node_estimate, False)
        else:
            # Deliberately stop at every connective except And.
            result = (expression, 0, 0, False)

        # Keep the input alive with the cached value because Z3 AST IDs can be
        # reused after temporary rewritten nodes are released.
        memo[expression_id] = (expression, result)
        return result

    rewritten, count, estimate, exhausted = visit(formula, max_generated_nodes)
    if exhausted:
        return ConjunctRewrite(formula, 0, 0, True)
    return ConjunctRewrite(rewritten, count, estimate, False)
