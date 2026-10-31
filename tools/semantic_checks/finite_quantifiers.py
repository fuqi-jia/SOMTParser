"""Strict finite expansion for a small, provable fragment of Z3 quantifiers.

This helper only rewrites Int quantifiers with a direct implication/and guard whose top-level
conjuncts prove a finite interval for every bound variable. Unsupported shapes
are returned unchanged. Z3 is imported lazily so importing this module does
not initialize any solver runtime.
"""
from dataclasses import dataclass
from itertools import product


@dataclass(frozen=True)
class ExpansionStats:
    expanded_quantifiers: int
    expanded_instances: int
    enumerated_tuples: int
    skipped_quantifiers: int
    budget_exhausted: bool
    unchanged_reasons: tuple


@dataclass(frozen=True)
class ExpansionResult:
    formula: object
    stats: ExpansionStats


class _BudgetExceeded(Exception):
    pass


class _Unsupported(Exception):
    pass


def _and_conjuncts(z3, expression):
    result = []
    stack = [expression]
    while stack:
        node = stack.pop()
        if z3.is_and(node):
            stack.extend(reversed(node.children()))
        else:
            result.append(node)
    return result


def _integer_numeral(z3, expression):
    if z3.is_int_value(expression):
        return expression.as_long()
    return None


def _var_index(z3, expression):
    return z3.get_var_index(expression) if z3.is_var(expression) else None


def _infer_intervals(z3, quantifier, guard):
    """Infer inclusive bounds from conjunctive integer comparisons.

    Supported atoms are x <[=] integer, integer <[=] x and x <[=] y,
    including reversed operands. Pairwise order constraints propagate bounds
    to a fixed point. Any other conjunct is harmless and ignored as an
    additional restriction; it does not contribute a bound.
    """
    count = quantifier.num_vars()
    if count == 0:
        raise _Unsupported("zero-variable quantifier")
    domains = {}
    for declaration_index in range(count):
        if quantifier.var_sort(declaration_index).kind() != z3.Z3_INT_SORT:
            raise _Unsupported("non-Int bound variable")
        # SMT de Bruijn index zero denotes the last variable in the binder.
        domains[count - declaration_index - 1] = [None, None]

    relations = []
    op_to_relation = {
        z3.Z3_OP_LT: ("lt", True),
        z3.Z3_OP_LE: ("le", False),
        z3.Z3_OP_GT: ("gt", True),
        z3.Z3_OP_GE: ("ge", False),
    }
    for atom in _and_conjuncts(z3, guard):
        if not z3.is_app(atom) or atom.num_args() != 2:
            continue
        relation_info = op_to_relation.get(atom.decl().kind())
        if relation_info is None:
            continue
        relation, strict = relation_info
        lhs, rhs = atom.children()
        li, ri = _var_index(z3, lhs), _var_index(z3, rhs)
        lv, rv = _integer_numeral(z3, lhs), _integer_numeral(z3, rhs)

        # Normalize all inequalities to a relation in the direction x <= y.
        if relation in {"gt", "ge"}:
            lhs, rhs, li, ri, lv, rv = rhs, lhs, ri, li, rv, lv
            relation = "lt" if relation == "gt" else "le"
        is_strict = strict
        if li in domains and rv is not None:
            lo, hi = domains[li]
            if relation in {"lt", "le"}:
                candidate = rv - (1 if is_strict else 0)
                domains[li][1] = candidate if hi is None else min(hi, candidate)
            else:  # normalized `constant <= x`
                candidate = rv + (1 if is_strict else 0)
                domains[li][0] = candidate if lo is None else max(lo, candidate)
            continue
        if lv is not None and ri in domains:
            lo, hi = domains[ri]
            # Original `constant <[=] x` gives a lower bound on x.
            candidate = lv + (1 if is_strict else 0)
            domains[ri][0] = candidate if lo is None else max(lo, candidate)
            continue
        if li in domains and ri in domains and li != ri:
            relations.append((li, ri, is_strict))

    # Propagate necessary bounds along x <[=] y. A bounded chain can make
    # every variable finite even when only one endpoint has an explicit bound.
    changed = True
    rounds = 0
    while changed and rounds <= count:
        changed = False
        rounds += 1
        for left, right, strict in relations:
            lo_l, hi_l = domains[left]
            lo_r, hi_r = domains[right]
            delta = 1 if strict else 0
            if hi_r is not None:
                value = hi_r - delta
                if hi_l is None or value < hi_l:
                    domains[left][1] = value
                    changed = True
            if lo_l is not None:
                value = lo_l + delta
                if lo_r is None or value > lo_r:
                    domains[right][0] = value
                    changed = True
    if changed:
        raise _Unsupported("cyclic inequalities do not yield stable finite bounds")

    if any(lower is None or upper is None
           for lower, upper in domains.values()):
        raise _Unsupported("guard does not prove finite bounds for every variable")
    return domains


def _guard_and_body(z3, quantifier):
    body = quantifier.body()
    if quantifier.is_forall():
        if not z3.is_implies(body) or body.num_args() != 2:
            raise _Unsupported("forall body is not a direct implication")
        return "forall", body.arg(0), body.arg(1)
    if quantifier.is_exists():
        if not z3.is_and(body):
            raise _Unsupported("exists body is not a direct conjunction")
        parts = list(body.children())
        if not parts:
            raise _Unsupported("empty exists conjunction")
        return "exists", z3.And(*parts), z3.BoolVal(True, ctx=quantifier.ctx)
    raise _Unsupported("unsupported quantifier kind")


def _replace_bound_vars(z3, body, declaration_values):
    # Z3's substitute_vars maps arguments to de Bruijn indices 0..n-1.
    values = [z3.IntVal(value, ctx=body.ctx) for value in declaration_values]
    return z3.substitute_vars(body, *reversed(values))


def _mk_and(z3, expressions, ctx):
    expressions = list(expressions)
    return z3.And(*expressions) if expressions else z3.BoolVal(True, ctx=ctx)


def _mk_or(z3, expressions, ctx):
    expressions = list(expressions)
    return z3.Or(*expressions) if expressions else z3.BoolVal(False, ctx=ctx)


def _dag_size(z3, expression):
    seen = set()
    stack = [expression]
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


def _closed_int_index(z3, expression, cache):
    """Canonicalize a closed Int arithmetic index, retaining every other term.

    Quantifier instantiation leaves indices such as ``(+ 1 0)`` in the DAG.
    Array projection matches numeral reads, so those exact constants must be
    represented as numerals before its complete-root disappearance check.
    Z3 evaluates the arithmetic; Python division/remainder conventions are
    never used. In particular, division by zero and any non-numeral result
    retain their original term. Function applications are never unfolded.
    """
    arithmetic = (z3.Z3_OP_ADD, z3.Z3_OP_SUB, z3.Z3_OP_MUL, z3.Z3_OP_UMINUS,
                  z3.Z3_OP_IDIV, z3.Z3_OP_MOD, z3.Z3_OP_REM)
    stack = [(expression, False)]
    while stack:
        current, ready = stack.pop()
        key = current.get_id()
        if key in cache:
            continue
        if (z3.is_int_value(current) or not z3.is_app(current)
                or current.sort().kind() != z3.Z3_INT_SORT
                or current.decl().kind() not in arithmetic):
            cache[key] = (current, current)
            continue
        children = current.children()
        if not ready:
            stack.append((current, True))
            stack.extend((child, False) for child in children)
            continue
        values = [cache[child.get_id()][1] for child in children]
        result = current
        if all(z3.is_int_value(value) for value in values):
            zero_divisor = (current.decl().kind() in
                            (z3.Z3_OP_IDIV, z3.Z3_OP_MOD, z3.Z3_OP_REM)
                            and len(values) == 2 and values[1].as_long() == 0)
            if not zero_divisor:
                simplified = z3.simplify(current.decl()(*values))
                if z3.is_int_value(simplified):
                    result = simplified
        # Retain source nodes as well as results: Z3 may reuse released AST ids.
        cache[key] = (current, result)
    return cache[expression.get_id()][1]


def expand_finite_int_quantifiers(formula, *, max_enumerated_tuples=50000,
                                  max_emitted_instances=5000,
                                  max_ast_nodes=2000000):
    """Expand only quantifiers with provably finite Int domains.

    Resource use is counted across the whole formula. If any limit is crossed,
    the exact original formula is returned, so callers never receive a partial
    rewrite. Unsupported quantifiers remain intact and are reported.

    The only accepted quantified shapes are ``forall vars. guard => body``
    and ``exists vars. and(guard, body...)``. Bounds come solely from a
    conjunctive guard of Int comparisons. Every guard-satisfying tuple is
    included; tuples violating the guard are removed only after Z3 simplifies
    that ground guard to false. Closed Int arithmetic indices in instantiated
    scalar or nested array reads are normalized with Z3's exact arithmetic
    semantics. Symbolic indices, undefined arithmetic and function applications
    remain unchanged; no array cell or other assertion is discarded.
    """
    import z3

    if min(max_enumerated_tuples, max_emitted_instances, max_ast_nodes) < 0:
        raise ValueError("resource limits must be nonnegative")
    counters = {"expanded": 0, "instances": 0, "tuples": 0,
                "estimated_nodes": 0, "skipped": 0, "reasons": []}
    memo = {}
    index_cache = {}

    def rewrite(expression, canonicalize_indices=False):
        # Keep ordinary unexpanded input unchanged. The same source subterm
        # can occur both inside an instance and elsewhere in the formula.
        expression_id = (expression.get_id(), canonicalize_indices)
        cached = memo.get(expression_id)
        if cached is not None:
            # Keep the source node alive alongside its rewritten node. Z3 AST
            # ids are context-local and may be reused after a temporary AST is
            # released, so an id-only cache must own the original expression.
            return cached[1]
        if z3.is_quantifier(expression):
            try:
                polarity, guard, quantified_body = _guard_and_body(z3, expression)
                intervals = _infer_intervals(z3, expression, guard)
                declaration_domains = []
                for declaration_index in range(expression.num_vars()):
                    debruijn = expression.num_vars() - declaration_index - 1
                    lower, upper = intervals[debruijn]
                    if lower > upper:
                        declaration_domains.append((lower, upper, ()))
                    else:
                        declaration_domains.append(
                            (lower, upper, range(lower, upper + 1)))
                tuple_count = 1
                for lower, upper, _domain in declaration_domains:
                    width = max(0, upper - lower + 1)
                    tuple_count *= width
                if tuple_count > max_enumerated_tuples - counters["tuples"]:
                    raise _BudgetExceeded("enumerated tuple budget")
                counters["tuples"] += tuple_count
                if tuple_count == 0:
                    # itertools.product materializes each input iterable before
                    # yielding tuples. Avoid passing it an empty range beside
                    # a potentially enormous range: the Cartesian product is
                    # already known to be empty from the integer widths.
                    result = z3.BoolVal(polarity == "forall", ctx=expression.ctx)
                    counters["expanded"] += 1
                    memo[expression_id] = (expression, result)
                    return result

                selected_values = []
                for values in product(*(domain for _lo, _hi, domain
                                        in declaration_domains)):
                    instantiated_guard = _replace_bound_vars(z3, guard, values)
                    simplified_guard = z3.simplify(instantiated_guard)
                    if z3.is_false(simplified_guard):
                        continue
                    if len(selected_values) >= max_emitted_instances - counters["instances"]:
                        raise _BudgetExceeded("emitted instance budget")
                    selected_values.append((values, simplified_guard))
                estimated = len(selected_values) * _dag_size(z3, quantified_body)
                if estimated > max_ast_nodes - counters["estimated_nodes"]:
                    raise _BudgetExceeded("estimated output AST budget")
                counters["estimated_nodes"] += estimated
                # Reserve all current-level instances before descending. This
                # makes nested expansions see the parent's pending work.
                counters["instances"] += len(selected_values)

                retained = []
                for values, simplified_guard in selected_values:
                    instantiated_body = _replace_bound_vars(z3, quantified_body, values)
                    transformed_body = yield instantiated_body, True
                    if polarity == "forall":
                        # Keep a residual ground guard if it did not simplify
                        # completely; this preserves exact implication meaning.
                        retained.append(
                            transformed_body if z3.is_true(simplified_guard)
                            else z3.Implies(simplified_guard, transformed_body))
                    else:
                        retained.append(
                            simplified_guard if z3.is_true(transformed_body)
                            else z3.And(simplified_guard, transformed_body))
                counters["expanded"] += 1
                result = (_mk_and(z3, retained, expression.ctx)
                          if polarity == "forall"
                          else _mk_or(z3, retained, expression.ctx))
                memo[expression_id] = (expression, result)
                return result
            except _Unsupported as error:
                counters["skipped"] += 1
                counters["reasons"].append(str(error))
                memo[expression_id] = (expression, expression)
                return expression

        if z3.is_app(expression) and expression.num_args():
            original_children = expression.children()
            children = []
            for child in original_children:
                children.append((yield child, canonicalize_indices))
            if canonicalize_indices and z3.is_select(expression):
                children = [children[0]] + [_closed_int_index(z3, index, index_cache)
                                           for index in children[1:]]
            if all(old.eq(new) for old, new in zip(original_children, children)):
                memo[expression_id] = (expression, expression)
                return expression
            result = expression.decl()(*children)
            memo[expression_id] = (expression, result)
            return result
        memo[expression_id] = (expression, expression)
        return expression

    def visit(expression):
        # Drive suspended rewrites explicitly: both ordinary DAG depth and
        # nested finite binders can exceed Python's call-stack limit. Each
        # frame resumes in the original left-to-right order, so budget
        # reservations, memo ownership and unsupported-binder behavior stay
        # identical to the recursive traversal.
        frames = [rewrite(expression)]
        value = None
        try:
            while frames:
                try:
                    child, canonicalize_indices = frames[-1].send(value)
                except StopIteration as completed:
                    frames.pop()
                    value = completed.value
                    continue
                cached = memo.get((child.get_id(), canonicalize_indices))
                if cached is not None:
                    value = cached[1]
                else:
                    frames.append(rewrite(child, canonicalize_indices))
                    value = None
            return value
        finally:
            # On any budget exception release suspended work without trying
            # to finish it; the caller returns the original entire formula.
            for frame in reversed(frames):
                frame.close()

    try:
        rewritten = visit(formula)
        # Bound output DAG growth as well. This is post-construction, but an
        # over-budget result is discarded wholesale and the original returned.
        seen = set()
        stack = [rewritten]
        while stack:
            node = stack.pop()
            node_id = node.get_id()
            if node_id in seen:
                continue
            seen.add(node_id)
            if len(seen) > max_ast_nodes:
                raise _BudgetExceeded("AST node budget")
            if z3.is_quantifier(node):
                stack.append(node.body())
            elif z3.is_app(node):
                stack.extend(node.children())
    except _BudgetExceeded as error:
        return ExpansionResult(formula, ExpansionStats(
            0, 0, counters["tuples"], counters["skipped"], True,
            tuple(counters["reasons"] + [str(error)])))

    return ExpansionResult(rewritten, ExpansionStats(
        counters["expanded"], counters["instances"], counters["tuples"],
        counters["skipped"], False, tuple(counters["reasons"])))
