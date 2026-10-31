"""Prove redundant bounds for finite histogram expressions in a full target.

No source-model names or expected optima are used. Every leaf partition is
proved from actual top-level target constraints; exact integer regrouping is
checked independently; the abstract arithmetic bound is proved by Z3. A lemma
is returned only after all these obligations are UNSAT/identically true. The
caller keeps every original assertion in the final no-better query.
"""
from collections import Counter
import z3


def walk(root):
    pending = [root]
    seen = set()
    while pending:
        term = pending.pop()
        if term.get_id() in seen:
            continue
        seen.add(term.get_id())
        yield term
        if z3.is_app(term):
            pending.extend(term.children())


def conjuncts(assertions):
    pending = list(assertions)
    while pending:
        term = pending.pop()
        if z3.is_and(term):
            pending.extend(term.children())
        else:
            yield term


def coordinate(term):
    return (term.sort().kind() == z3.Z3_INT_SORT
            and ((z3.is_const(term) and not z3.is_int_value(term)) or z3.is_select(term)))


def histogram(term):
    if not z3.is_add(term) or term.num_args() < 2:
        return None
    cells, color = [], None
    for indicator in term.children():
        if (not z3.is_app_of(indicator, z3.Z3_OP_ITE)
                or not z3.is_int_value(indicator.arg(1)) or indicator.arg(1).as_long() != 1
                or not z3.is_int_value(indicator.arg(2)) or indicator.arg(2).as_long() != 0):
            return None
        comparison = indicator.arg(0)
        if not z3.is_eq(comparison):
            return None
        left, right = comparison.children()
        if z3.is_int_value(right):
            left, right = right, left
        if not z3.is_int_value(left) or not coordinate(right):
            return None
        value = left.as_long()
        if color is not None and value != color:
            return None
        color = value
        cells.append(right)
    return color, cells


def prove(assertions, record):
    """record(kind, assumptions, conclusion, answer) retains every obligation."""
    flat = list(conjuncts(assertions))
    domains = {}
    for term in flat:
        if not z3.is_app(term) or term.decl().kind() not in (
                z3.Z3_OP_GE, z3.Z3_OP_LE, z3.Z3_OP_GT, z3.Z3_OP_LT, z3.Z3_OP_EQ):
            continue
        if term.num_args() != 2:
            continue
        a, b = term.children()
        if z3.is_int_value(a):
            a, b = b, a
        if coordinate(a) and z3.is_int_value(b):
            domains.setdefault(a.get_id(), []).append(term)

    # AST roots remain owned by `assertions`; IDs are context-local only.
    partition_cache = {}
    lemmas = []
    for equality in flat:
        if not z3.is_eq(equality):
            continue
        output, expression = equality.children()
        if not coordinate(output):
            output, expression = expression, output
        if not coordinate(output) or not z3.is_arith(expression):
            continue
        candidates = []
        for term in walk(expression):
            parsed = histogram(term)
            if parsed is not None:
                candidates.append((term, *parsed))
        if len(candidates) < 2:
            continue
        colors = [color for _, color, _ in candidates]
        if len(set(colors)) != len(colors):
            continue
        cells = candidates[0][2]
        multiplicities = Counter(cell.get_id() for cell in cells)
        if any(Counter(cell.get_id() for cell in other) != multiplicities
               for _, _, other in candidates):
            continue
        partitions = []
        accepted = True
        for cell in {cell.get_id(): cell for cell in cells}.values():
            domain = domains.get(cell.get_id(), [])
            key = cell.get_id(), tuple(sorted(colors))
            partition = z3.Sum([z3.If(cell == color, 1, 0) for color in colors]) == 1
            if key not in partition_cache:
                solver = z3.Solver()
                solver.add(*domain, z3.Not(partition))
                answer = solver.check()
                record('cell-partition', domain, partition, str(answer))
                partition_cache[key] = answer == z3.unsat
            if not partition_cache[key]:
                accepted = False
                break
            partitions.append(partition)
        if not accepted:
            continue
        counts = [term for term, _, _ in candidates]
        transposed = z3.Sum([z3.Sum([z3.If(cell == color, 1, 0) for color in colors])
                             for cell in cells])
        regrouping = z3.Sum(counts) == transposed
        simplified = z3.simplify(regrouping, som=True, arith_lhs=True)
        record('integer-regrouping', [], regrouping, 'true' if z3.is_true(simplified) else 'unknown')
        if not z3.is_true(simplified):
            continue
        # A fresh symbol per complete histogram expression is a sound
        # abstraction even if the target contains additional dependencies.
        fresh = [z3.FreshInt('histogram') for _ in counts]
        abstract = z3.substitute(expression, *zip(counts, fresh))
        lower = 1 if len(cells) % len(colors) else 0
        assumption = z3.Sum(fresh) == len(cells)
        conclusion = abstract >= lower
        solver = z3.Solver()
        solver.add(assumption, z3.Not(conclusion))
        answer = solver.check()
        record('abstract-integer-bound', [assumption], conclusion, str(answer))
        if answer != z3.unsat:
            continue
        lemma = output >= lower
        lemmas.append(lemma)
        record('derived-target-bound', [equality, *partitions, regrouping], lemma,
               'proved-by-partition-regrouping-and-integer-abstraction')
    return lemmas
