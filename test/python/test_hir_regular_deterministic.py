"""Exact DFA lowering compared with independent finite-language enumeration."""
from _public_relation import public_relation
import itertools

import pytest
import z3

from somtparser import HirBuilder
from test_hir_regular_shared import accepted, automaton, lit, op


def translated_formula(builder):
    result = builder.translate()
    assert result.ok, [diagnostic.message for diagnostic in result.diagnostic_items]
    script = result.to_smt2()
    return public_relation(result, script)


def has_quantifier(expr):
    pending = [expr]
    seen = set()
    while pending:
        node = pending.pop()
        if node.get_id() in seen:
            continue
        seen.add(node.get_id())
        if z3.is_quantifier(node):
            return True
        pending.extend(node.children())
    return False


def equivalent(left, right):
    solver = z3.Solver()
    solver.set(timeout=10000)
    solver.add(z3.Xor(left, right))
    assert solver.check() == z3.unsat, solver.reason_unknown()


# The second case prevents using a real state/final as the default sink. The
# third includes start/final states that never occur in the transition table.
CASES = [
    (-4, [30], [[-4, -3, 10], [10, 7, 30], [30, 9, 30]]),
    (0, [0, 1, 2], [[0, -3, 1], [1, 7, 2], [2, 9, 0]]),
    (0, [0, 1, 2], [[10, -3, 11], [11, 7, 10]]),
    (10**100, [-10**100], [[10**100, -3, -10**100],
                          [-10**100, 9, -10**100]]),
]


@pytest.mark.parametrize('start,finals,transitions', CASES)
@pytest.mark.parametrize('length', [0, 1, 3])
@pytest.mark.parametrize('negated', [False, True])
def test_deterministic_language_without_auxiliary_quantifiers(start, finals, transitions,
                                                             length, negated):
    builder = HirBuilder()
    for i in range(length):
        builder.declare(f'x{i}', 'Int')
    expr = automaton([{'var': f'x{i}'} for i in range(length)],
                     start=start, finals=finals, transitions=transitions)
    builder.constrain(op('not', expr) if negated else expr)
    actual = translated_formula(builder)
    assert not has_quantifier(actual)
    variables = [z3.Int(f'x{i}') for i in range(length)]
    words = [z3.And(*[var == value for var, value in zip(variables, word)])
             for word in itertools.product([-3, 7, 9], repeat=length)
             if accepted(word, start, finals, transitions)]
    expected = z3.Or(*words)
    # Equality is checked on unbounded Int inputs, including all labels absent
    # from the enumerated alphabet. Such words must reach the rejecting sink.
    equivalent(actual, z3.Not(expected) if negated else expected)


def test_identical_duplicate_edges_remain_deterministic():
    builder = HirBuilder()
    builder.declare('x', 'Int')
    expr = automaton([{'var': 'x'}], start=0, finals=[7, 7],
                     transitions=[[0, 3, 7], [0, 3, 7]])
    builder.constrain(expr)
    actual = translated_formula(builder)
    assert not has_quantifier(actual)
    equivalent(actual, z3.Int('x') == 3)


def test_distinct_targets_still_preserve_both_nondeterministic_paths():
    builder = HirBuilder()
    builder.declare('x', 'Int')
    expr = automaton([lit(1), {'var': 'x'}], start=0, finals=[3],
                     transitions=[[0, 1, 1], [0, 1, 2],
                                  [1, 7, 3], [2, 9, 3]])
    builder.constrain(expr)
    actual = translated_formula(builder)
    assert has_quantifier(actual)
    equivalent(actual, z3.Or(z3.Int('x') == 7, z3.Int('x') == 9))


def test_changed_table_does_not_change_a_previously_built_relation():
    builder = HirBuilder()
    builder.declare('x', 'Int')
    transitions = [[0, 1, 2]]
    first = automaton([{'var': 'x'}], start=0, finals=[2], transitions=transitions)
    builder.constrain(first)
    transitions[0][1] = 3
    second = automaton([{'var': 'x'}], start=0, finals=[2], transitions=transitions)
    builder.constrain(op('not', second))
    actual = translated_formula(builder)
    assert not has_quantifier(actual)
    equivalent(actual, z3.Int('x') == 1)


@pytest.mark.parametrize('length', [200, 1000])
def test_long_word_keeps_exact_missing_edge_semantics(length):
    builder = HirBuilder()
    builder.declare('x', 'Int')
    items = [lit(0) for _ in range(length)]
    items[length // 2] = {'var': 'x'}
    expr = automaton(items, start=0, finals=[7],
                     transitions=[[0, 0, 0], [0, 3, 7], [7, 0, 7]])
    builder.constrain(expr)
    actual = translated_formula(builder)
    assert not has_quantifier(actual)
    equivalent(actual, z3.Int('x') == 3)
