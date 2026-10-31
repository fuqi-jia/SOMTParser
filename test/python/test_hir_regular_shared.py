"""Automaton input sharing must preserve the language under every polarity."""
from _public_relation import public_relation
import itertools
import pytest
import z3
from somtparser import HirBuilder
from somtparser._nl_model import ModelError


def lit(n): return {'literal': n, 'sort': 'Int'}
def op(name, *args): return {'op': name, 'args': list(args)}


def accepted(word, start, finals, transitions):
    states = {start}
    for symbol in word:
        states = {c for a, b, c in transitions if a in states and b == symbol}
    return bool(states.intersection(finals))


def automaton(items, start=-4, finals=None, transitions=None):
    return dict(cp='regular', items=items, start=start, finals=[30] if finals is None else finals,
                transitions=[[-4, -3, 10], [-4, -3, 30], [10, 7, 30], [30, 9, 30], [10, 7, 30]]
                if transitions is None else transitions)


def formula(b):
    result = b.translate(); assert result.ok, [d.message for d in result.diagnostic_items]
    return public_relation(result)


@pytest.mark.parametrize('length', [0, 1, 2, 3])
@pytest.mark.parametrize('negated', [False, True])
def test_nondeterministic_path_matches_independent_word_enumeration(length, negated):
    b = HirBuilder()
    for i in range(length): b.declare(f'x{i}', 'Int')
    expr = automaton([{'var': f'x{i}'} for i in range(length)])
    b.constrain(op('not', expr) if negated else expr)
    xs = [z3.Int(f'x{i}') for i in range(length)]
    accepted_words = [z3.And(*[x == a for x, a in zip(xs, word)])
                      for word in itertools.product([-3, 7, 9], repeat=length)
                      if accepted(word, expr['start'], expr['finals'], expr['transitions'])]
    expected = z3.Or(*accepted_words)
    solver = z3.Solver(); solver.set(timeout=10000)
    # No input-domain restriction: arbitrary unlisted labels must be rejected.
    solver.add(z3.Xor(formula(b), z3.Not(expected) if negated else expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('length', [0, 1])
@pytest.mark.parametrize('finals', [[], [-4], [30]])
def test_empty_transition_and_final_sets(length, finals):
    b = HirBuilder(); expr = automaton([lit(-3)] * length, finals=finals, transitions=[])
    b.constrain(expr); s = z3.Solver(); s.add(formula(b))
    assert s.check() == (z3.sat if not length and -4 in finals else z3.unsat)


def test_repeated_relations_have_local_independent_witnesses():
    b = HirBuilder(); b.declare('x', 'Int')
    first = automaton([{'var': 'x'}], start=0, finals=[1], transitions=[[0, 2, 1]])
    second = automaton([{'var': 'x'}], start=8, finals=[9], transitions=[[8, 3, 9]])
    b.constrain(op('and', first, op('not', second)))
    solver = z3.Solver(); solver.add(z3.Xor(formula(b), z3.Int('x') == 2))
    assert solver.check() == z3.unsat


def test_regular_input_retains_outer_quantifier_binding_and_polarity():
    b = HirBuilder(); b.declare('x', 'Int')
    expr = automaton([{'var': 'x'}], start=0, finals=[1], transitions=[[0, 2, 1]])
    b.constrain({'quantifier': 'forall', 'binders': [{'name': 'x', 'sort': 'Int'}],
                 'body': op('eq', op('not', expr), op('ne', {'var': 'x'}, lit(2)))})
    solver = z3.Solver(); solver.set(timeout=10000)
    solver.add(z3.Not(formula(b)))
    assert solver.check() == z3.unsat


def test_table_read_is_compiled_once_per_automaton_input():
    b = HirBuilder(); b.declare('sequence', 'Int', shape=[200])
    b.data = {'requires': [[int((i+j) % 2 == 0) for j in range(5)] for i in range(24)]}
    items = [{'data': 'requires', 'indices': [{'at': 'sequence', 'indices': [lit(i)]}, lit(2)],
              'default': lit(0)} for i in range(200)]
    triples = [[a, symbol, (a+symbol) % 20] for a in range(20) for symbol in [0, 1]]
    b.expr(automaton(items, start=0, finals=list(range(20)), transitions=triples))
    assert b.nodes < 12000


def test_regular_rejects_bad_sorts_even_with_no_accepting_path():
    b = HirBuilder()
    with pytest.raises(ModelError, match='Int'):
        b.expr(automaton([{'literal': True, 'sort': 'Bool'}], finals=[]))
    with pytest.raises(ModelError, match='integer'):
        b.expr(automaton([], start=True))
    with pytest.raises(ModelError, match='length'):
        b.expr(automaton([], transitions=[[1, 2]]))
    with pytest.raises(ModelError, match='exact integer'):
        b.expr(automaton([], transitions=[[0, 10**512, 1]]))
