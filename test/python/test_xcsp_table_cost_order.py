"""Archive original tables, then use exact compaction in every proof path."""
import pytest
import z3

from tools.semantic_checks.source_oracles import xcsp_relation
from tools.semantic_checks.source_oracles.xcsp_source import Source


PAIRS = [(a, b) for a in range(4) for b in range(4) if a != b]


def instance(direction='minimize', private=False, mutation=None):
    x, y = z3.Ints('x y')
    domains = [z3.And(v >= 0, v <= 3) for v in (x, y)]
    table = z3.Or(*[z3.And(x == a, y == b) for a, b in PAIRS])
    objectives = [(direction, x), ('minimize', y + 1)] if direction else []
    source = Source({'x': x, 'y': y}, {'x': ((0, 3),), 'y': ((0, 3),)},
                    [*domains, table], objectives, 1, 'COP' if direction else 'CSP')
    pairs = list(PAIRS)
    if mutation == 'missing_tuple':
        pairs.remove((0, 1))
    if mutation == 'added_tuple':
        pairs.append((0, 0))
    body = '(or ' + ' '.join('(and (= a %d) (= b %d))' % pair for pair in pairs) + ')'
    definition = '(define-fun-rec f ((a Int) (b Int)) Bool ' + body + ')'
    constraints = '(assert (and (>= x 0) (<= x 3)))(assert (and (>= y 0) (<= y 3)))'
    constraints += '(assert true)' if mutation == 'missing_constraint' else '(assert (f x y))'
    first, second = 'x', '(+ y 1)'
    if mutation == 'offset':
        first = '(+ x 1)'
    elif mutation == 'sign':
        first = '(- x)'
    elif mutation == 'order':
        first, second = second, first
    costs = '(' + direction + ' ' + first + ')(minimize ' + second + ')' if direction else ''
    raw = ('(declare-const x Int)(declare-const y Int)' +
           ('(declare-const private_witness Bool)' if private else '') +
           definition + constraints + costs + '(check-sat)(exit)').encode()
    return source, raw


@pytest.mark.parametrize('direction', ['minimize', 'maximize', None])
@pytest.mark.parametrize('private', [False, True])
def test_compaction_precedes_first_proof_and_keeps_original_archive(monkeypatch, direction, private):
    source, raw = instance(direction, private)
    events = []
    compact = xcsp_relation.compact_literal_table_module
    prove = xcsp_relation.prove_complete_relation

    def archive(left, right):
        solver = z3.Solver(); solver.add(z3.Xor(left, right))
        text = solver.to_smt2()
        assert 'define-funs-rec' in text or 'define-fun-rec' in text
        context = z3.Context(); replay = z3.Solver(ctx=context)
        replay.from_string(text)
        assert replay.check() == z3.unsat
        events.append('archive')

    def compact_after_archive(module):
        assert events == ['archive']
        result, record = compact(module)
        assert record['applied']
        events.append('compact')
        return result, record

    def prove_without_opaque_tables(left, right):
        assert events[:2] == ['archive', 'compact']
        solver = z3.Solver(); solver.add(z3.Xor(left, right))
        text = solver.to_smt2()
        assert 'define-funs-rec' not in text and 'define-fun-rec' not in text
        events.append('proof')
        return prove(left, right)

    monkeypatch.setattr(xcsp_relation, 'compact_literal_table_module', compact_after_archive)
    monkeypatch.setattr(xcsp_relation, 'prove_complete_relation', prove_without_opaque_tables)
    result = xcsp_relation.compare(source, raw, solve=True, project_private_scalars=True,
                                   complete_relation_callback=archive)
    assert result['equivalent'] and result['literal_table_helpers']['applied']
    assert events.count('archive') == events.count('compact') == 1 and 'proof' in events
    if direction and not private:
        assert result['domain_cost_certificate']['equivalent'] is True
        assert result['composed_feasibility_certificate']['equivalent'] is True


@pytest.mark.parametrize('direction', ['minimize', 'maximize'])
@pytest.mark.parametrize('mutation', ['missing_tuple', 'added_tuple', 'missing_constraint',
                                     'offset', 'sign', 'order'])
def test_early_compaction_does_not_accept_changed_models(direction, mutation):
    source, raw = instance(direction, mutation=mutation)
    original_answers = []

    def archive(left, right):
        solver = z3.Solver(); solver.add(z3.Xor(left, right))
        text = solver.to_smt2()
        if mutation != 'missing_constraint':
            assert 'define-funs-rec' in text or 'define-fun-rec' in text
        context = z3.Context(); replay = z3.Solver(ctx=context)
        replay.from_string(text)
        original_answers.append(replay.check())

    result = xcsp_relation.compare(source, raw, solve=True, complete_relation_callback=archive)
    assert original_answers == [z3.sat]
    assert result['equivalent'] is False
