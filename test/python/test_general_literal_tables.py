"""Exact general finite tables: direction, loops, holes, scope and signed cost."""
import itertools

import pytest
import z3

from tools.semantic_checks import finite_table_helpers as tables
from tools.semantic_checks.closed_helpers import retain_closed_helpers
from tools.semantic_checks.source_oracles import xcsp_relation
from tools.semantic_checks.source_oracles.xcsp_source import Source


def number(n):
    return str(n) if n >= 0 else '(- ' + str(-n) + ')'


def definition(pairs, name='f', params=('a', 'b')):
    a, b = params
    terms = ['(and (= ' + a + ' ' + number(x) + ')(= ' + b + ' ' + number(y) + '))'
             for x, y in pairs]
    body = '(or ' + ' '.join(terms) + ')' if terms else 'false'
    return '(define-fun-rec ' + name + ' ((' + a + ' Int)(' + b + ' Int)) Bool ' + body + ')'


def relation(pairs, a, b):
    return z3.Or(*[z3.And(a == x, b == y) for x, y in pairs])


def parse(raw, context=None):
    target = z3.Optimize(ctx=context); target.from_string(raw.decode()); return target


def equal(a, b):
    solver = z3.Solver(ctx=a.ctx); solver.add(z3.Xor(a, b)); assert solver.check() == z3.unsat


UNIVERSE = list(itertools.product((0, 1), (0, 1, 3)))


@pytest.mark.parametrize('mask', range(1 << len(UNIVERSE)))
def test_every_relation_on_two_by_three_coordinates_includes_loops_and_direction(mask):
    pairs = {p for i, p in enumerate(UNIVERSE) if mask & (1 << i)}
    raw = (definition(sorted(pairs) * 2) + '(declare-const x Int)(declare-const y Int)(assert (f x y))').encode()
    compact, record = tables.compact_literal_table_module(raw)
    assert record['applied'] and record['helpers'][0]['tuples'] == len(pairs)
    assert record['helpers'][0]['complete_reconstruction_equal']
    x, y = z3.Ints('x y'); result = parse(compact).assertions()[0]
    # Complete integer-domain equivalence also rejects missing rows and columns.
    equal(result, relation(pairs, x, y)); equal(z3.Not(result), z3.Not(relation(pairs, x, y)))


@pytest.mark.parametrize('offset', [-10**40, -5, 10**40])
def test_grouping_merges_equal_neighbors_but_never_fills_integer_holes(offset):
    rows = (offset, offset+1, offset+3, offset+4)
    neighbors = (offset-9, offset-8, offset-2, offset+11)
    pairs = set(itertools.product(rows, neighbors)) | {(offset+7, offset+7)}
    raw = (definition(pairs) + '(declare-const x Int)(declare-const y Int)(assert (f x y))').encode()
    compact, record = tables.compact_literal_table_module(raw)
    helper = record['helpers'][0]
    assert record['applied'] and helper['representation'] == 'row-groups'
    assert len(helper['row_groups']) == 2
    assert {(a,b) for g in helper['row_groups'] for a in g['rows'] for b in g['columns']} == pairs
    equal(parse(compact).assertions()[0], relation(pairs, *z3.Ints('x y')))
    assert b'>=' in compact and b'<=' in compact


@pytest.mark.parametrize('params', [('a', 'b'), ('|ite|', '|not|'), ('|first row|', '|second;column|'),
                                  ('__somt_literal_column_0', '__somt_literal_column_1')])
def test_general_helpers_preserve_quantified_compound_repeated_and_shadowed_calls(params):
    pairs = {(0,0), (0,2), (1,2), (2,1), (2,2)}
    raw = (definition(pairs, params=params) +
           '(declare-const __somt_literal_column_0 Int)(declare-const __somt_literal_column_1 Int)'
           '(assert (exists ((x Int)) (and (f (+ __somt_literal_column_0 1) x)'
           '(f x x)(not (f x __somt_literal_column_1)))))').encode()
    original, _ = retain_closed_helpers(raw)
    compact, record = tables.compact_literal_table_module(original)
    assert record['applied'] and record['helpers'][0]['representation'] == 'row-groups'
    left, right = parse(original).assertions()[0], parse(compact).assertions()[0]
    equal(left, right)
    solver = z3.Solver(); solver.add(z3.Xor(left, right)); text = solver.to_smt2()
    context = z3.Context(); replay = z3.Solver(ctx=context); replay.from_string(text)
    assert replay.check() == z3.unsat


@pytest.mark.parametrize('mutation', ['missing_pair', 'added_pair', 'transposed'])
def test_changed_finite_table_remains_a_different_relation(mutation):
    pairs = {(0,0), (0,1), (1,3), (2,3)}
    changed = pairs - {(0,0)} if mutation == 'missing_pair' else pairs | {(2,2)} if mutation == 'added_pair' else {(b,a) for a,b in pairs}
    raw = (definition(changed) + '(declare-const x Int)(declare-const y Int)(assert (f x y))').encode()
    compact, record = tables.compact_literal_table_module(raw)
    assert record['applied']
    actual = parse(compact).assertions()[0]; x, y = z3.Ints('x y')
    equal(actual, relation(changed, x, y))
    solver = z3.Solver(); solver.add(z3.Xor(actual, relation(pairs, x, y)))
    assert solver.check() == z3.sat


@pytest.mark.parametrize('mutation', ['missing_pair', 'added_pair'])
def test_reconstruction_mismatch_keeps_the_entire_original_module(monkeypatch, mutation):
    pairs = {(0,0), (0,1), (1,3), (2,3)}
    planner = tables.plan_literal_rows
    wrong = pairs - {(0,0)} if mutation == 'missing_pair' else pairs | {(1,1)}
    monkeypatch.setattr(tables, 'plan_literal_rows', lambda original: planner(wrong))
    raw = (definition(pairs) + '(declare-const x Int)(declare-const y Int)(assert (f x y))').encode()
    compact, record = tables.compact_literal_table_module(raw)
    assert compact == raw and not record['applied'] and record['helpers'] == []
    assert 'reconstructed tuple set differs' in record['fallback_reason']


@pytest.mark.parametrize('direction', ['minimize', 'maximize'])
@pytest.mark.parametrize('private', [False, True])
def test_multiple_general_tables_keep_original_query_scopes_and_ordered_signed_cost(direction, private):
    pairs = {(a,b) for a in range(2,10) for b in range(2,10) if a % 2 or b % 2}
    second = {(2,2), (2,3), (3,2), (4,9)}
    x, y = z3.Ints('x y'); bounds = [z3.And(v >= 2, v <= 9) for v in (x,y)]
    constraints = [*bounds, relation(pairs,x,y), z3.Not(relation(second,y,x))]
    cost = x + z3.If(relation(second,x,y),3,7)
    source = Source({'x':x,'y':y}, {'x':((2,9),),'y':((2,9),)}, constraints,
                    [(direction,cost),('maximize',y)], 2, 'COP')
    raw = (definition(pairs) + definition(second,name='g') + '(declare-const x Int)(declare-const y Int)' +
           ('(declare-const witness Bool)' if private else '') +
           '(assert (and (>= x 2)(<= x 9)))(assert (and (>= y 2)(<= y 9)))'
           '(assert (f x y))(assert (not (g y x)))' +
           '('+direction+' (+ x (ite (g x y) 3 7)))(maximize y)(check-sat)(exit)').encode()
    archived = []
    def archive(left,right):
        solver = z3.Solver(); solver.add(z3.Xor(left,right)); text=solver.to_smt2()
        assert 'define-funs-rec' in text or 'define-fun-rec' in text
        context=z3.Context(); replay=z3.Solver(ctx=context); replay.from_string(text)
        assert replay.check()==z3.unsat; archived.append(text)
    result=xcsp_relation.compare(source,raw,solve=True,project_private_scalars=True,complete_relation_callback=archive)
    assert result['equivalent'] and result['signed_cost_equal'] and len(archived)==1
    helpers=result['literal_table_helpers']['helpers']
    assert len(helpers)==2 and all(h['representation']=='row-groups' for h in helpers)
