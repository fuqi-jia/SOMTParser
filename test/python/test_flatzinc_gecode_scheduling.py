"""Proven-domain Gecode aliases and exact registry cardinality boundaries."""
import pytest
import z3
import somtparser as sp


def equivalent(source, expected, profile='default'):
    result = sp.translate(source=source + '\nsolve satisfy;', language='flatzinc', profile=profile)
    assert result.ok, [diagnostic.message for diagnostic in result.diagnostic_items]
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(z3.And(*z3.parse_smt2_string(result.to_smt2())) != expected)
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('profile', ['default', 'ground', 'quantified'])
def test_cumulative_matches_independent_integer_time_load(profile):
    s0, s1, d0, d1, r0, r1, b = z3.Ints('s0 s1 d0 d1 r0 r1 b')
    values = (s0, s1, r0, r1)
    bounds = [z3.And(value >= 0, value <= 2) for value in values] + [d0 >= 1, d0 <= 2, d1 >= 1, d1 <= 2, b >= 0, b <= 3]
    # Independent time-grid oracle covers every possible active integer time
    # for starts/durations 0..2; production uses task-start event constraints.
    loads = [z3.Sum(*[z3.If(z3.And(s <= t, t < s + d), r, 0)
        for s, d, r in ((s0, d0, r0), (s1, d1, r1))]) <= b for t in range(5)]
    source = ''.join('var 0..2: ' + str(value) + ';' for value in values) + 'var 1..2: d0; var 1..2: d1; var 0..3: b;'
    source += 'constraint gecode_cumulatives([s0,s1],[d0,d1],[r0,r1],b);'
    equivalent(source, z3.And(*(bounds + loads)), profile)


@pytest.mark.parametrize('profile', ['default', 'ground', 'quantified'])
def test_strict_nooverlap_has_exact_coordinate_and_size_order(profile):
    x0, x1, y0, y1, w0, w1, h0, h1 = z3.Ints('x0 x1 y0 y1 w0 w1 h0 h1')
    positions = (x0, x1, y0, y1); sizes = (w0, w1, h0, h1)
    bounds = [z3.And(v >= -1, v <= 1) for v in positions]
    bounds += [z3.And(v >= 0, v <= 2) for v in sizes]
    relation = z3.Or(x0 + w0 <= x1, x1 + w1 <= x0, y0 + h0 <= y1, y1 + h1 <= y0)
    source = ''.join('var -1..1: ' + str(value) + ';' for value in positions)
    source += ''.join('var 0..2: ' + str(value) + ';' for value in sizes)
    source += 'constraint gecode_nooverlap([x0,x1],[w0,w1],[y0,y1],[h0,h1]);'
    equivalent(source, z3.And(*(bounds + [relation])), profile)


@pytest.mark.parametrize('call,expected', [
    ('gecode_cumulatives([],[],[],-1)', True),
    ('gecode_cumulatives([0],[0],[3],-1)', False),
    ('gecode_cumulatives([0],[0],[3],0)', False),
    ('gecode_cumulatives([0,2],[2,2],[3,3],3)', True),
    ('gecode_cumulatives([0,1],[2,2],[3,3],3)', False),
    ('gecode_nooverlap([],[],[],[])', True),
    ('gecode_nooverlap([0,1],[3,0],[0,1],[3,0])', False),
    ('gecode_nooverlap([0,3],[3,0],[0,1],[3,0])', True),
])
def test_empty_zero_extent_and_boundary_cases(call, expected):
    equivalent('constraint ' + call + ';', z3.BoolVal(expected))


@pytest.mark.parametrize('source', [
    'constraint gecode_cumulatives([0],[],[1],2);',
    'constraint gecode_cumulatives([],[],[],true);',
    'array[1..0] of bool: a = []; constraint gecode_cumulatives(a,[],[],0);',
    'constraint gecode_nooverlap([0],[1],[0],[]);',
    'constraint gecode_nooverlap([0],[true],[0],[1]);',
    'constraint gecode_nooverlap([0],[1],[0]);',
])
def test_mismatched_lengths_sorts_and_arity_are_rejected(source):
    result = sp.translate(source=source + 'solve satisfy;', language='flatzinc')
    assert not result.ok


@pytest.mark.parametrize('name,args,expected', [
    ('gecode_cumulatives', '[0,1],[2,2],[3,3],3', False),
    ('gecode_nooverlap', '[0,1],[3,0],[0,1],[3,0]', False),
])
def test_reification_keeps_entire_global_relation_inside_boolean(name, args, expected):
    equivalent('var bool: b; constraint ' + name + '_reif(' + args + ',b);', z3.Bool('b') == expected)


@pytest.mark.parametrize('source', [
    'constraint gecode_cumulatives([0,0],[0,1],[3,1],1);',
    'var int: d; constraint gecode_cumulatives([0,0],[d,1],[1,1],2);',
    'constraint gecode_cumulatives([0,0],[1,1],[-1,1],2);',
    'var int: w; constraint gecode_nooverlap([0,2],[w,1],[0,0],[1,1]);',
])
def test_unproven_vendor_domains_are_explicitly_refused(source):
    result = sp.translate(source=source + 'solve satisfy;', language='flatzinc')
    assert not result.ok
    assert any('requires declared' in d.message for d in result.diagnostic_items)


def test_singleton_preserves_registry_relation_without_duration_restriction():
    d, r, b = z3.Ints('d r b')
    equivalent('var int: d; var int: r; var int: b; '
        'constraint gecode_cumulatives([0],[d],[r],b);', r <= b)
