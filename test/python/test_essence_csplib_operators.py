"""Source-semantics checks for operators used by the published CSPLib models.

Savile Row manual sections 2.1.6, 2.1.9, 2.1.19, 3 and Appendix B.
No native reference compiler is assumed by these independent SMT checks.
"""
import itertools

import pytest
import somtparser as sp
import z3


def translate(declarations, expression):
    result = sp.translate(source="language ESSENCE' 1.0\n" + declarations +
                          "\nsuch that " + expression, language="essence")
    assert result.ok, [d.message for d in result.diagnostic_items]
    assert result.report.fidelity.sound and result.report.fidelity.complete
    solver = z3.Solver()
    solver.from_string(result.to_smt2())
    return solver


@pytest.mark.parametrize('operator', ['/', '%', 'div', 'mod'])
def test_floor_arithmetic_complete_small_signed_domain(operator):
    check = translate('find a,b: int(-4..4)\nfind q: int(-20..20)',
                      'q = a ' + operator + ' b')
    a, b, q = z3.Ints('a b q')
    for av, bv in itertools.product(range(-4, 5), repeat=2):
        check.push()
        check.add(a == av, b == bv)
        if bv == 0:
            assert check.check() == z3.unsat
        else:
            answer = av // bv if operator in ('/', 'div') else av % bv
            assert check.check() == z3.sat
            check.add(q != answer)
            assert check.check() == z3.unsat, (operator, av, bv)
        check.pop()


@pytest.mark.parametrize('expression,answer', [
    ('1 + true', 2), ('3 * false', 0), ('true - 2', -1),
    ('-true', -1), ('|false - true|', 1),
    ('sum([true, false, true])', 2), ('sum([true])', 1),
    ('sum i: int(1..3) . i != 2', 2),
    ('sum i: int(1..1) . i = 1', 1), ('true / true', 1),
])
def test_implicit_boolean_coercion_in_numeric_context(expression, answer):
    check = translate('find x: int(-10..10)', 'x = (' + expression + ')')
    assert check.check() == z3.sat
    check.add(z3.Int('x') != answer)
    assert check.check() == z3.unsat


@pytest.mark.parametrize('expression,answer', [
    ('2**3**2', 512), ('-2**2', -4), ('(-2)**2', 4),
    ('2**3 * 3', 24), ('2 * 3**2', 18), ('2**(1+2)', 8),
    ('true**2', 1), ('3**0', 1), ('(-3)**3', -27),
])
def test_power_associativity_precedence_and_integer_value(expression, answer):
    check = translate('find x: int(-1000..1000)', 'x = ' + expression)
    assert check.check() == z3.sat
    check.add(z3.Int('x') != answer)
    assert check.check() == z3.unsat


@pytest.mark.parametrize('expression,truth', [
    ('0**0 = 1', False), ('!(0**0 = 1)', True),
    ('0**0 != 1', False), ('catchUndef(0**0, 7) = 7', True),
    ('2**(-2) = 0', False), ('!(2**(-2) = 0)', True),
    ('catchUndef(2**(-2), 7) = 7', True),
    ('(0**0 = 1) + true = 1', True),
])
def test_power_partiality_closes_at_nearest_boolean(expression, truth):
    check = translate('', expression)
    assert (check.check() == z3.sat) == truth


def test_symbolic_base_zero_exponent_keeps_its_guard():
    check = translate('find x: int(-2..2)', 'x**0 = 1')
    for value in range(-2, 3):
        check.push()
        check.add(z3.Int('x') == value)
        assert (check.check() == z3.sat) == (value != 0)
        check.pop()


@pytest.mark.parametrize('expression,answer', [
    ('-2**2', -4), ('2**3**2', 512), ('(-3)/2', -2),
    ('3%(-2)', -1), ('true + 2', 3),
])
def test_parameter_arithmetic_uses_the_same_rules(expression, answer):
    check = translate('letting n be ' + expression + '\nfind x: int(-1000..1000)', 'x = n')
    assert check.check() == z3.sat
    check.add(z3.Int('x') != answer)
    assert check.check() == z3.unsat


@pytest.mark.parametrize('relation', [
    'table([x,y], [[1,2],[2,1]])',
    'table([x,y], T)',
])
def test_table_membership_is_exact_and_reifiable(relation):
    for negate in (False, True):
        check = translate('letting T = [[1,2],[2,1]]\nfind x,y: int(0..3)',
                          '!(' + relation + ')' if negate else relation)
        for xv, yv in itertools.product(range(4), repeat=2):
            check.push()
            check.add(z3.Int('x') == xv, z3.Int('y') == yv)
            expected = ((xv, yv) in {(1, 2), (2, 1)}) != negate
            assert (check.check() == z3.sat) == expected
            check.pop()


def test_table_boolean_scope_uses_zero_one_rows():
    check = translate('find a,b: bool', 'table([a,b], [[0,1],[1,0]])')
    for av, bv in itertools.product((False, True), repeat=2):
        check.push()
        check.add(z3.Bool('a') == av, z3.Bool('b') == bv)
        assert (check.check() == z3.sat) == (av != bv)
        check.pop()


def test_empty_table_is_false_even_under_negation():
    assert translate('find x: int(0..1)', 'table([x], [])').check() == z3.unsat
    assert translate('find x: int(0..1)', '!table([x], [])').check() == z3.sat


@pytest.mark.parametrize('expression', [
    'table([x,y], [[1],[2]])', 'table([x,y], [1,2])',
    'table([x,y], [[1,2],[3]])', 'table([x,y], [[x,y]])',
    '1 /\\ true', '!1', 'x ** y = 1',
])
def test_invalid_types_and_unsupported_variable_power_remain_explicit(expression):
    result = sp.translate(source="language ESSENCE' 1.0\nfind x,y: int(0..3)\nsuch that " +
                          expression, language='essence')
    assert not result.ok
    assert result.diagnostic_items


@pytest.mark.parametrize('spelling', ['allDiff', 'alldifferent'])
def test_alldifferent_alias_preserves_exact_relation(spelling):
    check = translate('find a: matrix indexed by [int(1..3)] of int(1..3)', spelling + '(a)')
    array = z3.Array('a', z3.IntSort(), z3.IntSort())
    for values in itertools.product(range(1, 4), repeat=3):
        check.push()
        check.add(*[z3.Select(array, i) == v for i, v in enumerate(values, 1)])
        assert (check.check() == z3.sat) == (len(set(values)) == 3)
        check.pop()


def test_legacy_csplib_implication_spelling_retains_false_antecedent():
    check = translate('find x: int(0..2)', '(x = 0) => table([x], [[1]])')
    for value in range(3):
        check.push()
        check.add(z3.Int('x') == value)
        assert (check.check() == z3.sat) == (value != 0)
        check.pop()


def _bounded_array(name, length, lower, upper):
    array = z3.Array(name, z3.IntSort(), z3.IntSort())
    cells = [z3.Select(array, i) for i in range(1, length + 1)]
    return cells, [z3.And(cell >= lower, cell <= upper) for cell in cells]


def _application_reference(name):
    if name == 'nqueens':
        x, clauses = _bounded_array('x', 8, 1, 8)
        return z3.And(*clauses, z3.Distinct(x),
                      z3.Distinct([v + i for i, v in enumerate(x, 1)]),
                      z3.Distinct([v - i for i, v in enumerate(x, 1)]))
    if name == 'all_interval':
        x, clauses = _bounded_array('x', 12, 1, 12)
        diffs, bounds = _bounded_array('diffs', 11, 1, 11)
        clauses += bounds + [z3.Distinct(x), z3.Distinct(diffs)]
        clauses += [diffs[i] == z3.Abs(x[i + 1] - x[i]) for i in range(11)]
        return z3.And(*clauses, x[0] < x[10], diffs[0] < diffs[1])
    if name == 'k4p2':
        nodes, clauses = _bounded_array('nodes', 8, 0, 16)
        edges, bounds = _bounded_array('edges', 16, 1, 16)
        pairs = [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3),
                 (4,5),(4,6),(4,7),(5,6),(5,7),(6,7),(0,4),(1,5),(2,6),(3,7)]
        clauses += bounds + [z3.Distinct(nodes), z3.Distinct(edges)]
        clauses += [edges[k] == z3.Abs(nodes[a] - nodes[b]) for k, (a, b) in enumerate(pairs)]
        return z3.And(clauses)
    if name == 'traffic_lights':
        vehicles, clauses = _bounded_array('V', 4, 1, 4)
        pedestrians, bounds = _bounded_array('P', 4, 1, 3)
        clauses += bounds + [z3.Or(p == 1, p == 3) for p in pedestrians]
        tuples = [(1,1,3,3), (2,1,4,1), (3,3,1,1), (4,1,2,1)]
        # Keep the original formal j=(1+i)%4 with i,j in1..4. Do not add an
        # extra edge merely because the surrounding prose describes a cycle.
        for i, j in itertools.product(range(1, 5), repeat=2):
            if j == (1 + i) % 4:
                scope = [vehicles[i-1], pedestrians[i-1], vehicles[j-1], pedestrians[j-1]]
                clauses.append(z3.Or(*[z3.And(*[v == c for v,c in zip(scope,t)]) for t in tuples]))
        return z3.And(clauses)
    if name == 'set_partition':
        a, clauses = _bounded_array('a', 16, 1, 2)
        sums, bounds = _bounded_array('sums', 2, 0, 16**2)
        squares, square_bounds = _bounded_array('sums_squared', 2, 0, 16**4)
        clauses += bounds + square_bounds
        for group in (1, 2):
            clauses += [sums[group-1] == z3.Sum([z3.If(v == group, i, 0) for i,v in enumerate(a, 1)]),
                        squares[group-1] == z3.Sum([z3.If(v == group, i*i, 0) for i,v in enumerate(a, 1)])]
        clauses += [z3.Sum([z3.If(v == 1, 1, 0) for v in a]) ==
                    z3.Sum([z3.If(v == 2, 1, 0) for v in a]),
                    sums[0] == sums[1], squares[0] == squares[1], a[0] == 1]
        return z3.And(clauses)
    raise AssertionError(name)


@pytest.mark.parametrize('name', ['all_interval', 'traffic_lights', 'set_partition', 'k4p2', 'nqueens'])
def test_complete_published_csplib_source_matches_independent_relation(name):
    from pathlib import Path
    source = (Path(__file__).resolve().parents[2] / 'languages/essence/instances/csplib' /
              (name + '.eprime')).read_text()
    result = sp.translate(source=source, language='essence')
    assert result.ok, [d.message for d in result.diagnostic_items]
    target = z3.And(list(z3.parse_smt2_string(result.to_smt2())))
    checker = z3.Solver()
    checker.set(timeout=0)
    checker.add(z3.Xor(target, _application_reference(name)))
    assert checker.check() == z3.unsat
