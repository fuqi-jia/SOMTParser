"""Finite data snapshots preserve total lookup, typing, scope and mutation."""
from fractions import Fraction
import pytest
import z3
from somtparser import HirBuilder, hir_api
from somtparser._nl_model import ModelError


def lit(value, sort='Int'):
    return {'literal': value, 'sort': sort}


def var(name):
    return {'var': name}


def op(name, *args):
    return {'op': name, 'args': list(args)}


def lookup(name, indices, default):
    return {'data': name, 'indices': indices, 'default': default}


def formula(builder):
    result = builder.translate()
    assert result.ok, [d.message for d in result.diagnostic_items]
    return z3.And(*z3.parse_smt2_string(result.to_smt2()))


def same(actual, expected):
    solver = z3.Solver(); solver.set(timeout=10000)
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('sort,table,default', [
    ('Int', [[3, -5], [10**24, 7]], -11),
    ('Bool', [[True, False], [False, True]], False),
    ('Real', [['1/3', '-2.5'], ['7/11', '0']], '9/2'),
])
@pytest.mark.parametrize('fixed_axis', [None, 0, 1])
def test_total_multidimensional_lookup_matches_exact_cases(sort, table, default, fixed_axis):
    b = HirBuilder(); b.data = {'t': table}
    for name in ['i', 'j']: b.declare(name, 'Int')
    b.declare('r', sort)
    indices = [lit(1) if fixed_axis == k else var(name) for k, name in enumerate(['i', 'j'])]
    b.constrain(op('eq', var('r'), lookup('t', indices, lit(default, sort))))
    i, j = z3.Ints('i j'); args = [1 if fixed_axis == 0 else i, 1 if fixed_axis == 1 else j]
    zv = lambda v: z3.BoolVal(v) if sort == 'Bool' else z3.IntVal(v) if sort == 'Int' else z3.RealVal(str(Fraction(v)))
    expected = zv(default)
    for row in range(2):
        for col in range(2):
            expected = z3.If(z3.And(args[0] == row, args[1] == col), zv(table[row][col]), expected)
    r = z3.Bool('r') if sort == 'Bool' else z3.Int('r') if sort == 'Int' else z3.Real('r')
    same(formula(b), r == expected)


def test_mutation_does_not_reuse_an_old_data_value_or_sort():
    b = HirBuilder(); b.declare('i', 'Int'); b.declare('old', 'Int'); b.declare('new', 'Int')
    b.data = {'t': [2, 3]}
    expr = lookup('t', [var('i')], lit(-1))
    b.constrain(op('eq', var('old'), expr))
    b.data['t'][0] = 9
    b.constrain(op('eq', var('new'), expr))
    i = z3.Int('i')
    same(formula(b), z3.And(z3.Int('old') == z3.If(i == 0, 2, z3.If(i == 1, 3, -1)),
                            z3.Int('new') == z3.If(i == 0, 9, z3.If(i == 1, 3, -1))))
    b.data['t'][0] = True
    with pytest.raises(ModelError, match='one exact scalar sort'):
        b.expr(expr)


def test_cached_values_do_not_capture_default_or_quantifier_binding():
    b = HirBuilder(); b.data = {'t': [3, 5]}
    b.declare('i', 'Int'); b.declare('r', 'Int')
    b.expr(lookup('t', [var('i')], lit(77)))
    b.constrain({'quantifier': 'forall', 'binders': [{'name': 'i', 'sort': 'Int'}],
                 'body': op('eq', lookup('t', [var('i')], var('i')),
                            op('ite', op('eq', var('i'), lit(0)), lit(3),
                               op('ite', op('eq', var('i'), lit(1)), lit(5), var('i'))))})
    same(formula(b), z3.BoolVal(True))


def test_same_flattened_values_keep_each_shape_and_axis_bounds():
    b = HirBuilder(); b.data = {'matrix': [[2, 4], [6, 8]], 'vector': [2, 4, 6, 8]}
    b.declare('i', 'Int'); b.declare('j', 'Int'); b.declare('a', 'Int'); b.declare('v', 'Int')
    b.constrain(op('eq', var('a'), lookup('matrix', [var('i'), var('j')], lit(-1))))
    b.constrain(op('eq', var('v'), lookup('vector', [op('add', op('mul', lit(2), var('i')), var('j'))], lit(-1))))
    i, j, a, v = z3.Ints('i j a v')
    solver = z3.Solver(); solver.add(formula(b), i == 0, j == 2)
    assert solver.check() == z3.sat
    assert solver.model().eval(a).as_long() == -1
    assert solver.model().eval(v).as_long() == 6


@pytest.mark.parametrize('bad', [[[1], [2, 3]], [[1], [False]]])
def test_fixed_lookup_still_validates_unvisited_table_cells(bad):
    b = HirBuilder(); b.data = {'t': bad}
    with pytest.raises(ModelError):
        b.expr(lookup('t', [lit(0), lit(0)], lit(-1)))


def test_repeated_data_queries_share_native_table_construction():
    b = HirBuilder(); b.declare('i', 'Int'); b.data = {'t': [[j + 7*k for j in range(7)] for k in range(100)]}
    for _ in range(500):
        b.expr(lookup('t', [var('i'), lit(3)], lit(-1)))
    assert b.nodes < 10000
    assert len(b._data_arrays) == 1


def test_constant_array_constructor_retains_scoped_values_and_index_sorts():
    assert 'constant_array' in hir_api()['constructors']
    b = HirBuilder(); b.declare('value', 'Int'); b.declare('key', 'Bool')
    array = {'const_array': {'index_sort': 'Bool', 'value': var('value')}}
    b.constrain(op('eq', op('select', array, var('key')), var('value')))
    same(formula(b), z3.BoolVal(True))
    with pytest.raises(ModelError):
        b.expr({'const_array': {'index_sort': 'Missing', 'value': lit(1)}})


def test_constant_array_value_is_bound_inside_its_quantifier():
    b = HirBuilder(); b.declare('value', 'Int')
    array = {'const_array': {'index_sort': 'Int', 'value': var('value')}}
    b.constrain({'quantifier': 'forall', 'binders': [{'name': 'value', 'sort': 'Int'}],
                 'body': op('eq', op('select', array, lit(5)), var('value'))})
    same(formula(b), z3.BoolVal(True))
