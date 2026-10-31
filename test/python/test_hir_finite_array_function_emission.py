"""Bounded array-read macros expose cells without disabling function sharing."""
import pytest
import z3

from somtparser import _somtparser as native
from somtparser.hir import HirBuilder
from tools.semantic_checks.projection import (
    free_constants,
    optimize_observation_projection,
)


INT = native.HirSort.integer()
ARRAY = native.HirSort.array(INT, INT)


def literal(value):
    return native._hir_literal(INT, str(value))


def op(name, *args):
    return native._hir_op(name, list(args))


def bound(name, sort=INT):
    return native._hir_ident(name, sort, True)


def count_body(array, count=200, index_for=None):
    terms = []
    for index in range(count):
        at = literal(index) if index_for is None else index_for(index)
        terms.append(op('ite', op('eq', op('select', array, at), bound('tag')),
                        literal(1), literal(0)))
    return op('add', *terms)


def declare_count(model, name='count', count=200):
    model.declare_function(name, [ARRAY, INT], INT)
    model.define_function(name, [('a', ARRAY), ('tag', INT)],
                          count_body(bound('a', ARRAY), count))


def script_for(model):
    result = model.translate()
    assert result.ok, [diagnostic.message for diagnostic in result.diagnostic_items]
    script = result.to_smt2()
    assert result.to_smt2() == script
    return script


def equivalent(left, right):
    solver = z3.Solver(ctx=left.ctx)
    solver.set(timeout=0)
    solver.add(z3.Xor(left, right))
    assert solver.check() == z3.unsat


def test_generated_200_cell_template_with_25_calls_is_exact_and_projectable():
    # The original DCP0060 template has 200 reads, 200 equalities, 200 ites,
    # one sum, and 25 applications: 601 * 25 = 15025 estimated operations.
    builder = HirBuilder()
    builder.declare('sequence', {'Array': ['Int', 'Int']})
    for tag in range(25):
        builder.constrain({
            'op': 'eq', 'args': [{
                'fold': 'sum', 'var': 'i', 'range': [0, 200],
                'body': {'op': 'ite', 'args': [
                    {'op': 'eq', 'args': [
                        {'at': 'sequence', 'indices': [{'var': 'i'}]},
                        {'literal': tag, 'sort': 'Int'}]},
                    {'literal': 1, 'sort': 'Int'},
                    {'literal': 0, 'sort': 'Int'}]},
            }, {'literal': 8, 'sort': 'Int'}],
        })
    result = builder.translate()
    assert result.ok, [diagnostic.message for diagnostic in result.diagnostic_items]
    script = result.to_smt2()
    assert len(builder._sum_template_cache) == 1
    assert script.count('(define-fun somt_hir_sum_template_1 ') == 1
    assert '(define-fun-rec ' not in script
    assert script.count('(somt_hir_sum_template_1 sequence ') == 25
    assert script.count('(select ') == 200
    assert len(script) < 40000

    context = z3.Context()
    formula = z3.And(*z3.parse_smt2_string(script, ctx=context))
    array = z3.Array('sequence', z3.IntSort(context), z3.IntSort(context))
    expected = z3.And(*[
        z3.Sum([z3.If(array[i] == tag, 1, 0) for i in range(200)]) == 8
        for tag in range(25)
    ])
    equivalent(formula, expected)
    aliases = [z3.Int(f'observed_{i}', ctx=context) for i in range(200)]
    bridges = [(alias, array[i]) for i, alias in enumerate(aliases)]
    projected = optimize_observation_projection(
        z3.And(formula, *[alias == term for alias, term in bridges]), bridges)
    assert projected.eliminated_array_roots == ('sequence',)
    assert projected.retained_array_roots == ()
    assert all(value.sort().kind() != z3.Z3_ARRAY_SORT
               for value in free_constants([projected.body]))
    expected_cells = z3.And(*[
        z3.Sum([z3.If(alias == tag, 1, 0) for alias in aliases]) == 8
        for tag in range(25)
    ])
    equivalent(projected.body, expected_cells)


def test_literal_reads_keep_negative_wide_indices_and_aliased_array_arguments():
    model = native.HirModel()
    array = model.declare('values', ARRAY)
    output = model.declare('total', INT)
    indices = list(range(-100, 99)) + [2 ** 100]
    first, second = bound('a', ARRAY), bound('b', ARRAY)
    body = op('add', *[
        op('ite', op('eq', op('select', first if i % 2 else second,
                             literal(index)), literal(7)), literal(1), literal(0))
        for i, index in enumerate(indices)
    ])
    model.declare_function('count_aliases', [ARRAY, ARRAY], INT)
    model.define_function('count_aliases', [('a', ARRAY), ('b', ARRAY)], body)
    model.constrain(op('eq', output,
                       native._hir_apply('count_aliases', INT, [array, array])))
    script = script_for(model)
    assert '(define-fun count_aliases ' in script
    context = z3.Context()
    formula = z3.And(*z3.parse_smt2_string(script, ctx=context))
    values = z3.Array('values', z3.IntSort(context), z3.IntSort(context))
    equivalent(formula, z3.Int('total', ctx=context) == z3.Sum([
        z3.If(values[index] == 7, 1, 0) for index in indices]))


@pytest.mark.parametrize('count,retained', [(200, False), (340, False), (341, True)])
def test_larger_leaf_stays_shared_instead_of_rejecting_the_model(count, retained):
    model = native.HirModel()
    array = model.declare('values', ARRAY)
    declare_count(model, count=count)
    model.constrain(op('ge', native._hir_apply('count', INT, [array, literal(1)]), literal(0)))
    script = script_for(model)
    # Cost is 3 * count + 1: the 1024-operation boundary is an encoding
    # threshold, not a language/instance-size restriction.
    spelling = 'define-fun-rec' if retained else 'define-fun'
    assert f'({spelling} count ' in script
    assert script.count('(count values ') == 1
    assert len(script) < 50000
    z3.parse_smt2_string(script, ctx=z3.Context())


@pytest.mark.parametrize('escape', ['symbolic_index', 'array_equality',
                                   'array_argument', 'array_return', 'binder'])
def test_non_leaf_or_whole_array_uses_keep_the_existing_sharing_policy(escape):
    model = native.HirModel()
    array = bound('a', ARRAY)
    body = count_body(array)
    result_sort = INT
    if escape == 'symbolic_index':
        body = count_body(array, index_for=lambda i: op('add', bound('tag'), literal(i)))
    elif escape == 'array_equality':
        other = model.declare('other', ARRAY)
        body = op('ite', op('eq', array, other), body, literal(0))
    elif escape == 'array_argument':
        model.declare_function('opaque', [ARRAY], INT)
        body = op('add', body, native._hir_apply('opaque', INT, [array]))
    elif escape == 'array_return':
        other = model.declare('other', ARRAY)
        body = op('ite', op('ge', body, literal(0)), array, other)
        result_sort = ARRAY
    else:
        quantified = native._hir_quantifier(
            True, [('q', INT)], op('ge', bound('q'), bound('tag')))
        body = op('ite', quantified, body, literal(0))
    model.declare_function('count', [ARRAY, INT], result_sort)
    model.define_function('count', [('a', ARRAY), ('tag', INT)], body)
    values = model.declare('values', ARRAY)
    output = model.declare('result', result_sort)
    model.constrain(op('eq', output,
                       native._hir_apply('count', result_sort, [values, literal(1)])))
    script = script_for(model)
    assert '(define-fun-rec count ' in script
    z3.parse_smt2_string(script, ctx=z3.Context())


def test_forward_dependency_keeps_full_leaf_cost_and_retains_the_caller():
    model = native.HirModel()
    values = model.declare('values', ARRAY)
    # Deliberately declare and define the caller before its dependency. If
    # count's 601-operation macro were recorded as a shared one-operation
    # call, this wrapper would incorrectly miss the ordinary 512 threshold.
    model.declare_function('wrapper', [ARRAY, INT], INT)
    model.declare_function('count', [ARRAY, INT], INT)
    model.define_function('wrapper', [('a', ARRAY), ('tag', INT)],
                          native._hir_apply('count', INT, [bound('a', ARRAY), bound('tag')]))
    model.define_function('count', [('a', ARRAY), ('tag', INT)], count_body(bound('a', ARRAY)))
    model.constrain(op('ge', native._hir_apply('wrapper', INT, [values, literal(1)]), literal(0)))
    script = script_for(model)
    assert script.index('(define-fun count ') < script.index('(define-fun-rec wrapper ')
    assert script.count('(select ') == 200
    assert '(wrapper values ' in script
    assert len(script) < 40000
    z3.parse_smt2_string(script, ctx=z3.Context())
