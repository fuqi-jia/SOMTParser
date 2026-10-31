"""Finite Boolean folds keep their exact domain without Cartesian expansion."""
from _public_relation import public_relation
import pytest
import z3
from somtparser.hir import HirBuilder, ModelError


def lit(x):
    return {'literal': x, 'sort': 'Bool' if type(x) is bool else 'Int'}


def op(name, *args):
    return {'op': name, 'args': list(args)}


def fold(kind, name, bounds, body):
    return {'fold': kind, 'var': name, 'range': bounds, 'body': body}


def compile_expression(expr, declarations=()):
    b = HirBuilder()
    for name in declarations:
        b.declare(name, 'Int')
    b.constrain(expr)
    result = b.translate()
    assert result.ok, [d.message for d in result.diagnostic_items]
    script = result.to_smt2()
    return b, script, public_relation(result, script)


@pytest.mark.parametrize('kind', ['forall', 'exists'])
@pytest.mark.parametrize('bounds', [[-70, 0], [3, 68], [5, 69], [8, 9], [8, 8]])
@pytest.mark.parametrize('negated', [False, True])
def test_fold_matches_independent_enumeration(kind, bounds, negated):
    expr = fold(kind, 'i', bounds, op('le', {'var': 'i'}, {'var': 'x'}))
    if negated:
        expr = op('not', expr)
    _, script, actual = compile_expression(expr, ['x'])
    terms = [i <= z3.Int('x') for i in range(*bounds)]
    expected = z3.And(*terms) if kind == 'forall' else z3.Or(*terms)
    if negated:
        expected = z3.Not(expected)
    s = z3.Solver(); s.set(timeout=10000)
    s.add(z3.Xor(actual, expected))
    assert s.check() == z3.unsat
    if bounds[1] - bounds[0] > 64:
        assert '(forall ' in script or '(exists ' in script or '!somt_exists_' in script


def test_nested_ranges_remain_compact_and_do_not_capture_shadowed_names():
    # The old construction tries 9999 * 4999 copies of the inner body.
    inner = fold('exists', 'd', [2, 5001], op('eq', {'var': 'd'}, lit(3)))
    expr = fold('forall', 'd', [2, 10001], inner)
    b, script, actual = compile_expression(expr, ['d'])
    assert b.nodes < 100
    assert len(script) < 5000
    s = z3.Solver(); s.set(timeout=10000); s.add(z3.Not(actual))
    assert s.check() == z3.unsat
    # An outer free d is independent of either bound d.
    s = z3.Solver(); s.add(actual, z3.Int('d') == -123)
    assert s.check() == z3.sat


def test_nested_medium_finite_boolean_folds_do_not_expand_cartesian_products():
    # The source is only a few thousand JSON nodes, but unrolling four ranges
    # of length 16 visits over 65,000 copies of the innermost body. Keep the
    # exact finite bounds while lowering each Boolean fold as a guarded native
    # quantifier instead.
    expr = fold(
        'forall', 'i', [0, 16],
        fold('exists', 'j', [0, 16],
             fold('forall', 'k', [0, 16],
                  fold('exists', 'l', [0, 16],
                       op('eq', {'var': 'l'}, {'var': 'i'})))),
    )
    builder, script, actual = compile_expression(expr)
    assert builder.nodes < 100
    assert script.count('(forall ') >= 2
    assert script.count('(exists ') >= 2
    solver = z3.Solver()
    solver.add(z3.Not(actual))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize(('kind', 'bounds', 'value', 'expected'), [
    ('exists', [3, 12], 11, True),
    ('exists', [3, 12], 12, False),
    ('forall', [3, 12], 11, False),
])
def test_medium_quantified_folds_keep_half_open_bounds(kind, bounds, value, expected):
    expr = fold(kind, 'i', bounds, op('eq', {'var': 'i'}, lit(value)))
    _, _, actual = compile_expression(expr)
    solver = z3.Solver()
    solver.add(z3.Not(actual) if expected else actual)
    assert solver.check() == z3.unsat


def test_wide_integer_endpoints_are_exact():
    n = 10**30
    expr = fold('exists', 'i', [n, n+65], op('eq', {'var': 'i'}, lit(n+64)))
    _, _, actual = compile_expression(expr)
    s = z3.Solver(); s.add(z3.Not(actual)); assert s.check() == z3.unsat


@pytest.mark.parametrize('kind', ['forall', 'exists'])
def test_quantified_fold_rejects_non_boolean_body(kind):
    with pytest.raises(ModelError, match='Bool'):
        compile_expression(fold(kind, 'i', [0, 65], {'var': 'i'}))


def test_sum_and_input_budgets_are_preserved():
    _, _, actual = compile_expression(op('eq', fold('sum', 'i', [0, 70], {'var': 'i'}), lit(sum(range(70)))))
    s = z3.Solver(); s.add(z3.Not(actual)); assert s.check() == z3.unsat
    for kind in ['sum', 'forall', 'exists']:
        with pytest.raises(ModelError, match='10000'):
            compile_expression(fold(kind, 'i', [0, 10001], lit(True)))


def test_repeated_fold_array_lookups_share_nodes_without_changing_relation():
    def compile_repeated(cache_enabled):
        builder = HirBuilder()
        builder._sum_template_limit = 0
        builder.declare('values', {'Array': ['Int', 'Int']})
        if not cache_enabled:
            builder._fold_lookup_cache = None
        for target in range(12):
            matches = fold(
                'sum', 'i', [0, 12],
                op('ite', op('eq', {'at': 'values', 'indices': [{'var': 'i'}]}, lit(target)),
                   lit(1), lit(0)),
            )
            builder.constrain(op('eq', matches, lit(1)))
        translated = builder.translate()
        assert translated.ok, [item.message for item in translated.diagnostic_items]
        formula = public_relation(translated)
        return builder, formula

    cached, cached_formula = compile_repeated(True)
    uncached, uncached_formula = compile_repeated(False)
    assert cached.nodes < uncached.nodes
    solver = z3.Solver()
    solver.add(z3.Xor(cached_formula, uncached_formula))
    assert solver.check() == z3.unsat


def test_fold_lookup_sharing_respects_nested_fold_and_quantifier_shadowing():
    def compile_shadowed(cache_enabled):
        builder = HirBuilder()
        builder._sum_template_limit = 0
        builder.declare('values', {'Array': ['Int', 'Int']})
        if not cache_enabled:
            builder._fold_lookup_cache = None
        nested_fold = fold(
            'sum', 'i', [0, 2],
            op('ite', op('eq', {'at': 'values', 'indices': [{'var': 'i'}]}, {'var': 'i'}),
               lit(1), lit(0)),
        )
        quantified = fold(
            'forall', 'i', [0, 9],
            op('ge', {'at': 'values', 'indices': [{'var': 'i'}]}, lit(0)),
        )
        body = op('ite', op('and', quantified,
                            op('eq', {'at': 'values', 'indices': [{'var': 'i'}]}, {'var': 'i'})),
                  nested_fold, lit(0))
        builder.constrain(op('eq', fold('sum', 'i', [0, 3], body), lit(3)))
        translated = builder.translate()
        assert translated.ok, [item.message for item in translated.diagnostic_items]
        return builder, public_relation(translated)

    cached, cached_formula = compile_shadowed(True)
    uncached, uncached_formula = compile_shadowed(False)
    assert cached.nodes < uncached.nodes
    solver = z3.Solver()
    solver.add(z3.Xor(cached_formula, uncached_formula))
    assert solver.check() == z3.unsat


def test_fold_data_lookup_cache_tracks_mutable_table_contents():
    builder = HirBuilder()
    builder.data = {'weights': [1, 2]}

    def total():
        return fold('sum', 'i', [0, 2],
                    {'data': 'weights', 'indices': [{'var': 'i'}], 'default': lit(0)})

    builder.constrain(op('eq', total(), lit(3)))
    builder.data['weights'][0] = 5
    builder.constrain(op('eq', total(), lit(7)))
    translated = builder.translate()
    assert translated.ok, [item.message for item in translated.diagnostic_items]
    formula = public_relation(translated)
    solver = z3.Solver()
    solver.add(z3.Not(formula))
    assert solver.check() == z3.unsat


def test_shared_fold_predicates_match_independent_counting():
    builder = HirBuilder()
    builder.declare('hosts', {'Array': ['Int', 'Bool']})
    builder.declare('visits', {'Array': ['Int', 'Int']})
    for target in range(4):
        body = op('and', op('not', {'at': 'hosts', 'indices': [{'var': 'i'}]}),
                  op('eq', {'at': 'visits', 'indices': [{'var': 'i'}]}, lit(target)))
        builder.constrain(op('eq', fold('sum', 'i', [0, 12],
                                       op('ite', body, lit(1), lit(0))), lit(target)))
    result = builder.translate()
    assert result.ok, [d.message for d in result.diagnostic_items]
    hosts = z3.Array('hosts', z3.IntSort(), z3.BoolSort())
    visits = z3.Array('visits', z3.IntSort(), z3.IntSort())
    expected = z3.And(*[
        z3.Sum(*[z3.If(z3.And(z3.Not(hosts[i]), visits[i] == target), 1, 0)
                 for i in range(12)]) == target for target in range(4)
    ])
    solver = z3.Solver()
    solver.add(z3.Xor(public_relation(result), expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('cache_enabled', [True, False])
def test_cached_fold_subtree_cannot_bypass_depth_limit(cache_enabled):
    builder = HirBuilder()
    builder.declare('values', {'Array': ['Int', 'Bool']})
    if not cache_enabled:
        builder._fold_lookup_cache = None
    lookup = {'at': 'values', 'indices': [{'var': 'i'}]}
    builder.expr(fold('forall', 'i', [0, 1], lookup))
    deep = lookup
    for _ in range(63):
        deep = op('not', deep)
    with pytest.raises(ModelError, match='budget'):
        builder.expr(fold('forall', 'i', [0, 1], deep))
