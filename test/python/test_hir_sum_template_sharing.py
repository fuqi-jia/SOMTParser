"""Focused qualification cases for compact finite-sum helper sharing."""
import pytest
import z3

from somtparser.hir import HirBuilder, ModelError


def lit(value, sort=None):
    return {'literal': value, 'sort': sort or ('Bool' if type(value) is bool else 'Int')}


def op(name, *args):
    return {'op': name, 'args': list(args)}


def fold(name, bounds, body):
    return {'fold': 'sum', 'var': name, 'range': bounds, 'body': body}


def translated_formula(builder):
    result = builder.translate()
    assert result.ok, [item.message for item in result.diagnostic_items]
    return z3.And(*z3.parse_smt2_string(result.to_smt2()))


def test_alpha_literal_templates_preserve_relation_and_reduce_construction():
    def build(helpers_enabled, count=8):
        builder = HirBuilder()
        builder.declare('values', 'Int', shape=[12, 4])
        if not helpers_enabled:
            builder._sum_template_limit = 0
        for group in range(count):
            body = op('ite',
                      op('eq', {'at': 'values', 'indices': [
                          {'var': 'i'}, lit(group % 4)]}, lit(group % 4)),
                      lit(1), lit(0))
            builder.constrain(op('eq', fold('i', [0, 12], body), lit(3)))
        return builder, translated_formula(builder)

    shared, shared_formula = build(True)
    expanded, expanded_formula = build(False)
    assert len(shared._sum_template_cache) == 1
    assert shared.nodes < expanded.nodes
    solver = z3.Solver(); solver.add(z3.Xor(shared_formula, expanded_formula))
    assert solver.check() == z3.unsat


def test_free_array_arguments_inside_outer_quantifier_do_not_capture():
    def build(helpers_enabled):
        builder = HirBuilder()
        builder.declare('values', 'Int', shape=[4, 4])
        if not helpers_enabled:
            builder._sum_template_limit = 0
        body = op('ite', op('eq', {
            'at': 'values', 'indices': [{'var': 'i'}, {'var': 'q'}],
        }, lit(2)), lit(1), lit(0))
        inner = op('eq', fold('i', [0, 4], body), lit(1))
        builder.constrain({'fold': 'forall', 'var': 'q', 'range': [0, 4], 'body': inner})
        return builder, translated_formula(builder)

    shared, shared_formula = build(True)
    expanded, expanded_formula = build(False)
    assert len(shared._sum_template_cache) == 1
    solver = z3.Solver(); solver.add(z3.Xor(shared_formula, expanded_formula))
    assert solver.check() == z3.unsat


def test_mutable_data_content_is_part_of_template_key():
    builder = HirBuilder()
    builder.data = {'weights': [1, 2, 3]}

    def total():
        return fold('i', [0, 3], {
            'data': 'weights', 'indices': [{'var': 'i'}], 'default': lit(0),
        })

    first = builder.expr(op('eq', total(), lit(6)))
    builder.data['weights'][0] = 2
    second = builder.expr(op('eq', total(), lit(7)))
    builder.model.constrain(first)
    builder.model.constrain(second)
    assert len(builder._sum_template_cache) == 2
    assert translated_formula(builder) is not None


def test_reordered_data_keys_cannot_swap_same_sort_parameter_slots():
    def build(helpers_enabled):
        builder = HirBuilder()
        builder.data = {'weights': [7]}
        builder.declare('x', 'Int')
        builder.declare('y', 'Int')
        if not helpers_enabled:
            builder._sum_template_limit = 0
        first_body = {
            'data': 'weights', 'indices': [{'var': 'x'}], 'default': lit(5),
        }
        # Same normalized lookup, but visit the Int literal before the Int
        # free variable. The helper formal order must not be inferred from
        # equal sorts alone.
        second_body = {
            'default': lit(9), 'indices': [{'var': 'y'}], 'data': 'weights',
        }
        builder.constrain(op('eq', fold('i', [0, 1], first_body), lit(5)))
        builder.constrain(op('eq', fold('i', [0, 1], second_body), lit(9)))
        return builder, translated_formula(builder)

    shared, shared_formula = build(True)
    expanded, expanded_formula = build(False)
    assert len(shared._sum_template_cache) == 2
    solver = z3.Solver(); solver.add(z3.Xor(shared_formula, expanded_formula))
    assert solver.check() == z3.unsat


def test_same_smt_array_sort_with_different_finite_dimensions_does_not_reuse():
    def build(helpers_enabled):
        builder = HirBuilder()
        builder.declare('left', 'Int', shape=[2, 3])
        builder.declare('right', 'Int', shape=[3, 2])
        if not helpers_enabled:
            builder._sum_template_limit = 0
        for array_name in ('left', 'right'):
            body = op('ite', op('eq', {
                'at': array_name, 'indices': [{'var': 'i'}, lit(1)],
            }, lit(0)), lit(1), lit(0))
            builder.constrain(op('eq', fold('i', [0, 2], body), lit(1)))
        return builder, translated_formula(builder)

    shared, shared_formula = build(True)
    expanded, expanded_formula = build(False)
    assert len(shared._sum_template_cache) == 2
    solver = z3.Solver(); solver.add(z3.Xor(shared_formula, expanded_formula))
    assert solver.check() == z3.unsat


def test_static_out_of_bounds_finite_array_index_uses_ordinary_path():
    builder = HirBuilder()
    builder.declare('values', 'Int', shape=[2, 3])
    invalid = {'at': 'values', 'indices': [{'var': 'i'}, lit(3)]}
    candidate = fold('i', [0, 2], op('ite', op('ge', invalid, lit(0)), lit(1), lit(0)))
    assert builder._sum_template(candidate, {}) is None
    assert not builder._sum_template_cache


@pytest.mark.parametrize('helpers_enabled', [True, False])
def test_invalid_data_index_type_keeps_precise_helper_body_diagnostic(helpers_enabled):
    builder = HirBuilder()
    if not helpers_enabled:
        builder._sum_template_limit = 0
    builder.data = {'weights': [4, 5]}
    bad_lookup = {
        'data': 'weights', 'indices': [lit('0.0', 'Real')], 'default': lit(0),
    }
    candidate = fold('i', [0, 2], op('ite',
        op('eq', {'var': 'i'}, lit(0)), bad_lookup, lit(0)))
    with pytest.raises(ModelError, match='data lookup indices must have sort Int') as error:
        builder.expr(candidate, _path='constraints[0].expr')
    assert error.value.path == 'constraints[0].expr.body.args[1].indices[0]'
    assert not builder._sum_template_cache


def test_private_helper_compilation_does_not_share_fold_lookup_cache_terms():
    builder = HirBuilder()
    builder.declare('values', {'Array': ['Int', 'Int']})
    original_cache = builder._fold_lookup_cache
    candidate = fold('i', [0, 4], op('ite', op('eq', {
        'at': 'values', 'indices': [{'var': 'i'}],
    }, lit(1)), lit(1), lit(0)))
    assert builder.expr(candidate) is not None
    assert builder._fold_lookup_cache is original_cache
    assert original_cache == {}
    assert len(builder._sum_template_cache) == 1


def test_unsafe_partial_arithmetic_and_non_numeric_body_stay_on_checked_path():
    boolean_body = fold('i', [0, 2], lit(True))
    boolean_builder = HirBuilder()
    with pytest.raises(ModelError, match='numeric operands'):
        boolean_builder.expr(boolean_body)
    assert not boolean_builder._sum_template_cache

    guarded = HirBuilder()
    guarded.declare('x', 'Int')
    partial = op('implies', op('ne', {'var': 'x'}, lit(0)),
                 op('eq', fold('i', [0, 3], op('div', {'var': 'i'}, {'var': 'x'})), lit(3)))
    guarded.constrain(partial)
    assert not guarded._sum_template_cache
    assert translated_formula(guarded) is not None


def test_repeated_templates_preserve_existing_100000_construction_budget():
    builder = HirBuilder()
    builder.declare('values', 'Int', shape=[12, 4])
    for group in range(800):
        body = op('ite', op('eq', {'at': 'values', 'indices': [
            {'var': 'i'}, lit(group % 4)]}, lit(group % 4)), lit(1), lit(0))
        builder.constrain(op('eq', fold('i', [0, 12], body), lit(3)))
    translated_formula(builder)
    assert len(builder._sum_template_cache) == 1
    assert builder.nodes < 100000


def test_real_sum_helper_keeps_exact_numeric_result_sort():
    builder = HirBuilder()
    builder.declare('x', 'Real')
    builder.constrain(op('eq', fold('i', [0, 3], {'var': 'x'}), lit('3.0', 'Real')))
    assert len(builder._sum_template_cache) == 1
    assert translated_formula(builder) is not None


def test_large_generated_sum_retains_definition_and_exact_relation():
    builder = HirBuilder()
    builder.declare('x', 'Int')
    builder.declare('y', 'Int')
    total = fold('i', [0, 600], op('add', {'var': 'x'}, {'var': 'i'}))
    builder.constrain(op('eq', total, {'var': 'y'}))
    result = builder.translate()
    assert result.ok, [item.message for item in result.diagnostic_items]
    smt = result.to_smt2()
    assert '(define-fun-rec ' in smt
    # Z3 keeps recursive definitions in its Context. This standalone script
    # must not inherit identically named private helpers from earlier tests.
    context = z3.Context()
    formula = z3.And(*z3.parse_smt2_string(smt, ctx=context))
    x, y = z3.Ints('x y', ctx=context)
    solver = z3.Solver(ctx=context)
    solver.set(timeout=5000)
    solver.add(z3.Xor(formula, y == 600 * x + 179700))
    assert solver.check() == z3.unsat
