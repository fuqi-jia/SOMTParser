"""Independent visible relations for existentially hidden auxiliary functions."""
import pytest
import z3

from tools.semantic_checks.projection import existential_projection, free_constants
from tools.semantic_checks.checker_adapter import candidate_projection


def equivalent(actual, expected):
    solver = z3.Solver()
    solver.set(timeout=10000)
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


def answer(formula, *assignments):
    solver = z3.Solver()
    solver.set(timeout=10000)
    solver.add(formula, *assignments)
    return solver.check()


def test_unconstrained_auxiliary_predicate_does_not_restrict_visible_output():
    predicate = z3.Function('private_predicate', z3.IntSort(), z3.BoolSort())
    visible = z3.Bool('predicate_output')
    projected = existential_projection(visible == predicate(0), [visible])
    equivalent(projected, z3.BoolVal(True))
    assert {v.get_id() for v in free_constants([projected])} <= {visible.get_id()}


def test_repeated_application_preserves_function_congruence():
    function = z3.Function('private_repeat', z3.IntSort(), z3.IntSort())
    x, y = z3.Ints('repeat_x repeat_y')
    projected = existential_projection(z3.And(x == function(0), y == function(0)), [x, y])
    equivalent(projected, x == y)


@pytest.mark.parametrize('left,right', [(False, False), (False, True), (True, False), (True, True)])
def test_symbolic_arguments_preserve_congruence_for_each_visible_assignment(left, right):
    function = z3.Function('private_symbolic', z3.BoolSort(), z3.BoolSort())
    x, y = z3.Bools('symbolic_x symbolic_y')
    projected = existential_projection(function(x) != function(y), [x, y])
    assert answer(projected, x == left, y == right) == (z3.sat if left != right else z3.unsat)


def test_nested_function_calls_share_their_interpretations():
    outer = z3.Function('nested_outer', z3.IntSort(), z3.IntSort())
    inner = z3.Function('nested_inner', z3.IntSort(), z3.IntSort())
    x, y = z3.Ints('nested_x nested_y')
    body = z3.And(inner(0) == inner(1), x == outer(inner(0)), y == outer(inner(1)))
    projected = existential_projection(body, [x, y])
    assert answer(projected, x == 0, y == 1) == z3.unsat
    assert answer(projected, x == 3, y == 3) == z3.sat


def test_different_argument_sorts_keep_argument_positions():
    function = z3.Function('mixed_domains', z3.IntSort(), z3.BoolSort(), z3.IntSort())
    x, y = z3.Ints('mixed_x mixed_y')
    projected = existential_projection(z3.And(x == function(1, True), y == function(1, False)), [x, y])
    assert answer(projected, x == 4, y == 9) == z3.sat
    repeated = existential_projection(z3.And(x == function(1, True), y == function(1, True)), [x, y])
    assert answer(repeated, x == 4, y == 9) == z3.unsat


def test_nested_quantifiers_do_not_capture_function_argument_placeholders():
    from tools.semantic_checks.hidden_functions import encode_hidden_functions

    function = z3.Function('quantified_auxiliary', z3.BoolSort(), z3.BoolSort(), z3.BoolSort())
    x, y, visible = z3.Bools('bound_x bound_y quantified_output')
    body = z3.And(z3.ForAll([x], z3.ForAll([y], function(x, y) == (x == y))),
                  visible == function(False, True))
    encoded, arrays = encode_hidden_functions(body)
    assert len(arrays) == 1
    array = arrays[0]
    # Z3 may return unknown for the full XOR of existential arrays and
    # universal binders. Check both constructive directions instead.
    # This explicit equality truth table witnesses every allowed output.
    false_row = z3.Store(z3.K(z3.BoolSort(), False), False, True)
    true_row = z3.Store(z3.K(z3.BoolSort(), False), True, True)
    witness = z3.Store(z3.K(z3.BoolSort(), false_row), True, true_row)
    equivalent(z3.substitute(encoded, (array, witness)), z3.Not(visible))
    # Conversely the universal body implies these four instances, which
    # already force the only observed cell to false.
    universal = encoded.arg(0)
    binders = universal
    while z3.is_quantifier(binders):
        binders = binders.body()
    instances = [z3.substitute_vars(binders, z3.BoolVal(b), z3.BoolVal(a))
                 for a in [False, True] for b in [False, True]]
    assert answer(z3.And(*instances, encoded.arg(1)), visible) == z3.unsat


def test_independent_models_do_not_share_private_predicate_interpretations():
    predicate = z3.Function('same_spelling_private', z3.IntSort(), z3.BoolSort())
    x = z3.Bool('shared_visible_output')
    left = existential_projection(x == predicate(0), [x])
    right = existential_projection(x == z3.Not(predicate(0)), [x])
    equivalent(left, right)


def test_checker_adapter_hides_functions_after_observation_aliases_are_bound():
    predicate = z3.Function('adapter_private', z3.IntSort(), z3.BoolSort())
    x, alias = z3.Bools('adapter_source adapter_visible')
    result = candidate_projection([x == predicate(0)], [(alias, x)])
    equivalent(result.formula, z3.BoolVal(True))


def test_datatype_constructors_are_not_reinterpreted_as_private_functions():
    datatype = z3.Datatype('ProjectionBox')
    datatype.declare('box', ('value', z3.IntSort()))
    datatype = datatype.create()
    x = z3.Int('box_output')
    body = datatype.value(datatype.box(x)) == 7
    equivalent(existential_projection(body, [x]), x == 7)
