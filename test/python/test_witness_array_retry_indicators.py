"""Complete equivalence of array retry and arithmetic-indicator composition."""
import pytest
import z3
from tools.semantic_checks.existential_definitions import (
    _scalar_array_witnesses, eliminate_existential_definitions)


def prove(left, right):
    solver = z3.Solver()
    solver.add(z3.Xor(left, right))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('kind', ['public-forall', 'private-scalar', 'shadowed-array'])
def test_array_retry_preserves_independent_quantified_conjunct(kind):
    a = z3.Array('a', z3.IntSort(), z3.IntSort())
    x, i = z3.Ints('x i')
    f = z3.Function('f', z3.IntSort(), z3.IntSort())
    condition = z3.ForAll([i], f(i) >= 0)
    private = [a]
    if kind == 'private-scalar':
        condition = z3.ForAll([i], z3.Implies(i == x, f(i) >= 0))
        private.append(x)
    elif kind == 'shadowed-array':
        condition = z3.ForAll([a], a[0] == a[0])
    body = z3.And(a[0] >= x, a[0] <= x, a[0] > 0, condition)
    projected = _scalar_array_witnesses(body, {v.get_id(): v for v in private})
    assert projected is not None and projected[2] == 1
    complete = z3.Exists(list(projected[1].values()), projected[0])
    expected = z3.And(x > 0, condition)
    if kind == 'private-scalar':
        expected = z3.Exists([x], expected)
    prove(complete, expected)
    forward = z3.Solver()
    forward.add(body, z3.Not(expected))
    assert forward.check() == z3.unsat
    # Explicit witness proves the reverse direction without depending on
    # Z3's incomplete nested quantified-array decision procedure.
    witness = z3.K(z3.IntSort(), x)
    reverse = z3.substitute(body, (a, witness))
    if kind == 'private-scalar':
        reverse = z3.Exists([x], reverse)
    prove(reverse, expected)


@pytest.mark.parametrize('position', ['body', 'pattern', 'whole-array', 'negative-quantifier'])
def test_quantified_or_whole_array_use_blocks_retry(position):
    a, other = z3.Consts('a other', z3.ArraySort(z3.IntSort(), z3.IntSort()))
    i = z3.Int('i')
    f = z3.Function('f', z3.IntSort(), z3.IntSort())
    if position == 'body':
        clause = z3.ForAll([i], a[i] >= 0)
    elif position == 'pattern':
        clause = z3.ForAll([i], f(i) >= 0, patterns=[a[i]])
    elif position == 'whole-array':
        clause = a != other
    else:
        clause = z3.Not(z3.Exists([i], a[i] < 0))
    body = z3.And(a[0] > 0, clause)
    assert _scalar_array_witnesses(body, {a.get_id(): a}) is None


@pytest.mark.parametrize('corrupt', [False, True])
def test_nested_defined_array_then_scalar_projection_preserves_all_cells(corrupt):
    sets = z3.Array('sets', z3.IntSort(), z3.ArraySort(z3.IntSort(), z3.BoolSort()))
    public = z3.Array('public', z3.IntSort(), z3.BoolSort())
    counts = z3.Array('counts', z3.IntSort(), z3.IntSort())
    i, x = z3.Ints('i x')
    domain = z3.ForAll([i], z3.Implies(public[i], z3.And(i >= 0, i <= 2)))
    body = z3.And(sets[0] == public, domain, counts[0] >= x,
                  counts[0] <= x, counts[0] > 0,
                  z3.Or(sets[0][0], sets[0][1]),
                  counts[1] > 3, counts[1] < (4 if corrupt else 5))
    result = eliminate_existential_definitions(z3.Exists([sets, counts], body))
    assert result.direct_definitions >= 1 and result.scalarized_arrays == 1
    expected = z3.And(domain, x > 0, z3.Or(public[0], public[1]), z3.BoolVal(not corrupt))
    prove(result.formula, expected)
    forward = z3.Solver()
    forward.add(body, z3.Not(expected))
    assert forward.check() == z3.unsat
    set_witness = z3.K(z3.IntSort(), public)
    scalar_witness = z3.Store(z3.K(z3.IntSort(), x), 1, 4)
    witness_body = z3.substitute(body, (sets, set_witness), (counts, scalar_witness))
    prove(witness_body, expected)


@pytest.mark.parametrize('sort', ['Int', 'Real'])
def test_indicator_products_exposed_after_witness_substitution(sort):
    b, c, d = z3.Bools('b c d')
    number = z3.IntVal if sort == 'Int' else z3.RealVal
    x, y = z3.Consts('x y', z3.IntSort() if sort == 'Int' else z3.RealSort())
    first, second = z3.If(b, number(1), number(0)), z3.If(c, number(1), number(0))
    body = z3.And(x == first, y == second,
                  z3.Or(x*y == 0, x*y == 1),
                  z3.Or(x*y == 1, z3.Not(b), z3.Not(c)), d)
    result = eliminate_existential_definitions(z3.Exists([x, y], body))
    assert result.indicator_products > 0
    prove(result.formula, d)
    prove(z3.Exists([x, y], body), result.formula)


def test_indicator_only_change_is_returned_with_residual_witness():
    x = z3.Int('x')
    b, c = z3.Bools('b c')
    term = z3.If(b, 1, 0) * z3.If(c, 1, 0)
    formula = z3.Exists([x], z3.And(x > 0, x < 3, z3.Or(term == 0, term == 1)))
    result = eliminate_existential_definitions(formula)
    assert result.indicator_products > 0
    assert result.direct_definitions == result.conditional_definitions == 0
    prove(result.formula, z3.BoolVal(True))
    prove(formula, result.formula)


def test_indicator_siblings_do_not_enter_or_capture_nested_binder():
    x, i = z3.Ints('x i')
    b, c = z3.Bools('b c')
    f = z3.Function('f', z3.IntSort(), z3.BoolSort())
    quantifier = z3.ForAll([i], z3.Implies(i == x, f(i)))
    product = z3.If(b, 1, 0)*z3.If(c, 1, 0)
    formula = z3.Exists([x], z3.And(x == 7, quantifier, z3.Or(product == 0, product == 1)))
    result = eliminate_existential_definitions(formula)
    assert result.indicator_products > 0
    prove(formula, result.formula)
    prove(result.formula, f(7))


def test_indicator_real_constraint_is_never_dropped_as_a_tautology():
    x = z3.Int('x')
    b, c = z3.Bools('b c')
    product = z3.If(b, 1, 0)*z3.If(c, 1, 0)
    formula = z3.Exists([x], z3.And(x == 1, product == x))
    result = eliminate_existential_definitions(formula)
    prove(formula, result.formula)
    prove(result.formula, z3.And(b, c))


@pytest.mark.parametrize('corrupt', [False, True])
def test_complete_certificate_retries_array_only_projection(corrupt):
    from tools.semantic_checks.full_relation_certificate import prove_complete_relation
    a = z3.Array('complete_array', z3.IntSort(), z3.IntSort())
    x, public = z3.Ints('complete_scalar public')
    bound = 8 if corrupt else 9
    left_body = z3.And(x >= public, x <= 9)
    right_body = z3.And(a[0] >= public, a[0] <= bound)
    left = z3.Exists([x], left_body)
    right = z3.Exists([a], right_body)
    proof = prove_complete_relation(left, right)
    projection = proof['definition_projection'][1]
    assert projection['direct'] == projection['conditional'] == 0
    assert projection['scalarized_arrays'] == 1 and projection['indicator_products'] == 0
    assert proof['equivalent'] is (None if corrupt else True)
    # Prove each existential against its exact closed condition using total
    # witnesses. Every check is quantifier-free, so the independent reference
    # does not depend on Z3's incomplete quantified-array procedure.
    left_condition, right_condition = public <= 9, public <= bound
    left_witness = z3.substitute(left_body, (x, public))
    right_witness = z3.substitute(right_body, (a, z3.K(z3.IntSort(), public)))
    for premise, conclusion in [(left_body, left_condition),
                                (left_condition, left_witness),
                                (right_body, right_condition),
                                (right_condition, right_witness)]:
        implication = z3.Solver()
        implication.add(premise, z3.Not(conclusion))
        assert implication.check() == z3.unsat
    solver = z3.Solver()
    solver.add(z3.Xor(left_condition, right_condition))
    assert solver.check() == (z3.sat if corrupt else z3.unsat)


def test_complete_certificate_retries_indicator_only_projection():
    from tools.semantic_checks.full_relation_certificate import prove_complete_relation
    witness = z3.Int('unused_after_indicator')
    b, c, public = z3.Bools('complete_b complete_c complete_public')
    product = z3.If(b, 1, 0)*z3.If(c, 1, 0)
    left = public
    right = z3.Exists([witness], z3.And(public, z3.Or(product == 0, product == 1)))
    proof = prove_complete_relation(left, right)
    projection = proof['definition_projection'][1]
    assert projection['direct'] == projection['conditional'] == projection['scalarized_arrays'] == 0
    assert projection['indicator_products'] > 0
    assert proof['equivalent'] is True
    prove(left, right)
