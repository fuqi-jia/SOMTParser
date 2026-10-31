import pytest
import z3

from tools.semantic_checks.ite_affine_factoring import factor_ite_common_affine_terms


def checked(term):
    result = factor_ite_common_affine_terms(term)
    solver = z3.Solver(ctx=term.ctx)
    solver.add(term != result.formula)
    assert solver.check() == z3.unsat
    return result


def test_cancel_external_sum_from_conditional_branches():
    a, b, d = z3.Ints('a b d')
    c = z3.Bool('c')
    term = -(a + 3*b) + z3.If(c, a + 3*b, a + 3*b + d)
    result = checked(term)
    assert result.rewritten_ites == 1
    assert result.formula.eq(z3.If(c, 0, d))


@pytest.mark.parametrize('coefficient', [-19, -2, -1, 1, 2, 19, 10**80])
def test_signed_multiplicities_are_preserved(coefficient):
    x, y, z = z3.Ints('x y z')
    common = coefficient*x
    term = -common + z3.If(z3.Bool('c'), common+y, z+common)
    result = checked(term)
    assert result.rewritten_ites == 1
    assert result.formula.eq(z3.If(z3.Bool('c'), y, z))


def test_different_coefficients_are_not_mistaken_for_equal_terms():
    x = z3.Int('x')
    result = checked(z3.If(z3.Bool('c'), 2*x, 3*x))
    assert result.rewritten_ites == 0


def test_repeated_terms_keep_integer_multiplicity():
    x, y = z3.Ints('x y')
    result = checked(-2*x + z3.If(z3.Bool('c'), x+x+y, 2*x-y))
    assert result.formula.eq(z3.simplify(z3.If(z3.Bool('c'), y, -y)))


def test_common_constant_and_different_offsets():
    x, y = z3.Ints('x y')
    c = z3.Bool('c')
    result = checked(z3.If(c, x+7, y+7) - 7)
    assert result.formula.eq(z3.If(c, x, y))
    checked(z3.If(c, x+7, x+8))


def test_condition_depends_on_common_term():
    x, y = z3.Ints('x y')
    result = checked(-x + z3.If(x > 3, x+y, x-y))
    solver = z3.Solver()
    solver.add(result.formula != z3.If(x > 3, y, -y))
    assert solver.check() == z3.unsat


def test_identical_branches_drop_irrelevant_condition():
    x, y = z3.Ints('x y')
    result = checked(z3.If(z3.Bool('c'), x-y+3, x-y+3))
    assert not z3.is_app_of(result.formula, z3.Z3_OP_ITE)


def test_opaque_nonlinear_product_is_not_distributed():
    x, y, z = z3.Ints('x y z')
    result = checked(-3*x*y + z3.If(z3.Bool('c'), 3*x*y+z, 3*x*y-z))
    assert result.rewritten_ites == 1


def test_opaque_integer_division_keeps_total_smt_semantics():
    x, d = z3.Ints('x d')
    v = x/d
    checked(-v + z3.If(z3.Bool('c'), v+1, v-2))


def test_array_read_and_uninterpreted_function_common_terms():
    array = z3.Array('a', z3.IntSort(), z3.IntSort())
    i, j = z3.Ints('i j')
    fun = z3.Function('f', z3.IntSort(), z3.IntSort())
    common = array[i] + 2*fun(j)
    result = checked(-common + z3.If(z3.Bool('c'), common+8, common-9))
    assert result.formula.eq(z3.If(z3.Bool('c'), 8, -9))


def test_boolean_real_and_bitvector_ites_do_not_use_integer_factoring():
    c, a, b = z3.Bools('c a b')
    x, y = z3.Reals('x y')
    v, w = z3.BitVecs('v w', 8)
    for term in [z3.If(c, a, b), z3.If(c, x+y, x-y), z3.If(c, v+w, v-w)]:
        assert checked(term).rewritten_ites == 0


def test_quantifier_body_is_not_factored_by_this_pass():
    x = z3.Int('x')
    q = z3.ForAll(x, z3.If(x > 0, x+1, x-2) >= x-2)
    assert checked(q).rewritten_ites == 0


def test_large_shared_affine_dag_is_not_expanded_by_paths():
    x, y = z3.Ints('x y')
    common = x
    for _ in range(150):
        common = common+common
    result = checked(-common + z3.If(z3.Bool('c'), common+y, common-y))
    assert result.visited_nodes < 180
    assert result.formula.eq(z3.simplify(z3.If(z3.Bool('c'), y, -y)))


def test_nested_factoring_can_expose_an_outer_common_term():
    x, y = z3.Ints('x y')
    p, q = z3.Bools('p q')
    common = z3.If(p, x+1, x+2)
    result = checked(z3.If(q, common+y, common-y)-x)
    assert result.rewritten_ites >= 2


def test_custom_context_and_separate_call_lifetimes():
    ctx = z3.Context()
    x, y = z3.Ints('x y', ctx=ctx)
    c = z3.Bool('c', ctx=ctx)
    checked(-x + z3.If(c, x+y, x-y))
    for k in range(25):
        checked(-x + z3.If(c, x+k, x-k))


def test_entire_relation_and_ordered_cost_equations_remain():
    x, y, cost0, cost1 = z3.Ints('x y cost0 cost1')
    c = z3.Bool('c')
    term = -x + z3.If(c, x+y, x-y)
    relation = z3.And(x >= -2, x <= 3, cost0 == term, cost1 == -term)
    checked(relation)
