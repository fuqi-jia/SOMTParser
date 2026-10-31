"""Exact occurrence indexing, including sharing, binders, and signed costs."""
import gc
import pytest
import z3
from tools.semantic_checks import existential_definitions as definitions


def index_for(*variables):
    return definitions._WitnessDependencyIndex({x.get_id(): x for x in variables})


def unsat(formula):
    solver = z3.Solver(ctx=formula.ctx)
    solver.add(formula)
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('kind', ['sum', 'ite', 'forall', 'exists', 'lambda', 'array', 'set', 'uf'])
def test_exact_legacy_occurrences_across_theories_and_binders(kind):
    x, y, z = z3.Ints('dep_x dep_y dep_z')
    p = z3.Bool('dep_p')
    a = z3.Array('dep_a', z3.IntSort(), z3.IntSort())
    s = z3.Const('dep_s', z3.SetSort(z3.IntSort()))
    expr = {
        'sum': x + y + x,
        'ite': z3.If(p, x + y, x - z),
        'forall': z3.ForAll(x, z3.Exists(z, x + y > z)),
        'exists': z3.Exists([y, z], z3.And(y == x, z > x)),
        'lambda': z3.Lambda(x, x + y),
        'array': z3.Select(z3.Store(a, x, y), z),
        'set': z3.IsMember(x, z3.SetAdd(s, y)),
        'uf': z3.Function('dep_f', z3.IntSort(), z3.IntSort())(x + y),
    }[kind]
    variables = [x, y, z, p, a, s]
    index = index_for(*variables)
    selections = [{v.get_id()} for v in variables] + [{v.get_id() for v in variables}, set()]
    for selected in selections:
        assert index.mentions(expr, selected) == definitions._mentions(expr, selected)
    if kind in ('forall', 'lambda'):
        assert x.get_id() not in index.mentions(expr, {v.get_id() for v in variables})


def test_reject_cross_context_even_if_ast_ids_collide():
    c1, c2 = z3.Context(), z3.Context()
    x, y = z3.Int('same', ctx=c1), z3.Int('same', ctx=c2)
    with pytest.raises(ValueError, match='context'):
        index_for(x).mentions(y, {x.get_id()})
    with pytest.raises(ValueError, match='context'):
        # Context-local AST IDs can collide; keep both inputs in this negative
        # test instead of losing one in index_for's same-context ID dictionary.
        definitions._WitnessDependencyIndex({0: x, 1: y})


def test_reject_nonconstant_or_unindexed_witness():
    x, y = z3.Ints('dep_invalid_x dep_invalid_y')
    with pytest.raises(ValueError, match='constants'):
        index_for(x + y)
    with pytest.raises(ValueError, match='unindexed'):
        index_for(x).mentions(y, {y.get_id()})


def test_shared_deep_dag_is_indexed_once_without_python_recursion(monkeypatch):
    variables = z3.Ints(' '.join('dep_shared_' + str(i) for i in range(128)))
    index = index_for(*variables)
    value = variables[0]
    for i in range(2400):
        value = z3.If(variables[i % 128] < i, value + 1, value - 1)
    expected = {v.get_id() for v in variables}
    assert index.mentions(value, expected) == definitions._mentions(value, expected) == expected
    nodes = len(index.memo)
    assert nodes < 15000
    def repeated_child_walk(*args):
        raise AssertionError('cached dependency query traversed a shared child again')
    with monkeypatch.context() as cache_check:
        cache_check.setattr(definitions.z3core, 'Z3_get_app_arg', repeated_child_walk)
        for i in range(512):
            variable = variables[i % len(variables)]
            assert index.mentions(value, {variable.get_id()}) == {variable.get_id()}
    assert len(index.memo) == nodes  # Repeated calls cannot revisit the shared DAG.
    assert isinstance(index.memo[value.get_id()], int)


def test_sparse_high_ordinal_stays_sparse_and_dense_union_is_exact():
    variables = [z3.Int('dep_sparse_' + str(i)) for i in range(8193)]
    index = index_for(*variables)
    high = variables[-1] + 1
    assert index.mentions(high, {variables[-1].get_id()}) == {variables[-1].get_id()}
    assert isinstance(index.memo[high.get_id()], frozenset)
    dense = z3.Sum(*variables[:128])
    expected = {v.get_id() for v in variables[:128]}
    assert index.mentions(dense, expected) == expected
    assert isinstance(index.memo[dense.get_id()], int)
    combined = dense + variables[-1]
    assert index.mentions(combined, set(index.identities)) == expected | {variables[-1].get_id()}


def test_roots_retain_temporary_ast_ids_and_extend_after_rewrite():
    x, y = z3.Ints('dep_hold_x dep_hold_y')
    index = index_for(x, y)
    first = x + 123
    first_id = first.get_id()
    assert index.mentions(first, {x.get_id(), y.get_id()}) == {x.get_id()}
    del first
    gc.collect()
    assert index.roots[first_id].eq(x + 123)
    second = z3.substitute(index.roots[first_id], (x, y + 1))
    assert index.mentions(second, {x.get_id(), y.get_id()}) == {y.get_id()}
    assert index.mentions(index.roots[first_id], {x.get_id(), y.get_id()}) == {x.get_id()}
    new_round = index_for(y)
    assert new_round.mentions(second, {y.get_id()}) == {y.get_id()}


def test_nested_bound_names_do_not_capture_free_witness_identity():
    x, y = z3.Ints('dep_bind_x dep_bind_y')
    expr = z3.ForAll(x, z3.Exists(y, x > y))
    assert index_for(x, y).mentions(expr, {x.get_id(), y.get_id()}) == set()
    mixed = z3.And(x == y, expr)
    assert index_for(x, y).mentions(mixed, {x.get_id(), y.get_id()}) == {x.get_id(), y.get_id()}


@pytest.mark.parametrize('case', ['chain', 'cycle', 'linear', 'nonunit', 'conflict', 'conditional', 'or_cover', 'domain', 'cost', 'nested'])
def test_projection_matches_legacy_and_complete_original_relation(monkeypatch, case):
    x, y, z, public, first_cost, second_cost = z3.Ints('dep_px dep_py dep_pz dep_public dep_c0 dep_c1')
    guard, other = z3.Bools('dep_guard dep_other')
    forms = {
        'chain': z3.And(x == public + 1, y == x + 2, z == y + 3, z < 20),
        'cycle': z3.And(x == y, y == z, z == x, x >= public),
        'linear': z3.And(x + 2*y == public, y == 4, x >= 0),
        'nonunit': z3.And(2*x == public, y == x + 1),
        'conflict': z3.And(x == public, x == public + 1, y == x),
        'conditional': z3.And(z3.Implies(guard, x == 1), z3.Implies(z3.Not(guard), x == 2), y == x, y == public),
        'or_cover': z3.And(z3.Implies(z3.Or(guard, other), x == 3), z3.Or(guard, other, x == 5), y == x, public == y),
        'domain': z3.And(x == public, x >= 1, x <= 4, y == x + 1, y != 3),
        'cost': z3.And(x == public + 1, y == 2*x, first_cost == x, second_cost == -y, x >= 0),
        'nested': z3.And(x == public, z3.ForAll(z, z3.Implies(z >= 0, x + z >= y)), y == x - 1),
    }
    original = z3.Exists([x, y, z], forms[case])
    indexed = definitions.eliminate_existential_definitions(original)
    with monkeypatch.context() as legacy:
        legacy.setattr(definitions, '_WitnessDependencyIndex', lambda variables: None)
        old = definitions.eliminate_existential_definitions(original)
    assert (indexed.direct_definitions, indexed.conditional_definitions) == (old.direct_definitions, old.conditional_definitions)
    unsat(z3.Xor(original, indexed.formula))
    unsat(z3.Xor(original, old.formula))
    unsat(z3.Xor(indexed.formula, old.formula))


def test_self_occurrence_and_missing_guard_do_not_invent_definitions():
    x, public = z3.Ints('dep_bad_x dep_bad_public')
    g = z3.Bool('dep_bad_g')
    original = z3.Exists(x, z3.And(z3.Implies(g, x == x + 1), x == public))
    result = definitions.eliminate_existential_definitions(original).formula
    unsat(z3.Xor(original, result))
    unsat(z3.And(result, g))
    solver = z3.Solver(); solver.add(result, z3.Not(g)); assert solver.check() == z3.sat


def test_ordered_signed_cost_counterexample_is_preserved():
    x, y, public, c0, c1 = z3.Ints('dep_cost_x dep_cost_y dep_cost_public dep_cost_0 dep_cost_1')
    original = z3.Exists([x, y], z3.And(x == public + 2, y == 3*x, c0 == x, c1 == -y, x >= 0))
    result = definitions.eliminate_existential_definitions(original).formula
    solver = z3.Solver(); solver.add(result, public == 1, c0 == 3, c1 == -9); assert solver.check() == z3.sat
    unsat(z3.And(result, public == 1, c0 == -9, c1 == 3))
    unsat(z3.Xor(original, result))
