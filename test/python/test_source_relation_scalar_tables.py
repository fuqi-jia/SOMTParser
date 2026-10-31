"""Literal lookup tables retain their total semantics inside relation projection."""
import pytest
import z3

from tools.semantic_checks.source_oracles.fzn_json_source import Source
from tools.semantic_checks.source_oracles.target_relation import compare


def contains_array_operation(expression):
    pending, seen = [expression], set()
    while pending:
        node = pending.pop()
        if node.get_id() in seen:
            continue
        seen.add(node.get_id())
        if z3.is_quantifier(node):
            pending.append(node.body())
        elif z3.is_app(node):
            if node.decl().kind() in (z3.Z3_OP_SELECT, z3.Z3_OP_STORE, z3.Z3_OP_CONST_ARRAY):
                return True
            pending.extend(node.children())
    return False


def assert_equivalent(left, right):
    solver = z3.Solver()
    solver.add(z3.Xor(left, right))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('direction', ['minimize', 'maximize'])
def test_private_table_index_is_scalarized_before_existential_binding(direction):
    hidden, value, public, cost = z3.Ints('hidden value public cost')
    table = z3.Store(z3.Store(z3.Store(z3.K(z3.IntSort(), 7), -3, 1), 5, 2), -3, 7)
    source = Source({'hidden': hidden, 'value': value}, {},
                    [hidden >= -3, hidden <= 6, value == z3.Select(table, hidden)],
                    value, direction, ())
    result = source.projected([(public, value)], signed_cost=cost)
    assert z3.is_quantifier(result)
    assert not contains_array_operation(result)
    signed = public if direction == 'minimize' else -public
    assert_equivalent(result, z3.And(z3.Or(public == 7, public == 2), cost == signed))


def test_boolean_table_preserves_negative_keys_and_unbounded_true_default():
    index, public = z3.Ints('index public_index')
    flag, observed = z3.Bools('flag public_flag')
    table = z3.Store(z3.K(z3.IntSort(), True), -2, False)
    source = Source({'index': index, 'flag': flag}, {},
                    [flag == z3.Select(table, index)], None, 'satisfy', ())
    relation = source.projected([(public, index), (observed, flag)])
    assert not contains_array_operation(relation)
    assert_equivalent(relation, observed == (public != -2))


def observations(index, value):
    return [dict(name=name, value=term, indices=None, dimensions=[])
            for name, term in [('index', index), ('value', value)]]


def target(*, direction='minimize', default=7, overwrite=True, guard='true'):
    table = f'(store (store ((as const (Array Int Int)) {default}) (- 3) 1) 5 2)'
    if overwrite:
        table = f'(store {table} (- 3) 7)'
    return (f'(declare-const index Int)\n(declare-const value Int)\n'
            f'(assert (= value (select {table} index)))\n(assert {guard})\n'
            f'({direction} value)\n(check-sat)\n(exit)').encode()


@pytest.mark.parametrize('direction', ['minimize', 'maximize'])
def test_complete_joint_relation_matches_total_table_and_signed_cost(direction):
    index, value = z3.Ints('index value')
    source = Source({'index': index, 'value': value}, {},
                    [value == z3.If(index == 5, 2, 7)], value, direction, ())
    result = compare(source, observations(index, value), target(direction=direction), solve=True)
    assert result['equivalent'], result
    assert result['all_source_constraints_retained'] and result['all_target_assertions_retained']
    assert result['finite_scalar_tables']['completed']
    # Earlier exact simplification may already remove these literal stores.
    # The contract is equality of the complete relation, not a rewrite count.


@pytest.mark.parametrize('change', ['wrong-default', 'missing-last-write', 'invented-index-bound'])
def test_incorrect_default_shadowing_or_domain_is_still_a_real_counterexample(change):
    index, value = z3.Ints('index value')
    source = Source({'index': index, 'value': value}, {},
                    [value == z3.If(index == 5, 2, 7)], value, 'minimize', ())
    options = {'wrong-default': dict(default=0), 'missing-last-write': dict(overwrite=False),
               'invented-index-bound': dict(guard='(and (<= 0 index) (<= index 5))')}[change]
    result = compare(source, observations(index, value), target(**options), solve=True)
    assert not result['equivalent'] and result['solver_answer'] == 'sat', result
    assert result['counterexample'] is not None


def test_unobserved_table_value_remains_part_of_the_feasible_relation():
    index, hidden = z3.Ints('index hidden')
    source = Source({'index': index, 'hidden': hidden}, {},
                    [hidden == z3.If(index == 5, 2, 7), hidden < 3], None, 'satisfy', ())
    rows = [dict(name='index', value=index, indices=None, dimensions=[])]
    complete = b'(declare-const index Int)\n(assert (= index 5))\n(check-sat)\n(exit)'
    lost_constraint = b'(declare-const index Int)\n(assert true)\n(check-sat)\n(exit)'
    assert compare(source, rows, complete, solve=True)['equivalent']
    wrong = compare(source, rows, lost_constraint, solve=True)
    assert not wrong['equivalent'] and wrong['solver_answer'] == 'sat'


def test_existing_binders_are_preserved_while_outer_literal_tables_normalize():
    index, local, public = z3.Ints('index local public')
    literal = z3.Store(z3.K(z3.IntSort(), 0), 2, 9)
    nested = z3.ForAll([local], z3.Select(literal, local) >= 0)
    source = Source({'index': index}, {}, [nested, z3.Select(literal, index) == 9],
                    None, 'satisfy', ())
    result = source.projected([(public, index)])
    assert contains_array_operation(result)  # The pre-existing binder is untouched.
    assert_equivalent(result, public == 2)
