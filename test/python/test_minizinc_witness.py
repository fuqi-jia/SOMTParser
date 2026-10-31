"""Exact MiniZinc observables, using official 2.10.1 OZN/JSON fixtures.

All five fixtures also passed independent original-model replay in MiniZinc.
"""
from decimal import Decimal
import hashlib
import json
from pathlib import Path

import pytest

from tools.semantic_checks.source_oracles import minizinc_witness as witness


CASES = json.loads((Path(__file__).parent / 'fixtures' /
                   'minizinc_witness_official_2_10_1.json').read_text())['cases']


def read_case(name):
    row = CASES[name]
    original = row['source'].encode()
    assert hashlib.sha256(original).hexdigest() == row['source_sha256']
    schema = witness.observation_schema(row['official_ozn'], row['declarations'], original)
    value = witness.solution_stream(row['stream'], witness.source_method(row['source']))
    return schema, value


@pytest.mark.parametrize('name', sorted(CASES))
def test_official_complete_assignment(name):
    schema, value = read_case(name)
    assert value['status'] == 'sat' and value['optimal'] is True
    projection, assignment = witness.project_solution(
        schema, value['solution'], flatten_multidimensional_arrays=True)
    assert projection == witness.projection_schema(schema, flatten_multidimensional_arrays=True)
    assert assignment == CASES[name]['expected_witness']
    assert value['original_objective_values'] == CASES[name]['expected_objectives']
    assert witness.witness_constraints(schema, projection, assignment).count('constraint ') == len(assignment)
    del assignment[next(iter(assignment))]
    with pytest.raises(ValueError, match='complete reverse witness coverage'):
        witness.witness_constraints(schema, projection, assignment)


def test_multidimensional_original_indices_and_target_layout():
    schema, value = read_case('integer_opt')
    projection, assignment = witness.project_solution(
        schema, value['solution'], flatten_multidimensional_arrays=True)
    assert [row['source_indices'] for row in projection] == [[0, -2], [0, -1], [1, -2], [1, -1]]
    assert [row['indices'] for row in projection] == [[0], [1], [2], [3]]
    assert 'constraint x[0,-2] = ' in witness.witness_constraints(schema, projection, assignment)
    with pytest.raises(ValueError, match='layout contract'):
        witness.projection_schema(schema, flatten_multidimensional_arrays=False)


def test_composite_enums_and_numeric_bounds_are_distinct():
    schema, value = read_case('composite_enum')
    rows = {row['name']: row for row in schema['observables']}
    assert rows['x']['source_enum'] == 'PAD'
    assert rows['distance']['source_enum'] is None
    assert schema['enum_tables']['PAD'] == [
        {'e': 'Dummy'}, {'c': 'Pin', 'e': {'e': 'red'}},
        {'c': 'Pin', 'e': {'e': 'blue'}}, {'c': 'Link', 'e': 2}, {'c': 'Link', 'e': 3}]
    projection, assignment = witness.project_solution(
        schema, value['solution'], flatten_multidimensional_arrays=True)
    constraints = witness.witness_constraints(schema, projection, assignment)
    assert 'constraint x[to_enum(PAD,4)] = to_enum(PAD,4);' in constraints
    assert 'constraint distance[to_enum(PAD,1)] = 0;' in constraints
    with pytest.raises(ValueError, match='absent or duplicated'):
        witness.typed_value({'c': 'Link', 'e': 99}, ['int'], schema['enum_tables'], 'PAD')
    with pytest.raises(ValueError, match='enum type not established'):
        witness.typed_value({'e': 'red'}, ['int'])


@pytest.mark.parametrize('value', [1.1, True, Decimal('NaN'), Decimal('Infinity')])
def test_nonexact_numeric_input_rejected(value):
    with pytest.raises(ValueError):
        witness.typed_number(value)


def test_decimal_objective_is_exact():
    value = witness.solution_stream([
        '{"type":"solution","output":{"json":{"x":0.1,"_objective":0.1}}}',
        '{"type":"status","status":"OPTIMAL_SOLUTION"}'], 'minimize')
    assert value['original_objective_values'] == [{'type': 'real', 'numerator': '1', 'denominator': '10'}]


def test_incumbent_is_not_optimum():
    value = witness.solution_stream([
        '{"type":"solution","output":{"json":{"x":2,"_objective":2}}}',
        '{"type":"status","status":"UNKNOWN"}'], 'minimize')
    assert value['status'] == 'sat' and value['optimal'] is False


def test_unknown_and_unsat_remain_distinct():
    assert witness.solution_stream(['{"type":"status","status":"UNKNOWN"}'], 'satisfy')['status'] == 'unknown'
    assert witness.solution_stream(['{"type":"status","status":"UNSATISFIABLE"}'], 'satisfy')['status'] == 'unsat'
    with pytest.raises(ValueError, match='UNSAT stream also contains'):
        witness.solution_stream([
            '{"type":"solution","output":{"json":{"x":2}}}',
            '{"type":"status","status":"UNSATISFIABLE"}'], 'satisfy')


def test_invalid_shape_and_extra_coordinates_rejected():
    schema, value = read_case('integer_opt')
    projection, assignment = witness.project_solution(
        schema, value['solution'], flatten_multidimensional_arrays=True)
    assignment['extra'] = {'type': 'int', 'value': '0'}
    with pytest.raises(ValueError, match='complete reverse witness coverage'):
        witness.witness_constraints(schema, projection, assignment)
    with pytest.raises(ValueError, match='extent mismatch'):
        witness.project_solution(schema, dict(value['solution'], x=[[1, 2]]), flatten_multidimensional_arrays=True)


def test_solve_annotations_do_not_change_direction():
    assert witness.source_method('solve :: int_search([x], input_order, indomain_min, complete) maximize x;') == 'maximize'
    with pytest.raises(ValueError, match='exactly one'):
        witness.source_method('solve satisfy; solve minimize x;')


def test_finite_set_normalization_preserves_every_member():
    assert witness.typed_value({'set': [[-2, 1], 4, 0]}, ['set', 'of', 'int']) == {
        'type': 'set-int', 'elements': ['-2', '-1', '0', '1', '4']}
    with pytest.raises(ValueError, match='finite-set range'):
        witness.typed_value({'set': [[3, 1]]}, ['set', 'of', 'int'])


def test_constructor_uses_official_carrier_when_source_parameter_is_folded():
    source = ('int: N = sum([1,2]); enum BUY = Buy(1..N); '
              'enum SELL = Sell(1..2); enum UNUSED = Gone(1..missing); '
              'array [SELL] of var BUY: origin; solve satisfy;')
    ozn = ('set of int: BUY = 1..3; set of int: SELL = 1..2; '
           'set of int: _constrId_0_BUY = 1..3; int: _constrMin_0_BUY = 0; '
           'set of int: _constrId_0_SELL = 1..2; int: _constrMin_0_SELL = 0; '
           'array [SELL] of int: origin;')
    declarations = [{'name': 'origin', 'statement_start': source.index('array ['),
                     'name_start': source.index('origin')}]
    schema = witness.observation_schema(ozn, declarations, source.encode())
    projection, assignment = witness.project_solution(schema, {'origin': [
        {'c': 'Buy', 'e': 2}, {'c': 'Buy', 'e': 3}]}, flatten_multidimensional_arrays=True)
    assert assignment == {'origin[1]': {'type': 'int', 'value': '2'},
                          'origin[2]': {'type': 'int', 'value': '3'}}
    assert witness.witness_constraints(schema, projection, assignment) == (
        'constraint origin[to_enum(SELL,1)] = to_enum(BUY,2);\n'
        'constraint origin[to_enum(SELL,2)] = to_enum(BUY,3);\n')
    assert 'UNUSED' not in schema['enum_tables']
    with pytest.raises(ValueError, match='ordinal offset differs'):
        witness.observation_schema(ozn.replace('_constrMin_0_BUY = 0', '_constrMin_0_BUY = 1'), declarations, source.encode())


def test_enum_constructor_boolean_is_not_integer_one():
    with pytest.raises(ValueError, match='absent or duplicated'):
        witness.typed_value({'c': 'Wrap', 'e': True}, ['int'], {'E': [{'c': 'Wrap', 'e': 1}]}, 'E')
