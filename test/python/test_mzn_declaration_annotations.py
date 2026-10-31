"""Declaration annotations must not hide initializers or model constraints."""
import pytest
import somtparser as sp
import z3


def translate(source):
    kwargs = dict(source=source, language='minizinc', dialect=sp.OmtDialect.Z3)
    result = sp.translate(**kwargs)
    assert result.ok, [d.message for d in result.diagnostic_items]
    return result


@pytest.mark.parametrize('sort,value,wrong', [
    ('int', '7', '8'), ('float', '1.5', '2.0'), ('bool', 'true', 'false'),
])
@pytest.mark.parametrize('annotations', [':: output', ':: output :: is_defined_var',
                                       ':: search_hint([1,2],nested({3,4}))',
                                       ':: search_hint(let { int: k = 1; } in k)'])
def test_scalar_initializer_and_declared_sort_remain_constraints(sort,value,wrong,annotations):
    result = translate(f'var {sort}: x {annotations} = {value}; constraint x = {wrong}; solve satisfy;')
    solver = z3.Solver(); solver.from_string(result.to_smt2(sp.OmtDialect.Z3))
    assert solver.check() == z3.unsat


def test_annotated_parameter_bounds_decision_arrays_holes_and_objective():
    result = translate(r'''
int: n :: output = 3;
float: weight :: output = 0.5;
bool: active :: output = true;
string: label :: output = "schedule";
array[1..n] of var 0..9: a :: output = [_,2,3];
array[int] of var int: shifted :: output = [a[i]+1 | i in 1..n];
var int: objective :: output = max(shifted);
constraint active /\ a[1] >= 4 /\ label = "schedule";
solve minimize objective;
''')
    solver = z3.Optimize(); solver.from_string(result.to_smt2(sp.OmtDialect.Z3))
    assert len(solver.objectives()) == 1
    assert solver.check() == z3.sat
    assert str(solver.model().eval(solver.objectives()[0])) == '5'
    a = z3.Array('a', z3.IntSort(), z3.IntSort())
    solver.add(a[1] == 10)
    assert solver.check() == z3.unsat


def test_parameter_assignment_items_still_supply_annotated_declarations():
    result = translate('int: n :: output; n = 2; array[1..n] of var int: x :: output = [3,4]; constraint x[2] != 4; solve satisfy;')
    solver = z3.Solver(); solver.from_string(result.to_smt2(sp.OmtDialect.Z3))
    assert solver.check() == z3.unsat


def test_annotated_partial_initializer_is_not_discarded():
    result = translate('var int: x :: output = 1 div 0; solve satisfy;')
    solver = z3.Solver(); solver.from_string(result.to_smt2(sp.OmtDialect.Z3))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('source', [
    'var int: x :: output = true;',
    'var int: x :: output = ;',
    'array[1..2] of var int: a :: output = [1];',
    'array[int] of var int: a :: output;',
    'var int: x :: hint([1,2)) = 4;',
    'var int: x :: hint({1,2]) = 4;',
    'var int: x :: hint([1,2] = 4;',
    'int: n :: output;',
    'var int: x :: output = 1; var int: x :: output = 2;',
])
def test_annotations_do_not_hide_invalid_initializers_or_declarations(source):
    assert not sp.translate(source=source+' solve satisfy;', language='minizinc').ok
