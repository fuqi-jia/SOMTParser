"""Objective labels cannot capture source scalar, matrix or parameter names."""
import re

import pytest
import somtparser as sp
import z3


@pytest.mark.parametrize('kind', ['scalar', 'parameter', 'matrix'])
@pytest.mark.parametrize('after', [False, True])
@pytest.mark.parametrize('direction', ['minimising', 'maximising'])
@pytest.mark.parametrize('dialect_name', ['Z3', 'SmtLib2025', 'OptiMathSAT'])
def test_objective_binding_preserves_all_source_names(kind, after, direction, dialect_name):
    x, obj, obj1 = z3.Ints('x obj obj1')
    expected = [x >= 0, x <= 3]
    if kind == 'scalar':
        declarations = 'find obj,obj1 : int(0..1)\n'
        expected += [obj >= 0, obj <= 1, obj1 >= 0, obj1 <= 1]
    elif kind == 'parameter':
        declarations = 'letting obj = 7\nletting obj1 = [1,2]\n'
    else:
        declarations = 'find obj : matrix indexed by [int(2..3)] of int(0..1)\nletting obj1 = 2\n'
        array = z3.Array('obj', z3.IntSort(), z3.IntSort())
        expected += [array[2] >= 0, array[2] <= 1, array[3] >= 0, array[3] <= 1]
    goal = direction + ' x\n'
    source = ("language ESSENCE' 1.0\nfind x : int(0..3)\n"
              + (goal + declarations if after else declarations + goal)
              + 'such that true')
    dialect = getattr(sp.OmtDialect, dialect_name)
    result = sp.translate(source=source, language='essence', dialect=dialect)
    assert result.ok, [d.message for d in result.diagnostic_items]
    assert result.report.fidelity.sound and result.report.fidelity.complete
    script = result.to_smt2(dialect)
    command = 'minimize' if direction == 'minimising' else 'maximize'
    if dialect_name == 'SmtLib2025':
        matches = re.findall(r'^\(define-objective (\S+) (OBJECTIVE_MIN|OBJECTIVE_MAX) (.*)\)$', script, re.M)
        assert len(matches) == 1
        label, sense, expression = matches[0]
        assert label not in {'x', 'obj', 'obj1'}
        assert sense == ('OBJECTIVE_MIN' if command == 'minimize' else 'OBJECTIVE_MAX')
        assert expression == 'x'
        assert script.count('(optimize-sat ' + label + ')') == 1
        # Read the complete GOMT script, including its dialect options, before
        # checking the preserved relation and objective with Z3.
        script = sp.parse(script).dump_smt2(dialect=sp.OmtDialect.Z3)
    else:
        assert script.count('(' + command + ' x)') == 1
    parser = z3.Optimize()
    parser.from_string(script)
    solver = z3.Solver()
    solver.add(z3.Xor(z3.And(*parser.assertions()), z3.And(*expected)))
    assert solver.check() == z3.unsat
    assert len(parser.objectives()) == 1
    signed = x if command == 'minimize' else -x
    solver = z3.Solver()
    solver.add(parser.objectives()[0] != signed)
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('text', ['+1.5', '-1.5', '+3/2', '-3/2', '+0.0', '+0007',
    '+340282366920938463463374607431768211457/3',
    '+340282366920938463463374607431768211457.0000000000000000001'])
@pytest.mark.parametrize('maximize', [False, True])
def test_direct_hir_real_spelling_preserves_exact_relation_and_objective(text, maximize):
    from somtparser import _somtparser as native
    model = native.HirModel()
    sort = native.HirSort.real()
    x = model.declare('x', sort)
    literal = native._hir_literal(sort, text)
    model.constrain(native._hir_op('eq', [x, literal]))
    model.objective(maximize, literal)
    result = model.translate()
    assert result.ok, [d.message for d in result.diagnostic_items]
    parser = z3.Optimize()
    parser.from_string(result.to_smt2(sp.OmtDialect.Z3))
    expected = z3.RealVal(text.lstrip('+'))
    solver = z3.Solver()
    solver.add(z3.Xor(z3.And(*parser.assertions()), z3.Real('x') == expected))
    assert solver.check() == z3.unsat
    assert len(parser.objectives()) == 1
    solver = z3.Solver()
    solver.add(parser.objectives()[0] != (-expected if maximize else expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('text', ['+', '++1.5', '+.5', '+1.', '+1/-2', '+1e2', '+ 1.5', '+1/'])
def test_malformed_hir_real_spelling_is_not_repaired(text):
    from somtparser import _somtparser as native
    with pytest.raises(ValueError, match='unsupported HIR literal'):
        native._hir_literal(native.HirSort.real(), text)


@pytest.mark.parametrize('profile', ['default', 'ground', 'quantified'])
@pytest.mark.parametrize('direction', ['minimize', 'maximize'])
def test_flatzinc_signed_real_bounds_initializer_and_goal(profile, direction):
    source = ('var +0.0..+2.0: x = +1.5; '
              'solve :: float_search([x],0.01,input_order,indomain_split,complete) '
              + direction + ' x;')
    result = sp.translate(source=source, language='flatzinc', profile=profile, dialect=sp.OmtDialect.Z3)
    assert result.ok, [d.message for d in result.diagnostic_items]
    parser = z3.Optimize()
    parser.from_string(result.to_smt2(sp.OmtDialect.Z3))
    x = z3.Real('x')
    solver = z3.Solver()
    solver.add(z3.Xor(z3.And(*parser.assertions()), x == z3.RealVal('1.5')))
    assert solver.check() == z3.unsat
    assert len(parser.objectives()) == 1
    solver = z3.Solver()
    solver.add(parser.objectives()[0] != (x if direction == 'minimize' else -x))
    assert solver.check() == z3.unsat
