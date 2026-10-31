"""Annotated FlatZinc goals preserve feasibility and pointwise signed objectives."""
import pytest
import z3
import somtparser as sp

PROFILES = ['default', 'ground', 'quantified']
ANNOTATIONS = [
    '',
    ':: int_search([x], input_order, indomain_min, complete)',
    ':: seq_search([int_search([x], first_fail, indomain_min, complete)]) :: restart_none',
    r':: note("maximize minimize satisfy ) ] } = :: ; % \\\"quoted\\\"") :: minimize_hint',
]


def translate(source, profile):
    result = sp.translate(source=source, language='flatzinc', profile=profile,
                          dialect=sp.OmtDialect.Z3)
    assert result.ok, [d.message for d in result.diagnostic_items]
    assert result.report.fidelity.sound and result.report.fidelity.complete
    parser = z3.Optimize()
    parser.from_string(result.to_smt2(sp.OmtDialect.Z3))
    return parser


def same_relation(actual, expected):
    solver = z3.Solver()
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('profile', PROFILES)
@pytest.mark.parametrize('annotation', ANNOTATIONS)
@pytest.mark.parametrize('direction', ['minimize', 'maximize'])
@pytest.mark.parametrize('term', ['obj', '-7', 'p'])
def test_complete_feasible_relation_and_signed_objective(profile, annotation, direction, term):
    x, obj, obj1, obj2 = z3.Ints('x obj obj1 obj2')
    expected = z3.And(x >= -2, x <= 2, obj >= -3, obj <= 5, obj == 2*x+1,
                      z3.Or(obj1 == 2, obj1 == 4), obj2 >= 0, obj2 <= 1)
    source = ('int: p = -9; var -2..+2: x; var -3..+5: obj; '
              'var {+2,+4}: obj1; var +0..+1: obj2; '
              'constraint int_lin_eq([2,-1],[x,obj],-1); '
              f'solve {annotation} {direction} {term};')
    parser = translate(source, profile)
    actual = z3.And(*parser.assertions())
    same_relation(actual, expected)
    objectives = parser.objectives()
    assert len(objectives) == 1
    expression = obj if term == 'obj' else z3.IntVal(-7 if term == '-7' else -9)
    signed = -expression if direction == 'maximize' else expression
    solver = z3.Solver()
    solver.add(actual, objectives[0] != signed)
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('profile', PROFILES)
@pytest.mark.parametrize('direction', ['minimize', 'maximize'])
def test_real_objective_direction_and_expression(profile, direction):
    x = z3.Real('x')
    parser = translate(f'var -1.5..2.5: x; solve :: float_search([x],0.01,input_order,indomain_split,complete) {direction} x;', profile)
    actual = z3.And(*parser.assertions())
    same_relation(actual, z3.And(x >= z3.RealVal('-1.5'), x <= z3.RealVal('2.5')))
    assert len(parser.objectives()) == 1
    solver = z3.Solver()
    solver.add(actual, parser.objectives()[0] != (-x if direction == 'maximize' else x))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('profile', PROFILES)
@pytest.mark.parametrize('annotation', ANNOTATIONS)
def test_satisfaction_has_no_objective(profile, annotation):
    x = z3.Int('x')
    parser = translate(f'var -2..2: x; solve {annotation} satisfy;', profile)
    same_relation(z3.And(*parser.assertions()), z3.And(x >= -2, x <= 2))
    assert len(parser.objectives()) == 0


@pytest.mark.parametrize('goal', [
    '', ':: restart_none', ':: note("minimize x")', '::',
    'maximizex x', 'minimizex x', 'satisfyx', 'minimize', 'maximize',
    ':: minimize x', ':: maximize x', ':: satisfy',
    ':: note("maximize") bogus minimize x', 'bogus minimize x',
])
def test_missing_or_malformed_goal_is_rejected(goal):
    result = sp.translate(source=f'var -2..2: x; solve {goal};', language='flatzinc')
    assert not result.ok


@pytest.mark.parametrize('profile', PROFILES)
@pytest.mark.parametrize('annotation', [
    r':: note(") = phantom")',
    r':: note("\\\" ) = phantom \\\"")',
    r':: note(["=", ")"], inner({1,2}, "minimize"))',
    r':: note("; % :: = )") :: output_var',
])
@pytest.mark.parametrize('initialized', [False, True])
def test_quoted_declaration_annotations_preserve_initializer(profile, annotation, initialized):
    x = z3.Int('x')
    initializer = ' = +7' if initialized else ''
    parser = translate(f'var +0..+9: x {annotation}{initializer}; solve maximize x;', profile)
    expected = z3.And(x >= 0, x <= 9, x == 7) if initialized else z3.And(x >= 0, x <= 9)
    actual = z3.And(*parser.assertions())
    same_relation(actual, expected)
    assert len(parser.objectives()) == 1
    solver = z3.Solver()
    solver.add(actual, parser.objectives()[0] != -x)
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('profile', PROFILES)
@pytest.mark.parametrize('goal,expected', [('minimize-7', -7), ('maximize+7', -7)])
def test_objective_tokens_do_not_require_whitespace(profile, goal, expected):
    parser = translate('solve::restart_none ' + goal + ';', profile)
    assert len(parser.objectives()) == 1
    solver = z3.Solver()
    solver.add(parser.objectives()[0] != expected)
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('source', ['solveminimize 1;', 'solvemaximize 1;',
                                   'solvesatisfy;', 'solve_goal satisfy;'])
def test_solve_keyword_requires_a_token_boundary(source):
    assert not sp.translate(source=source, language='flatzinc').ok


@pytest.mark.parametrize('text', ['+7', '-7', '+0007', '-0',
    '+340282366920938463463374607431768211457',
    '-340282366920938463463374607431768211457'])
@pytest.mark.parametrize('maximize', [False, True])
def test_direct_hir_integer_spelling_preserves_constraint_and_objective(text, maximize):
    from somtparser import _somtparser as native
    model = native.HirModel()
    sort = native.HirSort.integer()
    x = model.declare('x', sort)
    literal = native._hir_literal(sort, text)
    model.constrain(native._hir_op('eq', [x, literal]))
    model.objective(maximize, literal)
    result = model.translate()
    assert result.ok, [d.message for d in result.diagnostic_items]
    parser = z3.Optimize()
    parser.from_string(result.to_smt2(sp.OmtDialect.Z3))
    expected = int(text)
    same_relation(z3.And(*parser.assertions()), z3.Int('x') == expected)
    assert len(parser.objectives()) == 1
    solver = z3.Solver()
    solver.add(parser.objectives()[0] != (-expected if maximize else expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('text', ['+', '++7', '+-7', '+7x', '+ 7', '7+'])
def test_direct_hir_invalid_integer_text_is_not_repaired(text):
    from somtparser import _somtparser as native
    with pytest.raises(ValueError, match='unsupported HIR literal'):
        native._hir_literal(native.HirSort.integer(), text)
