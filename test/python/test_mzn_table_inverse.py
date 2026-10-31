"""Extensional tables and inverse vectors checked against finite relations."""
import itertools
import pytest
import z3
import somtparser as sp
from somtparser import _somtparser as native


def translate(source):
    result = sp.translate(source=source, language='minizinc', dialect=sp.OmtDialect.Z3)
    assert result.ok, [d.message for d in result.diagnostic_items]
    return result, z3.And(*z3.parse_smt2_string(result.to_smt2(sp.OmtDialect.Z3)))


@pytest.mark.parametrize('negated', [False, True])
@pytest.mark.parametrize('boolean', [False, True])
def test_table_matches_membership_for_every_assignment(negated, boolean):
    typ = 'bool' if boolean else 'int'
    data = '[|false,true|true,false|false,true|]' if boolean else '[|0,2|1,-1|0,2|]'
    call = f'table(x, array2d(-2..0,4..5,{data}))'
    result, formula = translate(f'array[4..5] of var {typ}: x; constraint '
                                + ('not (' + call + ')' if negated else call) + '; solve satisfy;')
    assert 'table-row-disjunction' in result.report.to_json()
    domain = (False, True) if boolean else (-1, 0, 1, 2)
    table = {(False, True), (True, False)} if boolean else {(0, 2), (1, -1)}
    x = z3.Array('x', z3.IntSort(), z3.BoolSort() if boolean else z3.IntSort())
    solver = z3.Solver(); solver.add(formula)
    for a, b in itertools.product(domain, repeat=2):
        solver.push(); solver.add(x[4] == a, x[5] == b)
        assert solver.check() == (z3.sat if (((a, b) in table) != negated) else z3.unsat)
        solver.pop()


@pytest.mark.parametrize('negated', [False, True])
def test_inverse_shifted_indices_and_out_of_domain_values(negated):
    call = 'inverse(f,g)'
    result, formula = translate('array[-1..0] of var int: f; array[3..4] of var int: g; constraint '
                                + ('not (' + call + ')' if negated else call) + '; solve satisfy;')
    assert 'inverse-bidirectional-matching' in result.report.to_json()
    f = z3.Array('f', z3.IntSort(), z3.IntSort()); g = z3.Array('g', z3.IntSort(), z3.IntSort())
    solver = z3.Solver(); solver.add(formula)
    for left in itertools.product(range(2, 6), repeat=2):
        for right in itertools.product(range(-2, 2), repeat=2):
            expected = (all(3 <= x <= 4 and right[x-3] == i-1 for i,x in enumerate(left))
                        and all(-1 <= y <= 0 and left[y+1] == j+3 for j,y in enumerate(right)))
            solver.push(); solver.add(f[-1] == left[0], f[0] == left[1], g[3] == right[0], g[4] == right[1])
            assert solver.check() == (z3.sat if expected != negated else z3.unsat), (left, right)
            solver.pop()


@pytest.mark.parametrize('expression, expected', [
    ('table([1], array2d(1..0,1..1,[]))', False),
    ('table([], array2d(1..0,1..0,[]))', False),
    ('table([], array2d(1..2,1..0,[]))', True),
    ('inverse([],[])', True), ('inverse([],[1])', False),
    ('inverse([1],[1])', True), ('inverse([1,1],[1,2])', False),
    ('not table([1 div 0], array2d(1..1,1..1,[1]))', True),
    ('not inverse([1 div 0],[1])', True),
])
def test_empty_degenerate_and_partial_relations(expression, expected):
    _, formula = translate(f'constraint {expression}; solve satisfy;')
    s = z3.Solver(); s.add(formula)
    assert s.check() == (z3.sat if expected else z3.unsat)


def test_dependent_table_comprehensions_preserve_objective():
    result, formula = translate('''
array[1..2] of int: sizes = [2,1];
array[1..2] of var int: x;
constraint forall(i in 1..2)(table([x[i]],array2d(1..sizes[i],1..1,[j+i | j in 1..sizes[i]])));
solve minimize sum(x);
''')
    opt = z3.Optimize(); opt.from_string(result.to_smt2(sp.OmtDialect.Z3))
    assert len(opt.objectives()) == 1 and opt.check() == z3.sat
    assert str(opt.model().eval(opt.objectives()[0])) == '5'


@pytest.mark.parametrize('source', [
    'constraint table([1,2], array2d(1..1,1..1,[1]));',
    'array[3..3] of var int: x; constraint table(x,[|1|]);',
    'constraint table([1], [1]);', 'constraint table([1], [|true|]);',
    'constraint table([true,1], [|true,1|]);',
    'constraint table([1], [|1|2,3|]);',
    'var int: a; constraint table([1], array2d(1..1,1..1,[a]));',
    'constraint inverse([true],[1]);',
    'constraint inverse(array2d(1..1,1..1,[1]), [1]);',
])
def test_wrong_shapes_types_and_decision_tables_are_refused(source):
    assert not sp.translate(source=source+' solve satisfy;', language='minizinc').ok


@pytest.mark.parametrize('name, values', [
    ('table', [-1, 0]), ('table', [2,1,1,2,1]), ('table', [1,-1,1]),
    ('table', [0,2,3]), ('table', ['99999999999999999999999',0]),
    ('inverse', [0,0,-1]), ('inverse',[0,0,2,1]),
])
def test_native_global_shapes_are_checked_before_decomposition(name, values):
    model = native.HirModel()
    args = [native._hir_literal(native.HirSort.integer(), str(v)) for v in values]
    model.constrain(native._hir_global(name,args))
    assert not model.translate().ok


@pytest.mark.parametrize('positive', [False, True])
def test_natural_language_hir_cp_table_uses_shared_native_global(positive):
    from somtparser.hir import HirBuilder
    builder = HirBuilder()
    builder.declare('x', 'Int')
    builder.constrain({'cp': 'table', 'items': [{'var':'x'}],
                       'tuples': [[-2], [4], [4]], 'positive': positive})
    result = builder.translate()
    assert result.ok, [d.message for d in result.diagnostic_items]
    assert 'table-row-disjunction' in result.report.to_json()
    formula = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    expected = z3.Or(z3.Int('x') == -2, z3.Int('x') == 4)
    solver = z3.Solver()
    solver.add(z3.Xor(formula, expected if positive else z3.Not(expected)))
    assert solver.check() == z3.unsat
