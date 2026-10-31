"""Shared box non-overlap semantics, including strict zero-sized boxes."""
import itertools
import pytest
import z3
import somtparser as sp
from somtparser import _somtparser as native
from somtparser.hir import build_hir, hir_api
from somtparser.hir_cp import expand_cp_model
from somtparser._nl_model import ModelError


def model(expr, names=()):
    return dict(schema='somt-hir-model-v1', language='hir', decision='satisfiability',
                declarations=[dict(name=name, sort='Int') for name in names], functions=[],
                constraints=[dict(expr=expr, span=[0,1])], objectives=[],
                objective_order='single', goal=None, assumptions=[], unresolved=[])


def formula(result):
    assert result.ok, [d.message for d in result.diagnostic_items]
    return z3.And(*z3.parse_smt2_string(result.to_smt2(sp.OmtDialect.Z3)))


@pytest.mark.parametrize('nonstrict', [False, True])
@pytest.mark.parametrize('negated', [False, True])
def test_variable_boxes_match_independent_interior_grid(nonstrict, negated):
    names = ['x', 'y', 'w', 'h']
    variables = z3.Ints(' '.join(names))
    expr = dict(cp='diffn', dimensions=2, positions=[[0,0],[{'var':'x'},{'var':'y'}]],
                sizes=[[2,2],[{'var':'w'},{'var':'h'}]], nonstrict=nonstrict)
    if negated:
        expr = {'op':'not', 'args':[expr]}
    candidate = model(expr, names)
    result = build_hir(candidate, 'x').translate()
    actual = formula(result)
    assert 'diffn-separating-axis' in result.report.to_json()
    # Sample open interiors on a doubled integer grid. A zero-length interval
    # contributes its point for strict diffn; the other box has positive sizes.
    def interior(start, width):
        return {2*start} if width == 0 else set(range(2*start+1, 2*(start+width)))
    accepted = []
    for x,y,w,h in itertools.product(range(-2,4),range(-2,4),range(3),range(3)):
        overlaps = bool({1,2,3} & interior(x,w)) and bool({1,2,3} & interior(y,h))
        holds = (nonstrict and (w==0 or h==0)) or not overlaps
        if holds != negated:
            accepted.append(z3.And(*[v==a for v,a in zip(variables,(x,y,w,h))]))
    solver = z3.Solver(); solver.set(timeout=10000)
    solver.add(variables[0]>=-2,variables[0]<=3,variables[1]>=-2,variables[1]<=3,
               variables[2]>=0,variables[2]<=2,variables[3]>=0,variables[3]<=2)
    solver.add(z3.Xor(actual,z3.Or(*accepted)))
    assert solver.check()==z3.unsat
    expanded = formula(build_hir(expand_cp_model(candidate),'x').translate())
    solver = z3.Solver(); solver.set(timeout=10000)
    solver.add(z3.Xor(actual,expanded))
    assert solver.check()==z3.unsat


@pytest.mark.parametrize('call,expected', [
    ('diffn([0,1],[0,1],[2,0],[2,0])',False),
    ('diffn_nonstrict([0,1],[0,1],[2,0],[2,0])',True),
    ('diffn([0,2],[0,0],[2,1],[2,1])',True),
    ('diffn([],[],[],[])',True),
    ('diffn([0],[0],[1],[1])',True),
    ('diffn([1,1],[1,1],[0,0],[0,0])',True),
    ('not diffn([1 div 0],[0],[1],[1])',True),
    ('diffn_k(array2d(4..5,-1..1,[0,0,0,0,0,2]),'
     'array2d(4..5,-1..1,[2,2,2,2,2,2]))',True),
    ('diffn_k(array2d(4..5,-1..1,[0,0,0,1,1,1]),'
     'array2d(4..5,-1..1,[2,2,2,2,2,2]))',False),
    ('diffn_nonstrict_k(array2d(4..5,-1..1,[0,0,0,1,1,1]),'
     'array2d(4..5,-1..1,[2,2,2,1,0,1]))',True),
])
def test_minizinc_boundary_cases_and_multiple_dimensions(call,expected):
    result = sp.translate(source='constraint '+call+';solve satisfy;',language='minizinc')
    solver = z3.Solver(); solver.add(formula(result))
    assert solver.check()==(z3.sat if expected else z3.unsat)


@pytest.mark.parametrize('call', [
    'diffn([0],[0,1],[1],[1])',
    'diffn(array1d(2..2,[0]),[0],[1],[1])',
    'diffn([true],[0],[1],[1])',
    'diffn_k([0],[1])',
    'diffn_k(array2d(1..1,1..2,[0,0]),array2d(1..1,2..3,[1,1]))',
])
def test_minizinc_bad_shapes_and_sorts_are_rejected(call):
    result = sp.translate(source='constraint '+call+';solve satisfy;',language='minizinc')
    assert not result.ok


@pytest.mark.parametrize('args', [[],[0],[2,0,1],[2,0,1,True,1],[True,0,1],[-1]])
def test_native_global_validates_metadata_and_element_types(args):
    def value(x):
        sort = native.HirSort.boolean() if type(x) is bool else native.HirSort.integer()
        return native._hir_literal(sort,str(x).lower())
    raw = native.HirModel()
    raw.constrain(native._hir_global('diffn',[value(x) for x in args]))
    assert not raw.translate().ok


@pytest.mark.parametrize('field,value', [('dimensions',True),('dimensions',0),
                                       ('positions',[[0,0]]),('nonstrict','false'),
                                       ('sizes',[[0]])])
def test_cp_schema_checks_dimensions_and_shape(field,value):
    expr = dict(cp='diffn',dimensions=2,positions=[],sizes=[],nonstrict=False)
    expr[field] = value
    with pytest.raises(ModelError):
        build_hir(model(expr),'x')


def test_native_cp_api_is_visible_to_natural_language_candidates():
    assert 'diffn' in hir_api()['cp_constructors']['constructors']
    expr = dict(cp='diffn',dimensions=3,positions=[[0,0,0],[0,0,3]],
                sizes=[[2,2,2],[2,2,2]],nonstrict=False)
    candidate = sp.propose_nl('x',language='hir',provider=lambda request:model(expr))
    assert candidate.valid, candidate.diagnostics
    result = sp.compile_candidate(candidate,accept_digest=candidate.digest)
    assert result.ok
    assert 'diffn-separating-axis' in result.translation.report.to_json()
