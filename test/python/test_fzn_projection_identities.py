import pytest
import z3

from tools.semantic_checks.source_oracles.fzn_json_source import Source, Unsupported, read_source


def flat(method='satisfy'):
    return read_source(dict(version='1.0', variables={'x':dict(type='int',domain=[[-3,7]]),'b':dict(type='bool')},
                            arrays={},constraints=[],output=[],solve=dict(method=method,**({}if method=='satisfy'else{'objective':'x'}))))


@pytest.mark.parametrize('recreate',[False,True])
def test_duplicate_public_coordinate_rejected(recreate):
    source=flat();p=z3.Int('public_x');second=z3.Int('public_x')if recreate else p
    with pytest.raises(Unsupported,match='duplicate'):
        source.projected([(p,source.variables['x']),(second,source.variables['x'])])


@pytest.mark.parametrize('recreate',[False,True])
def test_private_coordinate_overlap_rejected(recreate):
    source=flat();private=source.variables['x'];p=z3.Const(private.decl().name(),private.sort())if recreate else private
    with pytest.raises(Unsupported,match='overlap'):
        source.projected([(p,source.variables['x'])])


@pytest.mark.parametrize('cost_kind',['private','recreated-private','public','recreated-public'])
def test_cost_coordinate_remains_fresh(cost_kind):
    source=flat('minimize');p=z3.Int('public_x')
    cost={'private':source.variables['x'],'recreated-private':z3.Const(source.variables['x'].decl().name(),source.variables['x'].sort()),'public':p,'recreated-public':z3.Int('public_x')}[cost_kind]
    with pytest.raises(Unsupported,match='fresh'):
        source.projected([(p,source.variables['x'])],signed_cost=cost)


def test_identical_spelling_with_different_sorts_is_not_identity():
    source=flat();integer=z3.Int('same_public_name');boolean=z3.Bool('same_public_name')
    relation=source.projected([(integer,source.variables['x']),(boolean,source.variables['b'])])
    solver=z3.Solver();solver.add(z3.Xor(relation,z3.And(integer>=-3,integer<=7)))
    assert solver.check()==z3.unsat


@pytest.mark.parametrize('method',['minimize','maximize'])
def test_alias_observations_and_signed_cost_preserve_relation(method):
    source=flat(method);p,q,cost=z3.Ints('public_p public_q fresh_cost')
    relation=source.projected([(p,source.variables['x']),(q,source.variables['x'])],signed_cost=cost)
    expected=z3.And(p>=-3,p<=7,q==p,cost==(p if method=='minimize'else-p))
    solver=z3.Solver();solver.add(z3.Xor(relation,expected));assert solver.check()==z3.unsat
    solver=z3.Solver();solver.add(relation,p!=q);assert solver.check()==z3.unsat


def test_context_mismatch_does_not_merge_same_numeric_ast_ids():
    source=flat();context=z3.Context();public=z3.Int('x',ctx=context)
    with pytest.raises((Unsupported,z3.Z3Exception,ValueError)):
        source.projected([(public,source.variables['x'])])


def test_identity_check_scales_linearly_with_public_and_private_counts(monkeypatch):
    variables={f'v{i}':z3.Int(f'scale_private_{i}')for i in range(2048)}
    source=Source(variables,{},[],None,'satisfy',())
    observations=[(z3.Int(f'scale_public_{i}'),variables[f'v{i}'])for i in range(512)]
    calls=0;original=z3.AstRef.eq
    def counted(self,other):
        nonlocal calls
        calls+=1
        return original(self,other)
    monkeypatch.setattr(z3.AstRef,'eq',counted)
    relation=source.projected(observations)
    # The former nested identity scan made over a million API comparisons.
    assert calls<=16*(len(variables)+len(observations))
    assert z3.is_bool(relation)
