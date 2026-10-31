"""Public continuous construction, full translation and polynomial source oracle."""
from pathlib import Path
import importlib.util
import pytest
from somtparser import planning as n
import z3


def example():
    source=Path(__file__).resolve().parents[2]/'examples/planning_continuous_api.py'
    assert source.is_file(), f'continuous HIR example missing from source distribution: {source}'
    spec=importlib.util.spec_from_file_location('continuous_public_example',source)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    return module


@pytest.mark.parametrize('kind',['general','polynomial'])
def test_complete_public_construction_and_target_load(kind):
    model,encoding=example().build_model(kind)
    result=model.translate()
    assert result.ok,[d.message for d in result.diagnostic_items]
    target=z3.And(*z3.parse_smt2_string(result.to_smt2()))
    assert encoding.polynomial_witness==(kind=='polynomial')
    assert encoding.requires_trajectory_source_observations==(kind=='general')
    assert encoding.trajectory_names==['flow_x']
    if kind=='polynomial':
        # Complete relation on endpoint observations, not a sampled trace.
        x0,x1=z3.Reals('x0 x1');d0,d1=z3.Bools('d0 d1')
        oracle=z3.And(d0,d1,x0==0,x1==6)
        solver=z3.Solver();solver.add(z3.Tactic('qe')(z3.Xor(target,oracle)).as_expr())
        assert solver.check()==z3.unsat
    # General mode deliberately performs no arbitrary-ODE solver query.


def fixture(terminal_alias=False):
    model=n.HirModel();real=n.HirSort.real();boolean=n.HirSort.boolean()
    value=model.declare('x0',real);defined=model.declare('d0',boolean)
    next_value=value if terminal_alias else model.declare('x1',real)
    next_defined=model.declare('d1',boolean)
    initial=n.HirNumericStateCell(value,defined);terminal=n.HirNumericStateCell(next_value,next_defined)
    true=n.literal(boolean,'true');number=lambda v:n.literal(real,v)
    coordinate=n.HirContinuousCoordinate('curve','state',initial,terminal,true,n.planning_numeric_constant('0'))
    segment=n.HirContinuousSegment(true,number('0'),number('1'),'time',
        n.FlowDerivativeDomain.INTERIOR,[coordinate])
    return model,segment,number


def test_context_and_failed_composition_are_atomic():
    model,segment,number=fixture()
    original=model.translate().to_smt2()
    encoding=n.planning_continuous_segment(model,segment)
    assert model.translate().to_smt2()==original
    complete=encoding.to_model(model)
    assert model.translate().to_smt2()==original
    before=complete.translate().to_smt2()
    with pytest.raises(ValueError):encoding.to_model(complete)
    assert complete.translate().to_smt2()==before


@pytest.mark.parametrize('bad',['arity','Int','bound_time','state_alias'])
def test_bad_witness_shape_scope_and_alias_refused(bad):
    model,segment,number=fixture(terminal_alias=bad=='state_alias')
    coefficients=[[number('0')]]
    if bad=='arity':coefficients=[]
    if bad=='Int':coefficients=[[n.literal(n.HirSort.integer(),'0')]]
    if bad=='bound_time':coefficients=[[n.bound_variable('time',n.HirSort.real())]]
    original=model.translate().to_smt2()
    with pytest.raises(ValueError):n.planning_polynomial_flow_witness(model,segment,coefficients)
    assert model.translate().to_smt2()==original
