"""Construct and export exact continuous HIR; this example does not parse PDDL.

Run with a build that registers the public planning API:
    python examples/planning_continuous_api.py --kind general --output flow.smt2
    python examples/planning_continuous_api.py --kind polynomial --output known.smt2

General mode emits continuity, differential and invariant quantifiers over an
unknown real trajectory. Polynomial mode checks the supplied trajectory 2*t.
Neither command invokes a solver or promises that general ODEs are decidable.
"""
from pathlib import Path
import argparse
import hashlib
import json
from somtparser import planning as n


def build_model(kind):
    if kind not in ('general','polynomial'):
        raise ValueError('kind must be general or polynomial')
    model=n.HirModel()
    real,boolean=n.HirSort.real(),n.HirSort.boolean()
    x0=model.declare('x0',real);x1=model.declare('x1',real)
    d0=model.declare('d0',boolean);d1=model.declare('d1',boolean)
    true=n.literal(boolean,'true')
    number=lambda value:n.literal(real,value)
    initial=n.HirNumericStateCell(x0,d0)
    terminal=n.HirNumericStateCell(x1,d1)
    state_at_time=n.bound_variable('x',real)
    state_value=n.HirNumericValue(state_at_time,d0,[0])
    lower=n.planning_numeric_compare('>=',state_value,n.planning_numeric_constant('0'))
    upper=n.planning_numeric_compare('<=',state_value,n.planning_numeric_constant('6'))
    invariant=n.planning_numeric_logical('and',[lower,upper])
    coordinate=n.HirContinuousCoordinate('flow_x','x',initial,terminal,true,n.planning_numeric_constant('2'))
    segment=n.HirContinuousSegment(true,number('0'),number('3'),'time',
        n.FlowDerivativeDomain.CLOSED_ONE_SIDED,[coordinate],
        [n.HirContinuousInvariant(true,invariant,True,True)])
    model.constrain(d0)
    model.constrain(n.operation('eq',[x0,number('0')]))
    if kind=='general':
        encoding=n.planning_continuous_segment(model,segment)
    else:
        # Known polynomial in elapsed time: x(t)=0+2*(t-start).
        encoding=n.planning_polynomial_flow_witness(model,segment,[[number('0'),number('2')]])
    complete=encoding.to_model(model)
    return complete,encoding


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--kind',choices=('general','polynomial'),required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    model,encoding=build_model(args.kind)
    result=model.translate()
    if not result.ok:
        raise RuntimeError([diagnostic.message for diagnostic in result.diagnostics])
    raw=result.to_smt2().encode()
    args.output.write_bytes(raw)
    print(json.dumps(dict(kind=args.kind,polynomial_witness=encoding.polynomial_witness,
        trajectory_names=encoding.trajectory_names,bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest(),
        solver_invoked=False,pddl_frontend_support_claim=False)))


if __name__=='__main__':
    main()
