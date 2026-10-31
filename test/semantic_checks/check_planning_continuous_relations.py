"""Source polynomial oracles and exact eps/delta specializations, server only.

No solver query purports to decide the unrestricted nonlinear ODE/UF problem.
Unknown is saved verbatim and fails that control; it is never changed to PASS.
"""
from pathlib import Path
import json
import sys
import z3

ROOT=Path(sys.argv[1])
x0,x1=z3.Reals('x0 x1')
d0,d1,enabled,active,guard=z3.Bools('d0 d1 enabled active guard')
rows=[]


def put():
    (ROOT/'continuous-full-relations.json').write_text(json.dumps(dict(
        passed=bool(rows) and all(row['passed'] for row in rows),cases=rows,
        unrestricted_ode_solver_claim=False,resource_limits=None),indent=2)+'\n')


def decide(formula,label,expected):
    # Exact quantifier elimination over these small polynomial witnesses;
    # there is no epsilon tolerance, bounded sample set or solver timeout.
    transformed=z3.Tactic('qe')(z3.simplify(formula)).as_expr()
    solver=z3.Solver();solver.add(transformed)
    result=solver.check()
    row=dict(case=label,result=str(result),expected=str(expected),passed=result==expected,
             quantifier_elimination='exact real arithmetic')
    if result==z3.unknown:row['reason_unknown']=solver.reason_unknown()
    if result==z3.sat and result!=expected:row['counterexample']=str(solver.model())
    rows.append(row);put();assert row['passed'],row


def target(name):
    return z3.And(*z3.parse_smt2_file(str(ROOT/(name+'.smt2'))))


def point(initial,terminal):
    return z3.And(d0,d1,x0==initial,x1==terminal)


oracles={
    'linear_guarded':z3.Implies(enabled,z3.And(d1==d0,
        z3.Implies(z3.Not(d0),x0==0),z3.Implies(z3.Not(d1),x1==0),
        z3.Implies(active,d0),x1==x0+z3.If(active,2,0))),
    # A linear candidate solves x'=x for all t only at the zero equilibrium.
    'nonlinear_witness':point(0,0),
    'parabola_safe':point(0,0),
    # 4t(1-t) reaches 1 at t=1/2 despite zero values at both endpoints.
    'parabola_interior_violation':z3.BoolVal(False),
    'open_invariant':point(0,1),
    'closed_invariant':z3.BoolVal(False),
    # For t>0, 2t^2/t=2t; at t=0 its source RHS is undefined. The API's
    # explicit endpoint policy must preserve this mathematical distinction.
    'interior_rhs_domain':point(0,1),
    'closed_rhs_domain':z3.BoolVal(False),
    'inactive_undefined_frame':z3.And(d1==d0,x0==0,x1==0),
    'guarded_undefined_invariant':z3.And(point(0,0),z3.Not(guard)),
    'lexical_shadow':point(0,0),
    'bound_vs_ident':point(0,0),
    'wrong_derivative':z3.BoolVal(False),
}
for name,oracle in oracles.items():
    decide(z3.Xor(target(name),oracle),name+'-complete-relation',z3.unsat)

# Negative controls detect the common endpoint-only invariant and sequential
# update mistakes using independent source trajectories, not target samples.
decide(z3.Xor(oracles['parabola_interior_violation'],point(0,0)),
       'endpoint-only-invariant-mutant',z3.sat)
decide(z3.Xor(oracles['nonlinear_witness'],point(1,2)),
       'initial-derivative-only-mutant',z3.sat)

# All generic nested-quantifier targets must load in full even when no solver
# decision procedure for their general function equations is claimed.
generic={name:target(name) for name in ('general_interior','general_closed','general_nonlinear')}
for name,formula in generic.items():
    rows.append(dict(case=name+'-whole-module-parse',passed=True,
        general_ode_sat_query_attempted=False,assertion_ast_bytes=len(formula.sexpr())))
put()

curve=z3.Function('curve_x',z3.RealSort(),z3.RealSort())


def specialize(formula,body,initial,terminal,enabled_value=True):
    result=z3.substitute_funs(formula,(curve,body))
    return z3.substitute(result,(x0,z3.RealVal(initial)),(x1,z3.RealVal(terminal)),
                         (d0,z3.BoolVal(True)),(d1,z3.BoolVal(True)),
                         (enabled,z3.BoolVal(enabled_value)),(active,z3.BoolVal(False)))


# Exact checks of the *general* epsilon-delta construction. A constant zero
# trajectory is continuous and has derivative zero; a spike at the left
# endpoint has the same interior derivative but is not closed-continuous.
for name in ('general_interior','general_closed'):
    decide(z3.Not(specialize(generic[name],z3.RealVal(0),0,0)),
           name+'-constant-full-epsilon-delta',z3.unsat)
spike=z3.If(z3.Var(0,z3.RealSort())==0,z3.RealVal(1),z3.RealVal(0))
decide(specialize(generic['general_interior'],spike,1,0),
       'endpoint-spike-refused-by-continuity',z3.unsat)
# Disabled trajectories are canonically zero, but external states may differ.
decide(z3.Not(specialize(generic['general_interior'],z3.RealVal(0),7,19,False)),
       'disabled-segment-external-state-unconstrained',z3.unsat)
print(json.dumps(dict(passed=True,controls=len(rows))))
