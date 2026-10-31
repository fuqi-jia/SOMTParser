"""Independent full x/signed-cost relation for twenty accepted source controls."""
from pathlib import Path
import json
import sys
import z3
from z3.z3util import get_vars

CASES={
    'long-default':('Real',0,1,1),
    'long-inline-bounds':('Real',-1,1,1),
    'long-objective':('Real',0,2,4000),
    'named-reset':('Real',1,2,1),
    'unnamed-reset':('Real',1,2,1),
    'inline-subject':('Real',0,2,1),
    'inline-reset':('Real',1,2,1),
    'keyword-labels':('Real',1,2,1),
    'exact-duplicates':('Real',0,1,1),
    'integer-max':('Int',0,2,2),
    'range-reset':('Real',-1,2,1),
    'comments-crlf':('Real',0,2,1),
    'inline-negative-lower':('Real',-2,2,1),
    'inline-positive-lower':('Real',1,2,1),
    'header-negative-lower':('Real',-2,2,1),
    'header-positive-lower':('Real',1,2,1),
    'inline-negative-exponent':('Real',-5,2,1),
    'header-negative-exponent':('Real',-5,2,1),
    'inline-negative-infinity':('Real',None,2,1),
    'header-negative-infinity':('Real',None,2,1),
}


def main():
    root=Path(sys.argv[1]);results=[]
    for name,(sort,lo,hi,factor) in CASES.items():
        opt=z3.Optimize();opt.from_file(str(root/(name+'.smt2')))
        assert len(opt.objectives())==1
        x=z3.Int('x') if sort=='Int' else z3.Real('x')
        cost=z3.Real('__independent_lp_signed_cost')
        whole=z3.And(*opt.assertions(),cost==opt.objectives()[0])
        hidden=[v for v in get_vars(whole) if not v.eq(x) and not v.eq(cost)]
        actual=z3.Exists(hidden,whole) if hidden else whole
        expected=z3.And(*([x>=lo] if lo is not None else []),x<=hi,cost==factor*x)
        solver=z3.Solver();solver.set(timeout=0);solver.add(z3.Xor(actual,expected))
        answer=solver.check()
        row=dict(case=name,full_relation_xor=str(answer),hidden_symbols=[str(v) for v in hidden])
        results.append(row)
        (root/'full-relations.partial.json').write_text(json.dumps(results,indent=2)+'\n')
        assert answer==z3.unsat,(row,solver.model() if answer==z3.sat else solver.reason_unknown())
        witness=z3.Solver();witness.add(expected);assert witness.check()==z3.sat
    # Check that the oracle can see a changed bound, coefficient, maximization
    # sign, and integer carrier; these are deliberately false target relations.
    controls=[]
    x=z3.Real('x');cost=z3.Real('__independent_lp_signed_cost')
    expected=z3.And(x>=0,x<=1,cost==x)
    mutants={'bound':z3.And(x>=0,x<=2,cost==x),
             'coefficient':z3.And(x>=0,x<=1,cost==2*x),
             'objective-sign':z3.And(x>=0,x<=1,cost==-x),
             'unjustified-integer':z3.And(expected,z3.IsInt(x))}
    for name,mutant in mutants.items():
        s=z3.Solver();s.add(z3.Xor(expected,mutant));answer=s.check();assert answer==z3.sat,name
        controls.append(dict(kind=name,symmetric_difference=str(answer),witness=str(s.model())))
    result=dict(complete=True,passed=True,source_controls=27,accepted_full_relations=20,
                explicit_rejections=7,negative_controls=controls,relations=results,
                numerical_arithmetic='exact rationals',solver_timeout_ms=0)
    (root/'full-relations.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))


if __name__=='__main__':main()
