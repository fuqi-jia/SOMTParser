"""Server-only independent full-relation oracles for emitted Numeric API models."""
from pathlib import Path
import json,sys
import z3
ROOT=Path(sys.argv[1])
a,b=z3.Bools('a b');x,y,z,nx,ny,nz=z3.Reals('x y z nx ny nz');xd,yd,zd,nxd,nyd,nzd=z3.Bools('xd yd zd nxd nyd nzd')
old=[x,y,z];new=[nx,ny,nz];defined=[xd,yd,zd];new_defined=[nxd,nyd,nzd]
canon=z3.And(*[z3.Implies(z3.Not(d),v==0) for d,v in zip(defined,old)])
def frame(indices):return [f for i in indices for f in [new[i]==old[i],new_defined[i]==defined[i]]]
def outcome(index,value,isdefined):return [new_defined[index]==isdefined,new[index]==z3.If(isdefined,value,0)]
r=z3.RealVal
cases={
 'initialize':z3.And(canon,*frame([1,2]),*outcome(0,z3.If(a,r('1/3'),x),z3.Or(xd,a))),
 'swap':z3.And(canon,z3.Implies(a,z3.And(xd,yd)),*frame([2]),*outcome(0,z3.If(a,y,x),z3.Or(xd,a)),*outcome(1,z3.If(a,x,y),z3.Or(yd,a))),
 'additive':z3.And(canon,z3.Implies(z3.Or(a,b),xd),*frame([1,2]),*outcome(0,x-z3.If(a,r('3/2'),0)-z3.If(b,r('2/3'),0),xd)),
 'scaling':z3.And(canon,z3.Implies(a,z3.And(xd,yd)),z3.Implies(b,z3.And(xd,zd,z!=0)),*frame([1,2]),*outcome(0,x*z3.If(a,y,1)/z3.If(b,z,1),xd)),
 'scaling_conflict':z3.And(canon,z3.Not(z3.And(a,b)),z3.Implies(z3.Or(a,b),xd),*frame([1,2]),*outcome(0,x*z3.If(a,2,1)*z3.If(b,3,1),xd)),
 'duplicate_assignment':z3.And(canon,z3.Not(z3.And(a,b)),*frame([1,2]),*outcome(0,z3.If(z3.Or(a,b),2,x),z3.Or(xd,a,b))),
 'mixed_conflict':z3.And(canon,z3.Not(z3.And(a,b)),z3.Implies(b,xd),*frame([1,2]),*outcome(0,z3.If(a,2,x+z3.If(b,3,0)),z3.Or(xd,a))),
 'division':z3.And(canon,z3.Implies(a,z3.And(yd,y!=0)),*frame([1,2]),*outcome(0,z3.If(a,10/y,x),z3.Or(xd,a))),
 'undefined_logic':z3.And(canon,*frame(range(3)),a==z3.And(xd,x<=0),b==xd)
}
# Additional complete relations, independent of the helper representation:
# assign x := old(y)+1 under a; an uncalled future helper adds no restriction.
cases['helper_old_state']=z3.And(canon,z3.Implies(a,yd),*frame([1,2]),
 *outcome(0,z3.If(a,y+1,x),z3.Or(xd,a)))
# The formal is lexical; the actual old x is read. Enabled x:=x still needs
# x defined, whereas a disabled update preserves an undefined canonical cell.
cases['helper_lexical_argument']=z3.And(canon,z3.Implies(a,xd),*frame(range(3)))
helper_controls=json.loads((ROOT/'numeric-helper-dependency-controls.json').read_text())
expected_refusals={f'transitive_future_{position}_{activation}'
 for position in ('value','definedness','guard') for activation in ('enabled','disabled')}
expected_refusals.update({'old_metadata_value','old_metadata_definedness'})
assert helper_controls['passed'] is True
assert set(helper_controls['refusal_checks'])==expected_refusals
assert len(helper_controls['refusal_checks'])==len(expected_refusals)
assert helper_controls['emitted_models']==['helper_old_state','helper_lexical_argument']
rows=[]
for name,oracle in cases.items():
 target=z3.And(*z3.parse_smt2_file(str(ROOT/(name+'.smt2'))))
 solver=z3.Solver();solver.add(z3.Xor(target,oracle));result=solver.check()
 row=dict(case=name,full_relation=str(result),target_bytes=(ROOT/(name+'.smt2')).stat().st_size)
 if result!=z3.unsat:row['counterexample']=str(solver.model()) if result==z3.sat else solver.reason_unknown()
 rows.append(row);assert result==z3.unsat,row
 # A wrong next-state value must be observable even with feasible old values.
 mutant=z3.Solver();mutant.add(target,z3.Or(nx!=x,ny!=y))
 if name in ['initialize','swap','additive','scaling','division','helper_old_state']:assert mutant.check()==z3.sat,name
(ROOT/'numeric-full-relations.json').write_text(json.dumps(dict(passed=True,cases=rows,
 helper_dependency_controls=helper_controls,limits=None),indent=2)+'\n')
print(json.dumps(rows))
