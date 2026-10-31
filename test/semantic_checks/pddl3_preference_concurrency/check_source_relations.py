"""Exact full-state/cost controls for soft preference ownership and boundaries.

Fixed schedules are mathematical test inputs. Continuous cases substitute whole
linear functions into the original epsilon/delta and full-interval formulas.
No observation is sampled and no resource deadline is introduced.
"""
from pathlib import Path
from fractions import Fraction as Q
import hashlib,json,re,sys,time
import z3
from z3.z3util import get_vars
root=Path(sys.argv[1]);cases=json.loads(Path(__file__).with_name('cases.json').read_text())
def real(v):return z3.RealVal(str(v))
def curve(coefficients,u):return sum((real(c)*u**i for i,c in enumerate(coefficients)),real(0))
rows=[]
for case in cases:
    name=case['name'];ref=case['reference'];continuous=ref['kind']=='continuous';h=case['horizon'];count=2*h
    schedule=[(a,Q(s),Q(e)) for a,s,e in ref['schedule']];actions=sorted({a for a,s,e in schedule});times=sorted({t for a,s,e in schedule for t in (s,e)})
    initial={'(x)':Q(-1 if continuous else 0),'(d)':True,'(done-a)':False,'(done-b)':False}
    if not continuous:initial['(p)']=True
    pre=[initial];post=[]
    for i,t in enumerate(times):
        current=dict(pre[-1])
        for action,start,end in schedule:
            if action=='a':
                if start==t and ref.get('a_start')=='(not (p))':current['(p)']=False
                if start==t and ref.get('a_start')=='(assign (x) 2)':current['(x)']=Q(2)
                if end==t:current['(done-a)']=True
            elif start==t:
                current['(done-b)']=True
                if continuous:current['(x)']=Q(ref['reset'])
                elif ref['b_effect']=='(not (p))':current['(p)']=False
                else:current['(x)']=Q(2)
        current['(d)']=current['(x)']<0 if continuous else current['(p)'];post.append(current)
        following=dict(current)
        if continuous and i+1<len(times):
            coefficients=ref['curves'][i];u=times[i+1]-t;following['(x)']=sum(Q(c)*u**j for j,c in enumerate(coefficients));following['(d)']=following['(x)']<0
        pre.append(following)
    while len(post)<count:post.append(dict(pre[-1]));pre.append(dict(pre[-1]))
    target=root/(name+'.smt2');loaded=z3.Optimize();loaded.from_file(str(target));assert len(loaded.objectives())==1,name
    signed=z3.Real('__expected_soft_preference_cost');actual=z3.And(*loaded.assertions(),signed==loaded.objectives()[0])
    aliases=dict(line.split('\t') for line in (root/(name+'.tsv')).read_text().splitlines());expected_labels=set()
    for step,values in enumerate(pre):
        expected_labels.update(f'state[{step}]::{a}' for a in values)
        if continuous:expected_labels.add(f'state[{step}]::defined::(x)')
    if continuous:
        for step,values in enumerate(post):
            expected_labels.update(f'post[{step}]::{a}' for a in values);expected_labels.add(f'post[{step}]::defined::(x)')
        for step in range(count-1):expected_labels.update([f'flow[{step}]::(x)',f'flow[{step}]::(d)'])
    for slot in range(h):
        expected_labels.update([f'plan[{slot}]::start',f'plan[{slot}]::end']);expected_labels.update(f'choice[{slot}]::({a})' for a in actions)
    assert set(aliases)==expected_labels,(name,sorted(set(aliases)-expected_labels),sorted(expected_labels-set(aliases)))
    observed={str(signed)};expected=[];fixed=[];replacements=[];functions=[]
    for slot,(_,s,e) in enumerate(schedule):
        for endpoint,v in [('start',s),('end',e)]:
            base=f'__pddl_occurrence_{slot}_{endpoint}';replacements.extend([(z3.Int(base+'_numerator'),z3.IntVal(v.numerator)),(z3.Int(base+'_denominator'),z3.IntVal(v.denominator))])
    for step in range(count):replacements.extend([(z3.Bool(f'__pddl_happening_{step}_active'),z3.BoolVal(step<len(times))),(z3.Real(f'__pddl_happening_{step}_time'),real(times[step] if step<len(times) else 0))])
    for label,target_name in aliases.items():
        match=re.fullmatch(r'(state|post)\[(\d+)\]::(.*)',label)
        if match:
            mode,step,atom=match.groups();snapshot=(pre if mode=='state' else post)[int(step)]
            value=True if atom=='defined::(x)' else snapshot[atom]
            term=z3.Bool(target_name) if isinstance(value,bool) else z3.Real(target_name)
            expected.append(term==(z3.BoolVal(value) if isinstance(value,bool) else real(value)));observed.add(target_name)
        elif label.startswith('plan['):
            slot,endpoint=re.fullmatch(r'plan\[(\d+)\]::(start|end)',label).groups();v=schedule[int(slot)][1 if endpoint=='start' else 2];term=z3.Real(target_name)
            expected.append(term==real(v));fixed.append(term==real(v));replacements.append((term,real(v)));observed.add(target_name)
        elif label.startswith('choice['):
            slot,action=re.fullmatch(r'choice\[(\d+)\]::\(([^()]+)\)',label).groups();v=schedule[int(slot)][0]==action;term=z3.Bool(target_name)
            expected.append(term==v);fixed.append(term==v);replacements.append((term,z3.BoolVal(v)));observed.add(target_name)
        else:
            step,atom=re.fullmatch(r'flow\[(\d+)\]::(.*)',label).groups();step=int(step)
            if atom=='(d)':continue
            t=z3.Var(0,z3.RealSort())
            body=z3.If(z3.And(t>=real(times[step]),t<=real(times[step+1])),curve(ref['curves'][step],t-real(times[step])),real(0)) if step<len(times)-1 else real(0)
            functions.append((z3.Function(target_name,z3.RealSort(),z3.RealSort()),body))
    if functions:actual=z3.substitute_funs(actual,*functions)
    actual=z3.simplify(z3.And(z3.substitute(actual,*replacements),*fixed));auxiliary=[v for v in get_vars(actual) if str(v) not in observed]
    projected=z3.Exists(auxiliary,actual) if auxiliary else actual
    oracle=z3.And(*expected,signed==ref['cost']) if ref['valid'] else z3.BoolVal(False)
    independent_views=[]
    if continuous:
        raw=target.read_text();cut=raw.index('\n(check-sat)');point=z3.Real('__source_time')
        for step in range(count-1):
            wanted=z3.And(point>=real(times[step]),point<=real(times[step+1]),curve(ref['curves'][step],point-real(times[step]))<0) if step<len(times)-1 else z3.BoolVal(False)
            fun=aliases[f'flow[{step}]::(d)'];assertion=f'(assert (forall ((__source_time Real)) (= (|{fun}| __source_time) {wanted.sexpr()})))'
            parsed=z3.Optimize();parsed.from_string(raw[:cut]+'\n'+assertion+raw[cut:]);view=parsed.assertions()[-1];view=z3.substitute_funs(view,*functions)
            definitions=[(z3.Bool(aliases[f'post[{i}]::defined::(x)']),z3.BoolVal(True)) for i in range(count)]
            independent_views.append(z3.Not(z3.substitute(view,*(replacements+definitions))))
    query=z3.simplify(z3.Or(z3.Xor(projected,oracle),*independent_views))
    (root/'pddl3-preference-concurrency-current.json').write_text(json.dumps(dict(case=name,phase='full-relation',started_unix=time.time(),limits=None))+'\n')
    if continuous:query=z3.Tactic('qe')(query).as_expr()
    solver=z3.Solver();solver.add(query);answer=solver.check()
    row=dict(case=name,whole_module_loaded=True,source_schedule_valid=ref['valid'],expected_cost=ref['cost'],full_relation_xor=str(answer),source_observables=len(aliases),entire_flow_witnesses=len(functions),pointwise_derived_views=len(independent_views),target_sha256=hashlib.sha256(target.read_bytes()).hexdigest())
    if answer!=z3.unsat:row['detail']=str(solver.model()) if answer==z3.sat else solver.reason_unknown()
    rows.append(row);(root/'pddl3-preference-concurrency-source-oracles.partial.json').write_text(json.dumps(rows,indent=2)+'\n');assert answer==z3.unsat,row
(root/'pddl3-preference-concurrency-source-oracles.json').write_text(json.dumps(dict(passed=True,cases=rows,full_relation_cases=len(rows),limits=None,sampling=False,scope='fixed rational schedules with all state/choice/time/signed-cost coordinates; three entire continuous curves, not arbitrary-ODE completeness'),indent=2)+'\n')
print(json.dumps(dict(passed=True,full_relation_cases=len(rows))))
