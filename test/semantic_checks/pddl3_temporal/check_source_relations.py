"""Exact fixed-schedule source relations and entire continuous witnesses.

There is no endpoint approximation: x(u)=4u(1-u), y(u)=u are entire
mathematical test functions substituted into the original quantified ODE and
trajectory formulas. Full time/schedule/ODE decision completeness is not claimed.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib,json,re,sys,time
import z3
from z3.z3util import get_vars
root=Path(sys.argv[1]);cases=json.loads(Path(__file__).with_name('cases.json').read_text())
def exact(x): return z3.RealVal(str(x))
def scalar(v): return z3.BoolVal(v) if isinstance(v,bool) else exact(v)
def modal(name,states,times):
    p=[s['(p)'] for s in states];q=[s['(q)'] for s in states]
    if name=='at_end': return p[-1]
    if name=='always': return all(p)
    if name=='sometime': return any(q)
    if name=='within': return any(v and t<=2 for v,t in zip(q,times))
    if name=='at_most_once': return sum(v and (i==0 or not p[i-1]) for i,v in enumerate(p))<=1
    if name=='before': return all(not v or any(q[:i]) for i,v in enumerate(p))
    if name=='after': return all(not v or any(q[i:]) for i,v in enumerate(p))
    if name=='always_within': return all(not v or any(q[j] and times[j]-times[i]<=1 for j in range(i,len(q))) for i,v in enumerate(p))
    if name=='hold_after': return any(v and t>2 for v,t in zip(p,times)) if times[-1]>2 else p[-1]
    if name=='hold_during':
        if times[-1]<=1: return p[-1]
        before=max(i for i,t in enumerate(times) if t<=1)
        return p[before] and all(v for v,t in zip(p,times) if 1<=t<3)
    raise AssertionError(name)

rows=[]
for case in cases:
    name=case['name']
    if not case['accepted']:
        assert (root/(name+'.diagnostics.txt')).read_text().strip(),name
        assert not (root/(name+'.smt2')).exists(),name
        continue
    spec=case['reference'];continuous=spec['kind']=='continuous';h=case['horizon'];count=2*h
    schedule=[(a,Q(s),Q(e)) for a,s,e in spec['schedule']]
    times=sorted({t for _,s,e in schedule for t in [s,e]})
    if continuous:
        # Direct source ODE solution: y'=1, x'=4-8y, initial x=y=0.
        # At u=1/2, x=1, so d=(x<1) is false only at that interior point.
        pre=[{'(x)':Q(0),'(y)':Q(0),'(q)':False,'(d)':True}]
    else:
        pre=[{'(p)':False,'(q)':False}]
        if spec.get('numeric'): pre[0]['(x)']=None
    post=[]
    for i,t in enumerate(times):
        now=dict(pre[-1])
        if continuous:
            if t==2: now['(q)']=True
        elif spec.get('instant'): now['(q)']=True
        else:
            if any(s==t for _,s,e in schedule): now['(p)']=True
            if any(e==t for _,s,e in schedule): now['(p)']=False;now['(q)']=True
        post.append(now)
        after=dict(now)
        if continuous and i+1<len(times):
            u=times[i+1]-t;after['(x)']=4*u*(1-u);after['(y)']=u;after['(d)']=after['(x)']<1
        pre.append(after)
    while len(post)<count: post.append(dict(pre[-1]));pre.append(dict(pre[-1]))
    valid=spec.get('valid',True);score=spec.get('score')
    if 'operator' in spec:
        holds=modal(spec['operator'],[pre[0]]+post[:len(times)],[Q(0)]+times)
        if spec['soft']: score=int(not holds)
        else: valid=holds
    path=root/(name+'.smt2');loaded=z3.Optimize();loaded.from_file(str(path));objectives=list(loaded.objectives())
    assert len(objectives)==(score is not None),(name,score,objectives)
    signed=z3.Real('__source_signed_preference_cost');actual=z3.And(*loaded.assertions())
    if score is not None: actual=z3.And(actual,signed==objectives[0])
    aliases=dict(line.split('\t') for line in (root/(name+'.tsv')).read_text().splitlines())
    observed={str(signed)} if score is not None else set();expected=[];fixed=[];replacements=[];flow_replacements=[]
    for slot,(_,start,end) in enumerate(schedule):
        for endpoint,v in [('start',start),('end',end)]:
            base=f'__pddl_occurrence_{slot}_{endpoint}'
            replacements.extend([(z3.Int(base+'_numerator'),z3.IntVal(v.numerator)),(z3.Int(base+'_denominator'),z3.IntVal(v.denominator))])
    for step in range(count):
        active=step<len(times)
        replacements.extend([(z3.Bool(f'__pddl_happening_{step}_active'),z3.BoolVal(active)),(z3.Real(f'__pddl_happening_{step}_time'),exact(times[step] if active else 0))])
    expected_labels=set()
    for step,state in enumerate(pre):
        for atom in state: expected_labels.add(f'state[{step}]::{atom}')
        if continuous:
            for atom in ['(x)','(y)']: expected_labels.add(f'state[{step}]::defined::{atom}')
    if continuous:
        for step,state in enumerate(post):
            for atom in state: expected_labels.add(f'post[{step}]::{atom}')
            for atom in ['(x)','(y)']: expected_labels.add(f'post[{step}]::defined::{atom}')
        for step in range(count-1):
            for atom in ['(x)','(y)','(d)']: expected_labels.add(f'flow[{step}]::{atom}')
    for slot in range(h):
        expected_labels.update([f'plan[{slot}]::start',f'plan[{slot}]::end',f'choice[{slot}]::(a)'])
    assert set(aliases)==expected_labels,(name,sorted(set(aliases)-expected_labels),sorted(expected_labels-set(aliases)))
    for label,target in aliases.items():
        m=re.fullmatch(r'(state|post)\[(\d+)\]::(.*)',label)
        if m:
            mode,index,atom=m.groups();state=(pre if mode=='state' else post)[int(index)]
            if atom.startswith('defined::'): value=state[atom[9:]] is not None;term=z3.Bool(target)
            else:
                value=state[atom];term=z3.Bool(target) if isinstance(value,bool) else z3.Real(target)
                if value is None: value=0
            expected.append(term==scalar(value));observed.add(target)
        elif label.startswith('plan['):
            slot,endpoint=re.fullmatch(r'plan\[(\d+)\]::(start|end)',label).groups();v=schedule[int(slot)][1 if endpoint=='start' else 2];term=z3.Real(target)
            expected.append(term==exact(v));fixed.append(term==exact(v));replacements.append((term,exact(v)));observed.add(target)
        elif label.startswith('choice['):
            term=z3.Bool(target);expected.append(term);fixed.append(term);replacements.append((term,z3.BoolVal(True)));observed.add(target)
        else:
            step,atom=re.fullmatch(r'flow\[(\d+)\]::(.*)',label).groups();step=int(step)
            if atom=='(d)': continue
            t=z3.Var(0,z3.RealSort());u=t-exact(1)
            body=z3.If(z3.And(t>=1,t<=2),4*u*(1-u) if atom=='(x)' else u,exact(0)) if step==0 else exact(0)
            flow_replacements.append((z3.Function(target,z3.RealSort(),z3.RealSort()),body))
    if flow_replacements: actual=z3.substitute_funs(actual,*flow_replacements)
    actual=z3.simplify(z3.And(z3.substitute(actual,*replacements),*fixed))
    auxiliaries=[v for v in get_vars(actual) if str(v) not in observed]
    projected=z3.Exists(auxiliaries,actual) if auxiliaries else actual
    if score is not None: expected.append(signed==exact(score))
    oracle=z3.And(*expected) if valid else z3.BoolVal(False)
    extra=[]
    if continuous:
        raw=path.read_text();cut=raw.index('\n(check-sat)');point=z3.Real('__independent_flow_point')
        for step in range(count-1):
            u=point-1;wanted=z3.And(point>=1,point<=2,4*u*(1-u)<1) if step==0 else z3.BoolVal(False)
            declaration=aliases[f'flow[{step}]::(d)']
            assertion=f'(assert (forall ((__independent_flow_point Real)) (= (|{declaration}| __independent_flow_point) {wanted.sexpr()})))'
            checked=z3.Optimize();checked.from_string(raw[:cut]+'\n'+assertion+raw[cut:])
            equation=checked.assertions()[-1];equation=z3.substitute_funs(equation,*flow_replacements)
            defs=[(z3.Bool(aliases[f'post[{i}]::defined::{atom}']),z3.BoolVal(True)) for i in range(count) for atom in ['(x)','(y)']]
            extra.append(z3.Not(z3.substitute(equation,*(replacements+defs))))
    query=z3.simplify(z3.Or(z3.Xor(projected,oracle),*extra))
    (root/'pddl3-temporal-current.json').write_text(json.dumps(dict(case=name,phase='exact-full-relation',started_unix=time.time(),limits=None))+'\n')
    if continuous: query=z3.Tactic('qe')(query).as_expr()
    solver=z3.Solver();solver.add(query);answer=solver.check()
    row=dict(case=name,whole_module_loaded=True,full_schedule_relation_and_cost=str(answer),source_valid=valid,signed_cost=None if score is None else str(score),source_observables=len(aliases),complete_flow_witnesses=len(flow_replacements),derived_function_relations=len(extra),target_sha256=hashlib.sha256(path.read_bytes()).hexdigest())
    if answer!=z3.unsat: row['detail']=str(solver.model()) if answer==z3.sat else solver.reason_unknown()
    rows.append(row);(root/'pddl3-temporal-source-oracles.partial.json').write_text(json.dumps(rows,indent=2)+'\n')
    assert answer==z3.unsat,row
(root/'pddl3-temporal-source-oracles.json').write_text(json.dumps(dict(passed=True,cases=rows,full_relation_cases=len(rows),source_refusals=sum(not c['accepted'] for c in cases),limits=None,sampling=False,scope='complete source states/cost for each fixed schedule and explicit entire polynomial witness; not arbitrary-ODE decision completeness'),indent=2)+'\n')
print(json.dumps(dict(passed=True,full_relation_cases=len(rows))))
