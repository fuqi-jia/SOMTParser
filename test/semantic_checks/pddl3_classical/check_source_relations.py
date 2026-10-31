"""Independent complete small classical trace + signed objective relation.

Enumeration follows source action semantics, not emitted formula structure.
Every prefix plan up to the horizon and every state/cost value is compared by
XOR after existential projection of administrative encoding auxiliaries.
"""
from pathlib import Path
from itertools import product
from fractions import Fraction
import hashlib
import json
import sys
import z3
from z3.z3util import get_vars

ROOT=Path(sys.argv[1])
CASES=json.loads(Path(__file__).with_name('cases.json').read_text())


def modal(name, states):
    p=[s[0] for s in states];q=[s[1] for s in states];end=len(states)-1
    if name=='at_end': return p[-1]
    if name=='always': return all(p)
    if name=='sometime': return any(q)
    if name=='within': return any(q[i] for i in range(min(end,1)+1))
    if name=='within_padding': return q[0]
    if name=='at_most_once': return sum(v and (i==0 or not p[i-1]) for i,v in enumerate(p))<=1
    if name=='before': return all(not p[i] or any(q[:i]) for i in range(end+1))
    if name=='after': return all(not p[i] or any(q[i:]) for i in range(end+1))
    if name=='before_same': return all(not p[i] or any(p[:i]) for i in range(end+1))
    if name=='after_same': return all(not p[i] or any(p[i:]) for i in range(end+1))
    if name=='always_within': return all(not p[i] or any(q[i:min(end+1,i+2)]) for i in range(end+1))
    if name=='hold_after': return any(p[1:]) if end>0.5 else p[-1]
    if name=='hold_during':
        if end<=0.5: return p[-1]
        # Figure 1 includes the state spanning the lower boundary, here S0.
        return p[0] and all(p[i] for i in range(1,min(end,2)+1))
    if name in ('hold_after_final','hold_during_final'): return p[-1]
    if name=='domain_and_problem': return all(p) and any(q)
    raise AssertionError(name)


rows=[]
for case in CASES:
    name=case['name']
    if not case['accepted']:
        assert (ROOT/(name+'.diagnostics.txt')).read_text().strip(),name
        assert not (ROOT/(name+'.smt2')).exists(),name
        continue
    target=ROOT/(name+'.smt2')
    opt=z3.Optimize();opt.from_file(str(target))
    formula=z3.And(*opt.assertions());objectives=list(opt.objectives())
    # parse_smt2_file by itself discards optimization commands. Keep the full
    # Optimize load and include its min-oriented signed objective in relation.
    cost=z3.Real('__oracle_signed_cost')
    if objectives:
        assert len(objectives)==1,(name,objectives)
        formula=z3.And(formula,cost==objectives[0])
    aliases=dict(line.split('\t') for line in (ROOT/(name+'.tsv')).read_text().splitlines())
    observed=set(aliases.values());used=set();branches=[]
    if objectives: observed.add(str(cost))
    spec=case['oracle'];kind=spec['kind'];h=case['horizon']
    if kind=='trace': actions=['setp','clearp','setq','clearq'];initial=tuple(spec['initial'])
    elif kind=='quant': actions=['mark a','mark b','clear a','clear b'];initial=(False,False)
    elif kind=='action': actions=['use','set','clear'];initial=(False,)
    else: actions=['fill'];initial=(False,0)

    def bool_alias(label,value):
        used.add(label);return z3.Bool(aliases[label])==value

    def state(step,values):
        if kind=='trace': return [bool_alias(f'state[{step}]::({p})',v) for p,v in zip(['p','q'],values)]
        if kind=='quant': return [bool_alias(f'state[{step}]::(marked {a})',v) for a,v in zip('ab',values)]
        if kind=='action': return [bool_alias(f'state[{step}]::(p)',values[0])]
        label=f'state[{step}]::(x)';used.add(label)
        return [bool_alias(f'state[{step}]::defined((x))',values[0]),z3.Real(aliases[label])==values[1]]

    for length in range(h+1):
        for plan in product(actions,repeat=length):
            states=[initial];violations=0
            for action in plan:
                values=list(states[-1])
                if kind=='trace': values[0 if action.endswith('p') else 1]=action.startswith('set')
                elif kind=='quant': values[0 if action.endswith('a') else 1]=action.startswith('mark')
                elif kind=='action':
                    if action=='use': violations+=not values[0]
                    else: values[0]=action=='set'
                else: values=[True,2]
                states.append(tuple(values))
            valid=True;signed=None
            if kind=='trace':
                satisfied=modal(spec['operator'],states)
                if spec['soft']: signed=int(not satisfied)
                else: valid=satisfied
            elif kind=='quant':
                a,b=states[-1];mode=spec['mode']
                if mode=='each': signed=int(not a)+int(not b)
                elif mode=='whole': signed=int(not (a and b))
                elif mode=='shadow': signed=2*(int(not a)+int(not b))
                elif mode=='anonymous': signed=int(not a)
                elif mode=='maximum': signed=-(10-3*int(not b)-int(not a))
                elif mode=='nary': signed=7+6*int(not a)+int(not b)
                elif mode=='rational': signed=Fraction(3,2)*int(not a)+Fraction(1,4)*int(not b)
                elif mode=='empty': signed=0
                elif mode!='named_no_metric': raise AssertionError(mode)
            elif kind=='action': signed=violations
            else:
                defined,x=states[-1]
                satisfied=defined and ((x>0) if spec['mode']=='positive' else (x<=0) if spec['mode']=='negative' else True)
                signed=int(not satisfied)
            if not valid: continue
            assert bool(objectives)==(signed is not None),(name,len(objectives),signed)
            terms=[]
            for step in range(h):
                selected=plan[step] if step<length else None
                for action in actions: terms.append(bool_alias(f'choice[{step}]::({action})',selected==action))
                noop=z3.Bool('__pddl_noop@'+str(step));observed.add(str(noop));terms.append(noop==(selected is None))
            padded=states+[states[-1]]*(h-length)
            for step,values in enumerate(padded): terms.extend(state(step,values))
            if signed is not None: terms.append(cost==z3.RealVal(str(signed)))
            branches.append(z3.And(*terms))
    expected=z3.Or(*branches)
    # Even an inconsistent hard modality still observes the same source state
    # coordinate set; mark these from the source schema, not from target terms.
    if not branches:
        for step in range(h+1): state(step,initial)
        for step in range(h):
            for action in actions: bool_alias(f'choice[{step}]::({action})',False)
            observed.add('__pddl_noop@'+str(step))
    assert used==set(aliases),(name,sorted(set(aliases)-used),sorted(used-set(aliases)))
    auxiliaries=[v for v in get_vars(formula) if str(v) not in observed]
    actual=z3.Exists(auxiliaries,formula) if auxiliaries else formula
    solver=z3.Solver();solver.add(z3.Xor(actual,expected));answer=solver.check()
    row=dict(case=name,whole_module_loaded=True,objectives=len(objectives),full_relation_and_cost=str(answer),
        feasible_prefix_branches=len(branches),source_observables=len(aliases),auxiliaries=len(auxiliaries),
        source_sha256={key:case[key+'_sha256'] for key in ('domain','problem')},target_sha256=hashlib.sha256(target.read_bytes()).hexdigest())
    if answer!=z3.unsat: row['detail']=str(solver.model()) if answer==z3.sat else solver.reason_unknown()
    rows.append(row)
    (ROOT/'pddl3-classical-source-oracles.partial.json').write_text(json.dumps(rows,indent=2)+'\n')
    assert answer==z3.unsat,row
result=dict(passed=True,full_relation_cases=len(rows),source_refusals=sum(not c['accepted'] for c in CASES),cases=rows,
    limits=None,scope='complete finite source relations and signed objectives; not an official competition success rate')
(ROOT/'pddl3-classical-source-oracles.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
