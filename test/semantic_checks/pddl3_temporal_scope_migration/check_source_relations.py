"""Original byte-identical formerly unsupported source, now exact accepted cases."""
from pathlib import Path
import hashlib,json,sys
import z3
from z3.z3util import get_vars
r=Path(sys.argv[1]);case=json.loads(Path(__file__).with_name('case.json').read_text())['original_case']
for side in ['domain','problem']:assert hashlib.sha256((r/('original.'+side+'.pddl')).read_bytes()).hexdigest()==case[side+'_sha256']
opt=z3.Optimize();opt.from_file(str(r/'original.smt2'));assert len(opt.objectives())==0
aliases=dict(line.split('\t') for line in (r/'original.tsv').read_text().splitlines())
assert set(aliases)=={'state[0]::(p)','state[1]::(p)','state[2]::(p)','plan[0]::start','plan[0]::end','choice[0]::(a)'}
rows=[]
for name,active,start,end,valid in [('empty',False,0,0,True),('one-execution',True,1,2,True),('wrong-duration',True,1,3,False),('zero-start',True,0,1,False)]:
    replacements=[];fixed=[];expected=[]
    for endpoint,value in [('start',start),('end',end)]:
        term=z3.Real(aliases[f'plan[0]::{endpoint}']);fixed.append(term==value);expected.append(term==value)
        replacements.extend([(term,z3.RealVal(value)),(z3.Int(f'__pddl_occurrence_0_{endpoint}_numerator'),z3.IntVal(value)),(z3.Int(f'__pddl_occurrence_0_{endpoint}_denominator'),z3.IntVal(1))])
    selected=z3.Bool(aliases['choice[0]::(a)']);fixed.append(selected==active);expected.append(selected==active);replacements.append((selected,z3.BoolVal(active)))
    for i in range(2):
        replacements.extend([(z3.Bool(f'__pddl_happening_{i}_active'),z3.BoolVal(active)),(z3.Real(f'__pddl_happening_{i}_time'),z3.RealVal((start,end)[i] if active else 0))])
    for step in range(3):expected.append(z3.Bool(aliases[f'state[{step}]::(p)'])==(active and step==2))
    actual=z3.simplify(z3.And(z3.substitute(z3.And(*opt.assertions()),*replacements),*fixed))
    aux=[v for v in get_vars(actual) if str(v) not in set(aliases.values())];projected=z3.Exists(aux,actual) if aux else actual
    oracle=z3.And(*expected) if valid else z3.BoolVal(False)
    solver=z3.Solver();solver.add(z3.Xor(projected,oracle));answer=solver.check()
    row=dict(case=name,source_schedule_valid=valid,full_relation_xor=str(answer));rows.append(row);assert answer==z3.unsat,(row,str(solver.model()) if answer==z3.sat else solver.reason_unknown())
(r/'pddl3-temporal-scope-migration-oracles.json').write_text(json.dumps(dict(passed=True,original_case=case,cases=rows,full_relation_cases=len(rows),whole_module_loaded=True,objectives=0,limits=None),indent=2)+'\n')
print(json.dumps(dict(passed=True,full_relation_cases=len(rows))))
