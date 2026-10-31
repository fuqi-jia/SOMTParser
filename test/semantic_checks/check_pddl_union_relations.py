"""Server-only public/internal PDDL finite-union full relation checks."""
from pathlib import Path
import hashlib
import json
import sys
import z3
from z3.z3util import get_vars

root=Path(sys.argv[1])
names=['quantified_true','quantified_false','empty_union','overlapping_union',
       'dynamic_choice','derived_union','numeric_union','forall_effect']
refusals=json.loads((root/'union-refusals.json').read_text())
expected={'unknown_union','empty_syntax','nested_type_union','wrong_union_argument',
          'unknown_quantified','union_object_declaration','union_type_parent','numeric_variadic_goal'}
assert refusals['passed'] and set(refusals['cases'])==expected and len(refusals['cases'])==len(expected)
rows=[]
for name in names:
    aliases=dict(line.split('\t') for line in (root/(name+'.tsv')).read_text().splitlines())
    used=set()
    def atom(label,sort='Bool'):
        used.add(label)
        return z3.Bool(aliases[label]) if sort=='Bool' else z3.Real(aliases[label])
    facts=[]
    if name=='numeric_union':
        for obj,value in zip('abp',(1,2,3)):
            label=f'({"cost"} {obj})'
            # A numeric-only name need not carry the disambiguating namespace;
            # source mapping explicitly exposes whichever representation is used.
            stem=f'state[0]::{label}'
            if stem not in aliases:
                label='numeric::'+label
                stem=f'state[0]::{label}'
                defined=f'state[0]::defined({label})'
            else:
                defined=f'state[0]::defined({label})'
            facts += [atom(stem,'Real')==value,atom(defined)]
    elif name=='derived_union':
        for p in ('base','marked'):
            for obj in 'abp':facts.append(atom(f'state[0]::({p} {obj})')==(obj in 'ap'))
    elif name!='empty_union':
        for obj in 'abp':
            truth=name in ('quantified_true','overlapping_union') or name=='quantified_false' and obj!='p'
            facts.append(atom(f'state[0]::(marked {obj})')==truth)
        if name in ('dynamic_choice','forall_effect'):
            for obj in 'abp':facts.append(atom(f'state[1]::(marked {obj})')==(obj=='p' or name=='forall_effect'))
            if name=='dynamic_choice':
                for obj in 'abp':facts.append(atom(f'choice[0]::(mark {obj})')==(obj=='p'))
            else:facts.append(atom('choice[0]::(markall)'))
    if name=='quantified_false':facts.append(z3.BoolVal(False))
    assert used==set(aliases),(name,sorted(set(aliases)-used))
    oracle=z3.And(*facts)
    observed=set(aliases.values())
    for suffix in ('.smt2','.internal.smt2'):
        path=root/(name+suffix)
        target=z3.And(*z3.parse_smt2_file(str(path)))
        hidden=[v for v in get_vars(target) if str(v) not in observed]
        if hidden:target=z3.Exists(hidden,target)
        solver=z3.Solver();solver.add(z3.Xor(target,oracle));result=solver.check()
        row={'case':name,'path':path.name,'full_relation_xor':str(result),
             'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
        if result!=z3.unsat:row['diagnostic']=str(solver.model()) if result==z3.sat else solver.reason_unknown()
        rows.append(row)
        if result!=z3.unsat:
            (root/'union-oracle-failure.json').write_text(json.dumps(row,indent=2)+'\n')
            raise AssertionError(row)
(root/'union-full-relations.json').write_text(json.dumps({'passed':True,'cases':rows,'refusals':refusals,'limits':None},indent=2)+'\n')
print(json.dumps(rows))
