"""Independent complete-relation and exact-cost checks of public HIR examples."""
from copy import deepcopy
from itertools import permutations, product
from pathlib import Path
import json
import os
import z3
import somtparser as sp
from somtparser.hir import hir_api

EVIDENCE=Path(os.environ['PATTERN_EVIDENCE']) if 'PATTERN_EVIDENCE' in os.environ else None
if EVIDENCE is not None:
    EVIDENCE.mkdir(exist_ok=True)


def report(name,data):
    if EVIDENCE is not None:
        (EVIDENCE/(name+'.json')).write_text(json.dumps(data,indent=2)+'\n')


def check(*formulas):
    solver=z3.Solver()
    solver.add(*formulas)
    result=solver.check()
    return result, str(solver.model()) if result==z3.sat else None


def compiled(name):
    pattern=hir_api()['modeling_patterns'][name]
    candidate=sp.propose_nl(pattern['source'],language='hir',provider=lambda request:deepcopy(pattern['model']))
    assert candidate.valid,candidate.diagnostics
    translation=sp.compile_candidate(candidate,accept_digest=candidate.digest)
    assert translation.ok,translation.diagnostics
    text=translation.to_smt2()
    if EVIDENCE is not None:
        (EVIDENCE/(name+'.smt2')).write_text(text)
    target=z3.Optimize();target.from_string(text)
    return pattern,z3.And(*target.assertions()),list(target.objectives())


def elements(name):
    array=z3.Array(name,z3.IntSort(),z3.IntSort())
    return [z3.Select(array,i) for i in range(3)]


def fixed(values,assignment):return [value==literal for value,literal in zip(values,assignment)]


def test_shared_identity_complete_relation_and_all_identifier_permutations():
    _,actual,costs=compiled('shared_identity_coordinates');assert costs==[]
    riders,bikes=elements('riders'),elements('bikes')
    expected=z3.And(*[z3.And(value>=1,value<=3) for value in riders+bikes],
                    z3.Distinct(*riders),z3.Distinct(*bikes),riders[0]==bikes[2])
    answer,_=check(z3.Xor(actual,expected));assert answer==z3.unsat
    rows=[];allowed=[]
    for r,b in product(permutations((1,2,3)),repeat=2):
        answer,_=check(actual,*fixed(riders,r),*fixed(bikes,b))
        truth=r[0]==b[2]
        assert answer==(z3.sat if truth else z3.unsat)
        rows.append(dict(riders=r,bikes=b,source_relation=truth,compiled_status=str(answer)))
        if truth:allowed.append((r,b))
    assert len(rows)==36 and len(allowed)==12
    # Every bijection of shared labels preserves every accepted relation.
    for r,b in allowed:
        for perm in permutations((1,2,3)):
            relabel=dict(zip((1,2,3),perm))
            transformed=(tuple(relabel[x] for x in r),tuple(relabel[x] for x in b))
            assert transformed in allowed
    report('shared-identity-relation',dict(full_relation_xor='unsat',pairs=rows,
        feasible_permutation_pairs=12,all_six_shared_label_bijections_preserved=True,
        solver_limits=None))


def test_row_aligned_inverse_representation_changes_the_observed_relation():
    _,actual,_=compiled('shared_identity_coordinates')
    riders,bikes=elements('riders'),elements('bikes')
    row_aligned=z3.And(*[z3.And(value>=1,value<=3) for value in riders+bikes],
        z3.Distinct(*riders),z3.Distinct(*bikes),
        z3.Or(*[z3.And(riders[i]==1,bikes[i]==3) for i in range(3)]))
    result,witness=check(z3.Xor(actual,row_aligned));assert result==z3.sat
    wrong=(*fixed(riders,(1,2,3)),*fixed(bikes,(3,1,2)))
    right=(*fixed(riders,(1,2,3)),*fixed(bikes,(2,3,1)))
    assert check(row_aligned,*wrong)[0]==z3.sat and check(actual,*wrong)[0]==z3.unsat
    assert check(actual,*right)[0]==z3.sat and check(row_aligned,*right)[0]==z3.unsat
    report('inverse-coordinate-counterexamples',dict(xor='sat',witness=witness,
        row_aligned_only=dict(riders=[1,2,3],bikes=[3,1,2]),
        source_shared_id_only=dict(riders=[1,2,3],bikes=[2,3,1]),solver_limits=None))


def test_distinct_count_complete_feasibility_and_exact_cost_with_first_occurrence_oracle():
    _,actual,objectives=compiled('distinct_label_objective');assert len(objectives)==1
    labels=elements('labels');cost=objectives[0]
    expected=z3.And(*[z3.And(value>=2,value<=5) for value in labels],labels[0]!=labels[1])
    oracle=z3.Sum([z3.If(z3.And(*[labels[i]!=labels[j] for j in range(i)]),1,0)
                   for i in range(3)])
    assert check(z3.Xor(actual,expected))[0]==z3.unsat
    assert check(actual,cost!=oracle)[0]==z3.unsat
    rows=[];counts={2:0,3:0}
    for point in product(range(2,6),repeat=3):
        assignments=fixed(labels,point);feasible=point[0]!=point[1]
        result,_=check(actual,*assignments);assert result==(z3.sat if feasible else z3.unsat)
        # Independent host oracle counts first appearances, not domain labels.
        point_cost=sum(all(point[i]!=point[j] for j in range(i)) for i in range(3))
        if feasible:
            assert check(actual,*assignments,cost!=point_cost)[0]==z3.unsat
            assert check(actual,*assignments,cost==point_cost)[0]==z3.sat
            counts[point_cost]+=1
        rows.append(dict(point=point,feasible=feasible,first_occurrence_cost=point_cost,
                         compiled_feasibility=str(result),point_cost_proved=feasible))
    assert counts=={2:24,3:24}
    report('distinct-count-exact-oracle',dict(full_relation_xor='unsat',full_cost_disequality='unsat',
        oracle='sum_i indicator(all j<i: label_i != label_j)',all_domain_points=64,
        feasible_domain_points=48,cost_histogram=counts,points=rows,solver_limits=None))


def test_maximum_label_replacement_changes_cost_without_changing_feasibility():
    _,actual,objectives=compiled('distinct_label_objective')
    labels=elements('labels');cost=objectives[0]
    maximum=z3.If(labels[0]>=labels[1],labels[0],labels[1])
    maximum=z3.If(maximum>=labels[2],maximum,labels[2])
    result,witness=check(actual,cost!=maximum);assert result==z3.sat
    for point,max_value in [((2,3,2),3),((2,5,2),5)]:
        assert check(actual,*fixed(labels,point),cost==2,maximum==max_value)[0]==z3.sat
    # This domain starts at two: equality is impossible throughout the full
    # feasible relation, even though both objectives allow the two-label optimum.
    assert check(actual,cost==maximum)[0]==z3.unsat
    report('maximum-label-objective-counterexample',dict(cost_disequality='sat',witness=witness,
        points=[dict(labels=[2,3,2],distinct_cost=2,max_cost=3),
                dict(labels=[2,5,2],distinct_cost=2,max_cost=5)],
        same_feasible_relation=True,no_canonical_label_constraints_added=True,solver_limits=None))


def test_new_patterns_spans_and_catalog_are_fresh_and_complete():
    for name in ('shared_identity_coordinates','distinct_label_objective'):
        pattern=hir_api()['modeling_patterns'][name]
        annotated=pattern['model']['constraints']+pattern['model']['objectives']
        assert [pattern['source'][r['span'][0]:r['span'][1]] for r in annotated]==pattern['source'].splitlines()
        assert pattern['model']['assumptions']==pattern['model']['unresolved']==[]
    changed=hir_api()['modeling_patterns'];changed['shared_identity_coordinates']['model']['declarations'][0]['upper']=1
    assert hir_api()['modeling_patterns']['shared_identity_coordinates']['model']['declarations'][0]['upper']==3
