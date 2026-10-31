"""Semantic and mutation controls for the narrow capacity certificate."""
import json

import pytest
import z3

from tools.semantic_checks.skill_capacity_certificate import (REQUIRED_SOURCE, check_skill_capacity_bound,
                                                               check_skill_capacity_group_bounds)


def fixture(engineers=4, jobs=7, capacity=2, known=1):
    source = ('\n'.join(REQUIRED_SOURCE.values()) + '\nsolve minimize objective;\n').encode()
    matrix = [[int(e < known)] for e in range(engineers)]
    def literal(rows):
        return '[|' + '|'.join(','.join(map(str,row)) for row in rows) + '|]'
    data = (f'nNewSkillsPerPerson=1;\nnMaxJobs={capacity};\nsSkills=["one"];\n'
            + 'engineer_skills=' + literal(matrix) + ';\njobs='
            + literal([[1,0,0,0,0] for _ in range(jobs)]) + ';\n').encode()
    A, T = z3.Array('allocations', z3.IntSort(), z3.IntSort()), z3.Array('new_skills', z3.IntSort(), z3.IntSort())
    objective = z3.Int('objective')
    constraints = []
    for j in range(1,jobs+1):
        constraints += [A[j] >= 1, A[j] <= engineers]
    for j in range(1,jobs+1):
        constraints += [z3.Or(*([A[j] == e for e in range(1,known+1)] +
                               [z3.And(A[j] == e,T[e-1] == 1) for e in range(1,engineers+1)]))]
    for e in range(1,engineers+1):
        constraints += [z3.Sum([z3.If(A[j] == e,1,0) for j in range(1,jobs+1)]) <= capacity]
    constraints += [objective == z3.Sum([z3.If(T[e-1] > 0,1,0) for e in range(1,engineers+1)])]
    projection = [dict(id=f'allocations[{j}]',symbol='allocations',indices=[j],source_name='allocations',source_indices=[j]) for j in range(1,jobs+1)]
    projection += [dict(id=f'new_skills[{e},1]',symbol='new_skills',indices=[e-1],source_name='new_skills',source_indices=[e,1]) for e in range(1,engineers+1)]
    projection += [dict(id='objective',symbol='objective',indices=[],source_name='objective',source_indices=[])]
    return source,data,constraints,projection,A,T,objective


def target(constraints, objective, maximize=False):
    solver=z3.Optimize()
    solver.add(*constraints)
    (solver.maximize if maximize else solver.minimize)(objective)
    return (solver.sexpr()+'\n(exit)\n').encode()


@pytest.mark.parametrize('engineers,jobs,capacity,known',[(4,7,2,1),(5,9,2,1),(4,6,3,0),(3,3,1,2),(3,2,2,2),(5,11,3,1)])
def test_lower_bound_matches_full_synthetic_unsat_query(engineers,jobs,capacity,known):
    source,data,clauses,p,A,T,obj=fixture(engineers,jobs,capacity,known)
    report=check_skill_capacity_bound(source,data,target(clauses,obj),p,[1])
    expected=max(0,(jobs+capacity-1)//capacity-known)
    assert report['lower_bound']==expected
    # This is an independent complete-model test of the claimed theorem.
    solver=z3.Solver();solver.add(*clauses,obj<expected)
    assert solver.check()==z3.unsat
    solver=z3.Solver();solver.add(*clauses,obj==expected)
    assert solver.check()==z3.sat


def test_reordered_full_target_and_extra_constraints_remain_sound():
    source,data,clauses,p,A,T,obj=fixture()
    altered=[z3.And(*reversed(clauses)),T[0]>=0]
    report=check_skill_capacity_bound(source,data,target(altered,obj),p,[1])
    assert report['source_lower_bound']==report['target_lower_bound']==3
    assert report['candidate_coordinates_used'] is False


@pytest.mark.parametrize('mutation',['escaped-domain','missing-skill','unpaid-alternative','higher-capacity','missing-capacity','guarded-capacity','missing-charge','weighted-charge','wrong-charge','duplicated-job','changed-objective','maximize'])
def test_changed_real_target_ast_is_rejected(mutation):
    source,data,clauses,p,A,T,obj=fixture();clauses=list(clauses);goal=obj;maximize=False
    if mutation=='escaped-domain':clauses[1]=A[1]<=5
    elif mutation=='missing-skill':clauses[14]=z3.BoolVal(True)
    elif mutation=='unpaid-alternative':clauses[14]=z3.Or(clauses[14],A[1]==4)
    elif mutation=='higher-capacity':clauses[21]=z3.Sum([z3.If(A[j]==1,1,0)for j in range(1,8)])<=3
    elif mutation=='missing-capacity':clauses[21]=z3.BoolVal(True)
    elif mutation=='guarded-capacity':clauses[21]=z3.Or(z3.Bool('bypass_capacity'),clauses[21])
    elif mutation=='missing-charge':clauses[-1]=obj==z3.Sum([z3.If(T[e]>0,1,0)for e in range(3)])
    elif mutation=='weighted-charge':clauses[-1]=obj==2*z3.Sum([z3.If(T[e]>0,1,0)for e in range(4)])
    elif mutation=='wrong-charge':clauses[-1]=obj==z3.Sum([z3.If(T[e]>1,1,0)for e in range(4)])
    elif mutation=='duplicated-job':clauses[21]=z3.Sum([z3.If(A[j]==1,1,0)for j in [1,2,3,4,5,6,6]])<=2
    elif mutation=='changed-objective':goal=obj+1
    else:maximize=True
    if mutation=='escaped-domain':reason='allocation-1-upper'
    elif mutation in ['missing-skill','unpaid-alternative']:reason='job-1-skill-1'
    elif mutation in ['higher-capacity','missing-capacity','guarded-capacity','duplicated-job']:reason='engineer-1-complete-job-capacity'
    elif mutation in ['changed-objective','maximize']:reason='complete original objective/direction changed'
    else:reason='complete-positive-training-objective'
    with pytest.raises(ValueError,match=reason):check_skill_capacity_bound(source,data,target(clauses,goal,maximize),p,[1])


@pytest.mark.parametrize('mutation',['bypass','capacity-off','two-slots','different-source-charge','different-source-capacity','different-data-known','duplicate-skills','projection-cell','projection-omission'])
def test_changed_source_data_and_coordinate_identity_are_rejected(mutation):
    source,data,clauses,p,A,T,obj=fixture();group=[1]
    if mutation=='bypass':data+=b'allEng=true;\n'
    elif mutation=='capacity-off':data=data.replace(b'nMaxJobs=2;',b'nMaxJobs=0;')
    elif mutation=='two-slots':data=data.replace(b'nNewSkillsPerPerson=1;',b'nNewSkillsPerPerson=2;')
    elif mutation=='different-source-charge':source=source.replace(b'new_skills[e,t] > 0',b'new_skills[e,t] > 1')
    elif mutation=='different-source-capacity':source=source.replace(b'<= nMaxJobs',b'<= nMaxJobs + 1')
    elif mutation=='different-data-known':data=data.replace(b'engineer_skills=[|1|0|0|0|]',b'engineer_skills=[|1|1|0|0|]')
    elif mutation=='duplicate-skills':group=[1,1]
    elif mutation=='projection-cell':p=[dict(x)for x in p];p[7]['indices']=[1]
    elif mutation=='projection-omission':p=p[:-1]
    reasons={'bypass':'skill-matching bypass','capacity-off':'disabled job capacity','two-slots':'complete typed original-to-target coordinate map differs','different-source-charge':'unsupported source clause: objective_count','different-source-capacity':'unsupported source clause: job_capacity','different-data-known':'job-1-skill-1','duplicate-skills':'duplicate selected skill','projection-cell':'complete typed original-to-target coordinate map differs','projection-omission':'complete typed original-to-target coordinate map differs'}
    with pytest.raises(ValueError,match=reasons[mutation]):check_skill_capacity_bound(source,data,target(clauses,obj),p,group)


def test_scope_rejects_multiple_ordered_objectives():
    source,data,clauses,p,A,T,obj=fixture()
    solver=z3.Optimize();solver.add(*clauses);solver.minimize(obj);solver.maximize(A[1])
    with pytest.raises(ValueError,match='complete original objective/direction changed'):check_skill_capacity_bound(source,data,(solver.sexpr()+'\n(exit)\n').encode(),p,[1])


def test_legal_trailing_skill_comma_and_percent_comment_use_actual_tokens():
    source,data,clauses,p,A,T,obj=fixture()
    data=b'% engineer_skills=[|1|1|1|1|];\n'+data.replace(b'sSkills=["one"];',b'sSkills=["one",];')
    assert check_skill_capacity_bound(source,data,target(clauses,obj),p,[1])['lower_bound']==3


def test_commented_valid_matrix_cannot_hide_changed_real_matrix():
    source,data,clauses,p,A,T,obj=fixture()
    data=b'% engineer_skills=[|1|0|0|0|];\n'+data.replace(b'engineer_skills=[|1|0|0|0|]',b'engineer_skills=[|1|1|0|0|]')
    with pytest.raises(ValueError,match='job-1-skill-1'):check_skill_capacity_bound(source,data,target(clauses,obj),p,[1])


def test_block_comment_cannot_supply_missing_real_capacity():
    source,data,clauses,p,A,T,obj=fixture()
    original=REQUIRED_SOURCE['job_capacity'].encode()
    source=source.replace(original,b'/* ; '+original+b' ; */')
    with pytest.raises(ValueError,match='block comments'):check_skill_capacity_bound(source,data,target(clauses,obj),p,[1])


def test_boolean_array_index_is_not_an_integer_coordinate():
    source,data,clauses,p,A,T,obj=fixture()
    p=[dict(row)for row in p];p[0]['indices']=[True]
    with pytest.raises(ValueError,match='complete typed original-to-target coordinate map differs'):check_skill_capacity_bound(source,data,target(clauses,obj),p,[1])


@pytest.mark.parametrize('assignment',["'allEng'=true;", "'nMaxJobs'=0;"])
def test_quoted_data_alias_cannot_bypass_checked_parameters(assignment):
    source,data,clauses,p,A,T,obj=fixture()
    with pytest.raises(ValueError,match='only ordinary identifier data assignments'):
        check_skill_capacity_bound(source,data+assignment.encode(),target(clauses,obj),p,[1])


@pytest.mark.parametrize('statement',['include "override.dzn";', 'int: allEng=1;', 'constraint allEng=true;'])
def test_nonassignment_data_statements_are_rejected(statement):
    source,data,clauses,p,A,T,obj=fixture()
    with pytest.raises(ValueError,match='only ordinary identifier data assignments'):
        check_skill_capacity_bound(source,data+statement.encode(),target(clauses,obj),p,[1])


@pytest.mark.parametrize('name',['SKILLS','ENGS','JOBS','TRAINING','allocations','new_skills','objective'])
def test_data_cannot_override_derived_domains_or_decisions(name):
    source,data,clauses,p,A,T,obj=fixture()
    with pytest.raises(ValueError,match='data key is not an original input parameter'):
        check_skill_capacity_bound(source,data+(name+'={1};').encode(),target(clauses,obj),p,[1])


@pytest.mark.parametrize('statement',[
    'function var int: sum(array[int] of var bool: xs)=0;',
    'predicate forbidden(var int:x)=true;', 'test forbidden(int:x)=true;',
    'type Alias = int;', 'enum Extra={a,b};', 'annotation custom;',
])
def test_custom_source_semantic_definitions_are_rejected(statement):
    source,data,clauses,p,A,T,obj=fixture()
    with pytest.raises(ValueError,match='custom source definitions'):
        check_skill_capacity_bound(source+statement.encode(),data,target(clauses,obj),p,[1])


def test_extra_source_include_is_rejected():
    source,data,clauses,p,A,T,obj=fixture()
    with pytest.raises(ValueError,match='only the standard globals include'):
        check_skill_capacity_bound(source+b'include "override.mzn";',data,target(clauses,obj),p,[1])


def test_extra_source_parameter_assignment_is_rejected():
    source,data,clauses,p,A,T,obj=fixture()
    with pytest.raises(ValueError,match='extra top-level source assignments'):
        check_skill_capacity_bound(source+b'nMaxJobs=0;',data,target(clauses,obj),p,[1])


def test_quoted_source_identifier_is_rejected():
    source,data,clauses,p,A,T,obj=fixture()
    with pytest.raises(ValueError,match='quoted source identifiers'):
        check_skill_capacity_bound(source+b"constraint 'allEng'=false;",data,target(clauses,obj),p,[1])


def test_unknown_plain_data_key_is_rejected():
    source,data,clauses,p,A,T,obj=fixture()
    with pytest.raises(ValueError,match='data key is not an original input parameter'):
        check_skill_capacity_bound(source,data+b'unexpected=0;',target(clauses,obj),p,[1])


def test_extra_source_constraint_and_standard_include_are_allowed():
    source,data,clauses,p,A,T,obj=fixture()
    source=b'include "globals.mzn";\n'+source+b'constraint objective>=0;'
    assert check_skill_capacity_bound(source,data,target(clauses,obj),p,[1])['lower_bound']==3


def group_fixture(slots=2, counts=(5,4), known=((1,), (2,), (), ()), capacity=3):
    source=('\n'.join(REQUIRED_SOURCE.values())+'\nsolve minimize objective;\n').encode()
    engineers=len(known);skills=len(counts)
    job_skills=[s for s,n in enumerate(counts,1) for _ in range(n)]
    matrix=[[int(s in row)for s in range(1,skills+1)]for row in known]
    literal=lambda rows:'[|'+'|'.join(','.join(map(str,row))for row in rows)+'|]'
    data=(f'nNewSkillsPerPerson={slots};nMaxJobs={capacity};sSkills='+json.dumps([str(i)for i in range(skills)])+';engineer_skills='+literal(matrix)+';jobs='+literal([[s,0,0,0,0]for s in job_skills])+';').encode()
    A=z3.Array('allocations',z3.IntSort(),z3.IntSort());T=z3.Array('new_skills',z3.IntSort(),z3.IntSort());obj=z3.Int('objective')
    clauses=[]
    for j in range(1,len(job_skills)+1):clauses.extend([A[j]>=1,A[j]<=engineers])
    for j,skill in enumerate(job_skills,1):
        clauses.append(z3.Or(*([A[j]==e for e,row in enumerate(known,1)if skill in row]+
                              [z3.And(A[j]==e,T[(e-1)*slots+t]==skill)for e in range(1,engineers+1)for t in range(slots)])))
    for e in range(1,engineers+1):clauses.append(z3.Sum([z3.If(A[j]==e,1,0)for j in range(1,len(job_skills)+1)])<=capacity)
    clauses.append(obj==z3.Sum([z3.If(T[i]>0,1,0)for i in range(engineers*slots)]))
    p=[dict(id=f'allocations[{j}]',symbol='allocations',indices=[j],source_name='allocations',source_indices=[j])for j in range(1,len(job_skills)+1)]
    p += [dict(id=f'new_skills[{e},{t}]',symbol='new_skills',indices=[(e-1)*slots+t-1],source_name='new_skills',source_indices=[e,t])for e in range(1,engineers+1)for t in range(1,slots+1)]
    p.append(dict(id='objective',symbol='objective',indices=[],source_name='objective',source_indices=[]))
    return source,data,clauses,p,A,T,obj


@pytest.mark.parametrize('slots',[1,2,3,5])
def test_disjoint_group_bounds_sum_and_are_attainable(slots):
    source,data,clauses,p,A,T,obj=group_fixture(slots=slots)
    report=check_skill_capacity_group_bounds(source,data,target(clauses,obj),p,[[1],[2]])
    assert report['lower_bound']==2 and [g['lower_bound']for g in report['skill_groups']]==[1,1]
    assert report['training_slots_per_engineer']==slots and report['groups_pairwise_disjoint']
    solver=z3.Solver();solver.add(*clauses,obj<2);assert solver.check()==z3.unsat
    solver=z3.Solver();solver.add(*clauses,obj==2);assert solver.check()==z3.sat
    # Grouping everything loses an integer-rounding improvement here.
    single=check_skill_capacity_bound(source,data,target(clauses,obj),p,[1,2])
    assert single['lower_bound']==1 and single['selected_skills']==[1,2]


def test_known_engineer_overlap_is_allowed_but_skill_overlap_is_not():
    source,data,clauses,p,A,T,obj=group_fixture(counts=(5,3),known=((1,2),(),(),(),()),capacity=2)
    report=check_skill_capacity_group_bounds(source,data,target(clauses,obj),p,[[1],[2]])
    assert report['lower_bound']==3
    assert all(g['known_engineer_union']==[1]for g in report['skill_groups'])
    solver=z3.Solver();solver.add(*clauses,obj<3);assert solver.check()==z3.unsat
    solver=z3.Solver();solver.add(*clauses,obj==3);assert solver.check()==z3.sat


def test_group_counts_clip_at_zero_and_cover_every_slot():
    source,data,clauses,p,A,T,obj=group_fixture(counts=(1,1),known=((1,2),(1,2)),capacity=2)
    report=check_skill_capacity_group_bounds(source,data,target(clauses,obj),p,[[1],[2]])
    assert report['lower_bound']==0 and all(g['lower_bound']==0 for g in report['skill_groups'])
    solver=z3.Solver();solver.add(*clauses,obj<0);assert solver.check()==z3.unsat


@pytest.mark.parametrize('groups,reason',[
    ([], 'nonempty list of skill groups'), ([[]], 'nonempty supported skill subset'),
    ([[1,1]], 'duplicate selected skill'), ([[1],[1]], 'overlapping or duplicate'),
    ([[1,2],[2]], 'overlapping or duplicate'), ([[1],[True]], 'nonempty supported skill subset'),
    ([[0]], 'nonempty supported skill subset'), ([[-1]], 'nonempty supported skill subset'),
    ([[3]], 'nonempty supported skill subset'), ([[1.0]], 'nonempty supported skill subset'),
    ([1], 'skill group must be'),
])
def test_group_validation_rejects_double_charging_and_noninteger_skills(groups,reason):
    source,data,clauses,p,A,T,obj=group_fixture()
    with pytest.raises(ValueError,match=reason):
        check_skill_capacity_group_bounds(source,data,target(clauses,obj),p,groups)


def test_zero_training_slots_rejected_before_target_check():
    source,data,clauses,p,A,T,obj=group_fixture()
    data=data.replace(b'nNewSkillsPerPerson=2;',b'nNewSkillsPerPerson=0;')
    with pytest.raises(ValueError,match='positive training slots'):
        check_skill_capacity_group_bounds(source,data,target(clauses,obj),p,[[1],[2]])


@pytest.mark.parametrize('mutation',[
    'slot-stride', 'source-slot-coordinate', 'duplicate-slot-projection', 'omit-slot-projection',
    'missing-second-slot-alternative', 'extra-unpaid-alternative', 'wrong-slot-alternative',
    'omit-second-slot-charge', 'duplicate-slot-charge', 'weight-second-slot-charge',
    'charge-only-group-one', 'nonpositive-charge', 'capacity-selected-only',
])
def test_complete_multi_slot_identity_and_clauses_required(mutation):
    source,data,clauses,p,A,T,obj=group_fixture();p=[dict(x)for x in p];clauses=list(clauses)
    reason='complete typed original-to-target coordinate map differs'
    if mutation=='slot-stride':p[11]['indices']=[1]
    elif mutation=='source-slot-coordinate':p[10]['source_indices']=[1,1]
    elif mutation=='duplicate-slot-projection':p[10]=dict(p[9])
    elif mutation=='omit-slot-projection':p.pop(10)
    else:
        if mutation=='missing-second-slot-alternative':
            clauses[18]=z3.Or(A[1]==1,*[z3.And(A[1]==e,T[(e-1)*2]==1)for e in range(1,5)])
        elif mutation=='extra-unpaid-alternative':clauses[18]=z3.Or(clauses[18],A[1]==4)
        elif mutation=='wrong-slot-alternative':
            clauses[18]=z3.Or(A[1]==1,*[z3.And(A[1]==e,T[e-1+t]==1)for e in range(1,5)for t in range(2)])
        elif mutation=='capacity-selected-only':
            clauses[27]=z3.Sum([z3.If(A[j]==1,1,0)for j in range(1,6)])<=3
        else:
            charges=[z3.If(T[i]>0,1,0)for i in range(8)]
            if mutation=='omit-second-slot-charge':charges.pop(1)
            elif mutation=='duplicate-slot-charge':charges[1]=charges[0]
            elif mutation=='weight-second-slot-charge':charges[1]=2*charges[1]
            elif mutation=='charge-only-group-one':charges=[z3.If(T[i]==1,1,0)for i in range(8)]
            else:charges=[z3.If(T[i]>=0,1,0)for i in range(8)]
            clauses[-1]=obj==z3.Sum(charges)
        reason=('engineer-1-complete-job-capacity'if mutation=='capacity-selected-only'else
                'job-1-skill-1'if mutation in ['missing-second-slot-alternative','extra-unpaid-alternative','wrong-slot-alternative']else
                'complete-positive-training-objective')
    with pytest.raises(ValueError,match=reason):
        check_skill_capacity_group_bounds(source,data,target(clauses,obj),p,[[1],[2]])


def test_same_engineer_can_train_two_disjoint_skills_without_double_charging():
    source,data,clauses,p,A,T,obj=group_fixture()
    # Both training slots of engineer3 supply the two required new skills.
    assignment=[A[j]==(1 if j<=3 else 3 if j<=5 else 2 if j<=8 else 3)for j in range(1,10)]
    assignment += [T[i]==({4:1,5:2}.get(i,0))for i in range(8)]
    solver=z3.Solver();solver.add(*clauses,*assignment,obj==2);assert solver.check()==z3.sat
    report=check_skill_capacity_group_bounds(source,data,target(clauses,obj),p,[[1],[2]])
    assert report['lower_bound']==2


def test_training_values_outside_selected_groups_cannot_reduce_positive_slot_cost():
    source,data,clauses,p,A,T,obj=group_fixture()
    report=check_skill_capacity_group_bounds(source,data,target(clauses,obj),p,[[1],[2]])
    # Deliberately omit training-domain constraints: the theorem does not need them.
    solver=z3.Solver();solver.add(*clauses,T[0]==-7,obj<report['lower_bound'])
    assert solver.check()==z3.unsat
