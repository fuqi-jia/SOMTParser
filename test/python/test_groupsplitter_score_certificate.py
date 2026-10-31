"""Finite certificate controls; synthetic source clauses are not compilation tests."""
import copy
import itertools
import pytest
import z3

from tools.semantic_checks.groupsplitter_score_certificate import (
    REQUIRED, check_groupsplitter_score_bound, _finite_relation, source_facts)


def source():
    return ('include "count.mzn"; include "table.mzn";\n' + '\n'.join(REQUIRED.values()) +
            '\nsolve maximize objective;').encode()


def fixture(eta=9):
    a = [[[1, 9, 2, 1, 4], [2, 10, 3, 2, 1]],
         [[3, 12, 2, 2, 5], [4, 14, 3, 1, 2]]]
    p = [[[2, -1], [1, 2]], [[0, 2], [1, -2]]]
    return dict(users=2, eta=eta, activities=a, preferences=p)


def data(f):
    def matrix(rows):
        return '[|' + '|'.join(','.join(map(str, r)) for r in rows) + '|]'
    s = f'user_ids=1..{f["users"]}; group_ids=1..1; eta={f["eta"]};'
    for phase in (1, 2):
        s += f'activity{phase}_ids=1..{len(f["activities"][phase-1])};'
        s += f'activities{phase}={matrix(f["activities"][phase-1])};'
        s += f'preferences{phase}={matrix(f["preferences"][phase-1])};'
    return s.encode()


def relation(rows, arity, default=False):
    def build(rows, depth):
        if depth == 0:
            return z3.BoolVal(bool(rows))
        base = z3.BoolVal(default)
        for _ in range(depth-1):
            base = z3.K(z3.IntSort(), base)
        result = z3.K(z3.IntSort(), base)
        for key in sorted({r[0] for r in rows}):
            result = z3.Store(result, key, build([r[1:] for r in rows if r[0] == key], depth-1))
        return result
    return build(rows, arity)


def target(f, mutate=None, extra_objective=False):
    v = {f'{stem}{p}':z3.Array(f'{stem}{p}',z3.IntSort(),z3.IntSort())
         for p in (1,2) for stem in ['user_group_map','group_act_map','user_act_map',
           'activity_available_from','user_end_map','user_duration_map','user_cell_map',
           'user_pub_rating_map','user_weight_map']}
    obj=z3.Int('objective'); clauses={}; terms=[]
    for p in (1,2):
        sel=lambda stem,u:z3.Select(v[f'{stem}{p}'],u)
        aa=relation([(j+1,*r)for j,r in enumerate(f['activities'][p-1])],6)
        pp=relation([(u,j+1,x)for u,row in enumerate(f['preferences'][p-1],1)for j,x in enumerate(row)],3)
        for u in range(1,f['users']+1):
            g=sel('user_group_map',u)
            clauses[f'g{p}{u}lo']=g>=1;clauses[f'g{p}{u}hi']=g<=1
            clauses[f'c{p}{u}']=sel('user_act_map',u)==z3.Select(v[f'group_act_map{p}'],g)
            ar=aa
            for stem in ['user_act_map','activity_available_from','user_end_map','user_duration_map','user_cell_map','user_pub_rating_map']:
                ar=z3.Select(ar,sel(stem,u))
            clauses[f'a{p}{u}']=ar
            clauses[f'p{p}{u}']=z3.Select(z3.Select(z3.Select(pp,u),sel('user_act_map',u)),sel('user_weight_map',u))
        terms.extend([f['eta']*z3.Sum([sel('user_weight_map',u)for u in range(1,f['users']+1)]),
                      (10-f['eta'])*z3.Sum([sel('user_pub_rating_map',u)for u in range(1,f['users']+1)])])
    clauses['objective']=obj==z3.Sum(terms)
    if mutate:
        mutate(clauses,v,obj)
    opt=z3.Optimize();opt.add(*clauses.values());opt.maximize(obj)
    if extra_objective:opt.minimize(obj)
    text=opt.sexpr()
    if '(check-sat)' not in text:text+='\n(check-sat)'
    return (text+'\n(exit)\n').encode()


@pytest.mark.parametrize('eta',[0,1,5,9,10])
def test_full_target_and_source_score_bound(eta):
    f=fixture(eta);r=check_groupsplitter_score_bound(source(),data(f),target(f))
    expected=max(sum(eta*sum(row[j]for row in f['preferences'][p])+
                     (10-eta)*f['users']*f['activities'][p][j][4]for p,j in enumerate(pair))
                 for pair in itertools.product(range(2),repeat=2))
    assert r['source_upper_bound']==r['target_upper_bound']==expected
    assert not r['solver_optimality_claimed'] and not r['candidate_coordinates_used']


@pytest.mark.parametrize('key',['g11lo','g11hi','c11','a11','p11','objective'])
def test_missing_real_premise_rejected(key):
    f=fixture();t=target(f,lambda c,v,o:c.pop(key))
    with pytest.raises(ValueError,match='missing complete target'):
        check_groupsplitter_score_bound(source(),data(f),t)


@pytest.mark.parametrize('key',['g11hi','c11','objective'])
def test_changed_real_premise_rejected(key):
    f=fixture()
    def mutate(c,v,o):
        c[key]={'g11hi':z3.Select(v['user_group_map1'],1)<=2,
                'c11':z3.Select(v['user_act_map1'],1)==z3.Select(v['group_act_map1'],2),
                'objective':o==999}[key]
    with pytest.raises(ValueError,match='missing complete target clause'):
        check_groupsplitter_score_bound(source(),data(f),target(f,mutate))


@pytest.mark.parametrize('field',['activities','preferences'])
def test_target_data_table_mismatch(field):
    f=fixture();bad=copy.deepcopy(f)
    if field=='activities':bad[field][0][0][-1]=5
    else:bad[field][0][0][0]=-2
    with pytest.raises(ValueError,match='table differs from source'):
        check_groupsplitter_score_bound(source(),data(f),target(bad))


def test_second_objective_rejected():
    f=fixture()
    with pytest.raises(ValueError,match='complete target maximized objective'):
        check_groupsplitter_score_bound(source(),data(f),target(f,extra_objective=True))


def test_reified_tables_do_not_count_as_hard_premise():
    f=fixture()
    def mutate(c,v,o):c['a11']=z3.Implies(z3.Bool('enabled'),c['a11'])
    with pytest.raises(ValueError,match='missing complete target table'):
        check_groupsplitter_score_bound(source(),data(f),target(f,mutate))


def test_added_constraints_only_restrict_bound():
    f=fixture()
    t=target(f,lambda c,v,o:c.update(extra=z3.BoolVal(False)))
    assert check_groupsplitter_score_bound(source(),data(f),t)['passed']


@pytest.mark.parametrize('old,new,match',[
    ('group_ids=1..1','group_ids=1..2','single group'),
    ('user_ids=1..2','user_ids=0..1','one-based'),
    ('eta=9','eta=11','eta outside'),
    ('eta=9',"'eta'=9",'ordinary data'),
    ('eta=9','eta=9; objective=123','unknown or duplicate'),
    ('eta=9','eta=9; activities1_data=[]','unknown or duplicate'),
    ('eta=9','eta=9; eta=8','unknown or duplicate'),
])
def test_changed_data_scope(old,new,match):
    f=fixture()
    with pytest.raises(ValueError,match=match):
        source_facts(source(),data(f).replace(old.encode(),new.encode()))


@pytest.mark.parametrize('addition,match',[
    ('include "other.mzn";','only standard'),
    ('function int: sum(array[int] of int: a)=999;','custom source'),
    ('eta=4;','extra source assignment'),
    ("int: 'eta' = 4;",'quoted source'),
    ('/* fake constraint; */','block comments'),
])
def test_changed_source_scope(addition,match):
    with pytest.raises(ValueError,match=match):
        source_facts(source()+addition.encode(),data(fixture()))


def test_objective_source_changed_rejected():
    changed=source().replace(b'eta * sum(user_weight_map1)',b'eta * sum(user_weight_map2)')
    with pytest.raises(ValueError,match='unsupported source clause: objective'):
        source_facts(changed,data(fixture()))


def test_relation_last_write_and_negative_keys():
    a=z3.K(z3.IntSort(),z3.BoolVal(False));a=z3.Store(z3.Store(z3.Store(a,-1,True),3,True),-1,False)
    assert _finite_relation(a,1)=={(3,)}


def test_relation_nested_default_is_checked():
    a=z3.K(z3.IntSort(),z3.K(z3.IntSort(),z3.BoolVal(False)))
    a=z3.Store(a,1,z3.K(z3.IntSort(),z3.BoolVal(True)))
    with pytest.raises(ValueError,match='infinite nonempty relation default'):_finite_relation(a,2)


def test_relation_symbolic_write_rejected():
    a=z3.Store(z3.K(z3.IntSort(),z3.BoolVal(False)),z3.Int('i'),True)
    with pytest.raises(ValueError,match='symbolic relation store key'):_finite_relation(a,1)


def test_relation_shared_nested_rows_and_removed_rows():
    row=z3.Store(z3.K(z3.IntSort(),z3.BoolVal(False)),4,True)
    empty=z3.K(z3.IntSort(),z3.BoolVal(False))
    a=z3.K(z3.IntSort(),empty);a=z3.Store(z3.Store(z3.Store(a,1,row),2,row),1,empty)
    assert _finite_relation(a,2)=={(2,4)}


@pytest.mark.parametrize('eta',[0,9])
def test_complete_tiny_target_attains_bound_and_rejects_improvement(eta):
    from tools.semantic_checks.source_oracles.target_relation import read_target
    f=fixture(eta);raw=target(f);r=check_groupsplitter_score_bound(source(),data(f),raw)
    v,program,_=read_target(raw)
    solver=z3.Solver();solver.add(*program.assertions(),v['objective']>r['upper_bound'])
    assert solver.check()==z3.unsat
    solver=z3.Solver();solver.add(*program.assertions(),v['objective']==r['upper_bound'])
    assert solver.check()==z3.sat


def test_parsed_negative_literal_store_key():
    expr=z3.parse_smt2_string('(declare-const x Int) (assert (select (store ((as const (Array Int Bool)) false) (- 2) true) x))')[0]
    assert _finite_relation(expr.arg(0),1)=={(-2,)}
