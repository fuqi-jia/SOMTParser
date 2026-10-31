"""Exact set extrema and demanded fields in compiler output observations."""
import json
import pytest
import z3
from tools.semantic_checks.source_oracles.fzn_json_source import read_source, Unsupported
from tools.semantic_checks.source_oracles.ozn_observations import Program


def model(method='minimize'):
    return read_source(json.dumps(dict(version='1.0',
        variables={'x': {'type': 'int', 'domain': [[-10, 20]]}},
        arrays={'admission_days': {'a': ['x', 25]}}, constraints=[],
        output=['x', 'admission_days'],
        solve={'method': method, 'objective': 'x'})).encode())


def equivalent(a, b):
    solver = z3.Solver(); solver.add(z3.Xor(a, b)); assert solver.check() == z3.unsat


@pytest.mark.parametrize('name,values,expected', [
    ('min', '{-100,7,3}', -100), ('max', '{-100,7,3}', 7),
    ('min', '-8..-3', -8), ('max', '-8..-3', -3),
    ('max', '{123456789012345678901234567890}', 123456789012345678901234567890),
])
def test_fixed_set_extremum_is_exact(name, values, expected):
    program = Program('set of int: D='+values+'; int: y='+name+'(D);', model())
    assert program.observations(['y'])[0]['value'].eq(z3.IntVal(expected))


@pytest.mark.parametrize('name', ['min', 'max'])
def test_empty_set_has_no_invented_extremum(name):
    with pytest.raises(Unsupported, match='empty OZN extremum'):
        Program('int: y='+name+'({});', model()).observations(['y'])


def test_set_extremum_defines_actual_array_coordinates():
    program = Program('set of int: I={-3,2}; array[min(I)..max(I)] of int: a=array1d(min(I)..max(I),[7,8,9,10,11,12]);', model())
    rows = program.observations(['a'])
    assert [row['indices'] for row in rows] == [(i,) for i in range(-3,3)]
    assert [row['value'].as_long() for row in rows] == list(range(7,13))


def test_record_fields_are_selected_by_name_and_preserve_nested_values():
    text = 'record(int: a, record(int: b): child): r=(child:(b:9),a:-4); int: y=r.child.b+r.a;'
    assert z3.simplify(Program(text, model()).observations(['y'])[0]['value']).as_long() == 5


def test_record_comprehensions_capture_each_generator_environment():
    program = Program('array[1..3] of record(int: day): r=[(day:2*i) | i in 1..3];'
                      'array[1..3] of int: a=[r[i].day | i in 1..3];', model())
    assert [z3.simplify(row['value']).as_long() for row in program.observations(['a'])] == [2,4,6]


def test_unused_record_display_fields_are_not_evaluated():
    # Output reconstruction only needs release. Nested display arrays have
    # different lengths and contain no observed decision coordinate.
    program = Program('array[1..2] of record(string: label, array[1..1] of int: display, int: release):'
        'r=[(release:3,label:"first",display:[4]),(display:[4,5],label:"second",release:7)];'
        'int: y=r[1].release+r[2].release;', model())
    assert z3.simplify(program.observations(['y'])[0]['value']).as_long() == 10


@pytest.mark.parametrize('method', ['minimize', 'maximize'])
def test_complete_patient_observations_and_signed_cost(method):
    flat = model(method)
    program = Program('set of int: DAYS=1..14; set of int: PATIENTS=1..2;'
        'array[PATIENTS] of int: admission_days;'
        'array[PATIENTS] of record(string: id, int: surgery_release_day): patients='
        '[(id:"p0",surgery_release_day:5),(id:"p1",surgery_release_day:3)];'
        'int: delay=sum([if admission_days[p]>max(DAYS) then 0 else '
        'admission_days[p]-patients[p].surgery_release_day endif | p in PATIENTS]);'
        'int: unscheduled=sum([bool2int(admission_days[p]>max(DAYS)) | p in PATIENTS]);', flat)
    rows = program.observations(['admission_days','delay','unscheduled'])
    a,b,delay,unscheduled,cost = z3.Ints('a b delay unscheduled cost')
    actual = flat.projected(list(zip([a,b,delay,unscheduled], [r['value'] for r in rows])), signed_cost=cost)
    expected = z3.And(a>=-10,a<=20,b==25,delay==z3.If(a>14,0,a-5),
                      unscheduled==1+z3.If(a>14,1,0),cost==(a if method=='minimize' else -a))
    equivalent(actual,expected)
    wrong = z3.And(a>=-10,a<=20,b==25,delay==z3.If(a>14,0,a-3),
                   unscheduled==1+z3.If(a>14,1,0),cost==(a if method=='minimize' else -a))
    solver=z3.Solver();solver.add(z3.Xor(actual,wrong));assert solver.check()==z3.sat


@pytest.mark.parametrize('text,reason', [
    ('record(int:a):r=(a:1,a:2); int:y=r.a;', 'duplicate'),
    ('record(int:a):r=(b:1); int:y=r.b;', 'fields differ'),
    ('record(int:a):r=(a:true); int:y=r.a;', 'Int sort'),
    ('record(int:a):r=(a:1); int:y=r.b;', 'unknown OZN record field'),
    ('record(int:a):r=(a:r.a); int:y=r.a;', 'cyclic'),
    ('int:y=(1).a;', 'nonrecord'),
])
def test_invalid_requested_fields_cannot_invent_an_observation(text, reason):
    with pytest.raises(Unsupported,match=reason):Program(text,model()).observations(['y'])


def test_nonconstant_record_index_is_not_silently_approximated():
    program=Program('int:x; array[1..2] of record(int:a):r=[(a:1),(a:2)]; int:y=r[x].a;',model())
    with pytest.raises(Unsupported):program.observations(['y'])


def test_integer_array_indices_are_not_implicitly_rebased():
    # MiniZinc specification 4.1.6.6 requires explicit array1d here.
    with pytest.raises(Unsupported, match='declared extent mismatch'):
        Program('array[-3..2] of int: a=[7,8,9,10,11,12];', model()).observations(['a'])
