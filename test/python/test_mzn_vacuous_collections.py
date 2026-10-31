"""Empty generators validate syntax without executing a nominal iteration."""
import pytest
import z3
import somtparser as sp


def checked(source):
    result = sp.translate(source=source + ' solve satisfy;', language='minizinc')
    assert result.ok, [d.message for d in result.diagnostic_items]
    script = result.to_smt2(sp.OmtDialect.Z3)
    solver = z3.Solver()
    solver.add(*z3.parse_smt2_string(script))
    assert solver.check() == z3.sat
    return script


def test_carpet_stair_arrays_with_empty_dependent_generators():
    checked('''
      set of int: Stairs = 1..0;
      array[Stairs] of int: st_no_steps = [];
      array[Stairs] of int: st_len = [];
      array[Stairs] of int: offset =
        [sum(j in Stairs where j<i)(st_no_steps[j]) | i in Stairs];
      array[Stairs] of set of int: ids =
        [(offset[i]+1)..(offset[i]+st_no_steps[i]) | i in Stairs];
      array[1..0] of int: lengths =
        [st_len[i] div st_no_steps[i] | i in Stairs, j in ids[i]];
      constraint sum(lengths)=0;
    ''')


@pytest.mark.parametrize('head', ['a[i]..a[i]', '{a[i]}'])
def test_false_filter_does_not_evaluate_set_array_head(head):
    checked('array[1..0] of int:a=[]; '
            f'array[1..0] of set of int:b=[{head} | i in 1..2 where false];')


@pytest.mark.parametrize('data_kind', ['inline', 'dzn', 'json'])
def test_dependent_empty_set_array_range_and_filter(data_kind, tmp_path):
    declarations = 'array[1..0] of set of int:a;array[1..0] of bool:b;'
    data = []
    if data_kind == 'inline':
        declarations = declarations.replace(':a;', ':a=[];').replace(':b;', ':b=[];')
    else:
        path = tmp_path / ('empty.' + data_kind)
        path.write_text('a=[];b=[];' if data_kind == 'dzn' else '{"a":[],"b":[]}')
        data.append(str(path))
    result = sp.translate(source=declarations +
                          'array[1..0] of set of int:c=[{j} | i in 1..0,j in a[i] where b[i]];'
                          'solve satisfy;', language='minizinc', data=data)
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.add(*z3.parse_smt2_string(result.to_smt2()))
    assert solver.check() == z3.sat


@pytest.mark.parametrize('comprehension', [
    'array[1..0] of int:a=[missing | i in 1..0];',
    'array[1..0] of set of int:a=[true | i in 1..0];',
    'array[1..0] of int:a=[i | i in 1..0 where 3];',
    'array[1..0] of set of int:a=[{i} | i in 1..0 where 3];',
    'constraint forall(i in 1..0 where 3)(true);',
    'constraint sum([{1} | i in 1..0])=0;',
])
def test_empty_generation_does_not_hide_invalid_names_or_types(comprehension):
    result = sp.translate(source=comprehension+'solve satisfy;', language='minizinc')
    assert not result.ok


@pytest.mark.parametrize('declaration', [
    'array[1..1] of set of int:b=[{a[i]} | i in 1..1];',
    'array[1..1] of int:b=[a[i] | i in 1..1];',
])
def test_executed_out_of_bounds_reads_still_fail(declaration):
    result = sp.translate(source='array[1..0] of int:a=[];'+declaration+'solve satisfy;',
                          language='minizinc')
    assert not result.ok
    assert any('outside' in d.message for d in result.diagnostic_items)


def test_let_set_domain_and_array_declarations_do_not_escape_empty_probe():
    script = checked('array[1..0] of int:a=[]; constraint forall(i in 1..0)'
                     '(let {int:os=a[i],set of int:J=1..a[i],'
                     'array[J] of var bool:last_part} in last_part[a[i]]);')
    assert not any('(declare-fun ' in line and '@let' in line for line in script.splitlines())


def test_local_sets_and_scalar_shadowing_restore_outer_types():
    checked('set of int:J=4..5; constraint let {set of int:J=1..2;'
            'array[J] of var bool:a;} in forall(j in J)(a[j]);'
            'constraint card(J)=2 /\\ min(J)=4;'
            'constraint (let {int:J=3;} in J=3);')
    checked('array[1..2] of int:J=[7,8];'
            'constraint (let {set of int:J=1..3;} in sum(j in J)(j)=6);'
            'constraint J[1]=7;')
    checked('set of int:J=1..2;'
            'constraint (let {set of int:J=J union {3};} in card(J)=3);'
            'constraint card(J)=2;')


def test_two_local_arrays_over_local_sets_have_independent_choices():
    checked('constraint (let {set of int:J=1..1;array[J] of var bool:a;} in a[1])'
            ' /\\ (let {set of int:J=1..1;array[J] of var bool:a;} in not a[1]);')
