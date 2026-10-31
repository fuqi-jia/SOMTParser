"""Source modules preserve relations and unresolved calls without inventing tasks."""
import itertools
import re
from pathlib import Path

import pytest
import z3
import somtparser as sp

ROOT = Path(__file__).resolve().parents[2]


def imported(source, language):
    result = sp.import_module(source=source, language=language)
    assert result.ok, [d.message for d in result.diagnostics]
    return result


def formula(text):
    return z3.And(*z3.parse_smt2_string(text))


def equivalent(text, expected):
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(formula(text) != expected)
    assert solver.check() == z3.unsat


def test_empty_circuit_is_a_module_without_a_property():
    result = imported('aag 0 0 0 0 0\n', 'aiger')
    assert result.systems == [{'name': 'circuit', 'variables': [], 'output_count': 0, 'bad_count': 0}]
    assert not hasattr(result, 'solve') and hasattr(result, 'to_smt2')
    for part in ['init', 'trans', 'invariant']:
        equivalent(result.relation_smt2(0, part), z3.BoolVal(True))
    query = sp.translate(source='aag 0 0 0 0 0\n', language='aiger',
                         profile='bmc', options={'bmc_depth': '3'})
    assert not query.ok


def test_circuit_module_preserves_all_latches_inputs_and_uninitialised_reset():
    result = imported('aag 3 1 2 0 0\n2\n4 3\n6 4 6\n', 'aiger')
    state = result.systems[0]
    assert len(state['variables']) == 3 and state['bad_count'] == 0
    i, a, b, ip, ap, bp = z3.Bools('v1@0 v2@0 v3@0 v1@1 v2@1 v3@1')
    equivalent(result.relation_smt2(0, 'init'), z3.Not(a))
    equivalent(result.relation_smt2(0, 'trans'), z3.And(ap == z3.Not(i), bp == a))
    equivalent(result.relation_smt2(0, 'invariant'), z3.BoolVal(True))


def test_moxi_relations_are_separate_and_subsystem_locals_are_fresh():
    result = imported('''
      (define-system C :output ((x Bool)) :local ((l Bool))
        :init (= x l) :trans (= l' (not l)))
      (define-system P :output ((a Bool) (b Bool))
        :subsys (one (C a)) :subsys (two (C b)))''', 'moxi')
    parent = result.systems[1]
    locals_ = [v for v in parent['variables'] if v['role'] == 'local']
    assert len(locals_) == 2 and locals_[0]['current'] != locals_[1]['current']
    a, b = z3.Bools('a b')
    l, r = [z3.Bool(v['current'].strip('|')) for v in locals_]
    lp, rp = [z3.Bool(v['next'].strip('|')) for v in locals_]
    equivalent(result.relation_smt2(1, 'init'), z3.And(a == l, b == r))
    equivalent(result.relation_smt2(1, 'trans'), z3.And(lp == z3.Not(l), rp == z3.Not(r)))


def test_moxi_redefinitions_do_not_rebind_existing_instances():
    result = imported('''
      (define-system C :output ((x Bool)) :init x)
      (define-system P :output ((y Bool)) :subsys (one (C y)))
      (define-system C :output ((x Bool)) :init (not x))
      (define-system Q :output ((z Bool)) :subsys (two (C z)))''', 'moxi')
    assert [s['name'] for s in result.systems] == ['C', 'P', 'C', 'Q']
    equivalent(result.relation_smt2(1, 'init'), z3.Bool('y'))
    equivalent(result.relation_smt2(3, 'init'), z3.Not(z3.Bool('z')))


def test_function_let_values_substitute_each_calls_actual_arguments():
    result = imported('''
      (define-fun f ((x Int) (y Int)) Int
        (let ((u (* x y))) (let ((v (+ u x))) (+ v u))))
      (define-system S :input ((a Int) (b Int)) :output ((c Int) (d Int))
        :init (and (= c (f a b)) (= d (f b a))))''', 'moxi')
    a, b, c, d = z3.Ints('a b c d')
    equivalent(result.relation_smt2(0, 'init'), z3.And(c == 2*a*b+a, d == 2*a*b+b))


@pytest.mark.parametrize('source', [
    '(define-system Good :output ((x Bool))) (define-system Bad :init unknown)',
    '(define-system S :output ((x Bool)) :trans (+ x 1))',
    '(define-system S :output ((x Bool)) :init x\')',
    '(define-system S :subsys (i (Undefined)))',
    '(define-system S) (check-system S :query (q ()))',
])
def test_invalid_or_query_bearing_library_does_not_import(source):
    result = sp.import_module(source=source, language='moxi')
    assert not result.ok and not result.systems
    assert all(d.code != sp.ErrorCode.E_INTERNAL for d in result.diagnostics)


@pytest.mark.parametrize('stem', [
    'QF_LIA_LightStatusModified', 'QF_LIA_SmallSystems',
    'QF_LRA_LightStatusModified', 'QF_LRA_SmallSystems',
    'QF_NIA_Silly', 'QF_NRA_Silly1', 'QF_NRA_Silly2',
])
def test_original_query_free_libraries_import(stem):
    result = sp.import_module(str(ROOT / 'languages/moxi/instances/upstream' / (stem + '.moxi')))
    assert result.ok, [d.message for d in result.diagnostics]
    assert result.systems and not result.unresolved
    for index, _ in enumerate(result.systems):
        for part in ['init', 'trans', 'invariant']:
            assert result.relation_smt2(index, part)


def test_malformed_datatype_is_not_reported_only_as_missing_query():
    path = ROOT / 'languages/moxi/instances/upstream/QF_LRA_LossyIntChannelX.moxi'
    result = sp.import_module(str(path))
    assert not result.ok
    assert any(d.code == sp.ErrorCode.E_PARSE for d in result.diagnostics)
    query = sp.translate(str(path), language='moxi', profile='bmc', options={'bmc_depth': '3'})
    assert not query.ok
    assert any(d.code == sp.ErrorCode.E_PARSE for d in query.diagnostic_items)


def test_external_calls_preserve_constraints_types_and_annotation_punctuation():
    source = '''predicate opaque(array [int] of var int: xs,int: c);
      var 1..5: x;
      constraint int_le(x,3);
      constraint opaque([x,2],4):: blackbox_exec("a%;b,().py",[]);
      solve minimize x;'''
    result = imported(source, 'flatzinc')
    calls = result.unresolved
    assert len(calls) == 1 and calls[0]['predicate'] == 'opaque'
    assert calls[0]['annotations'] == ':: blackbox_exec("a%;b,().py",[])'
    assert [a['array'] for a in calls[0]['arguments']] == [True, False]
    assert [v['name'] for v in calls[0]['arguments'][0]['values']] == ['x', '2']
    partial = result.known_constraints_smt2()
    equivalent(partial, z3.And(z3.Int('x') >= 1, z3.Int('x') <= 3))
    assert '(minimize x)' in partial
    assert '(check-sat)' not in partial
    assert not sp.translate(source=source, language='flatzinc').ok
    calls.clear()
    assert len(result.unresolved) == 1  # snapshot mutation cannot close the model


@pytest.mark.parametrize('source', [
    'predicate p(int: x); var int: x; constraint p(x); solve satisfy;',
    'predicate p(var bool: x); var int: x; constraint p(x); solve satisfy;',
    'predicate p(var int: x); constraint p(1,2); solve satisfy;',
    'var int: x; constraint p(x); solve satisfy;',
    'predicate p(var int: x); constraint p(missing); solve satisfy;',
    'predicate p(var int: x); constraint p(1)::blackbox_exec("bad,[]); solve satisfy;',
    'predicate p(var int: x = true); constraint p(1); solve satisfy;',
    'predicate p bad(var int: x); constraint p bad(1); solve satisfy;',
    'predicate p(var int: x bad); constraint p(1); solve satisfy;',
    'predicate p(int: x,var int: y,var int: z); predicate p(var int: x,int: y,int: z); '
    'constraint p(1,2,3); solve satisfy;',
    'predicate p(array [int] of int: a); array [1..1] of var int: a=[1]; '
    'constraint p(a); solve satisfy;',
    'predicate p(array [int] of int: a); array [1..0] of float: a=[]; '
    'constraint p(a); solve satisfy;',
])
def test_unresolved_does_not_mean_unvalidated(source):
    result = sp.import_module(source=source, language='flatzinc')
    assert not result.ok and not result.unresolved
    assert all(d.code != sp.ErrorCode.E_INTERNAL for d in result.diagnostics)


def test_empty_external_array_keeps_its_declared_type_during_overload_selection():
    result = imported('''predicate p(array [int] of int: a);
      predicate p(array [int] of float: a);
      array [1..0] of float: a=[];
      constraint p(a); solve satisfy;''', 'flatzinc')
    argument = result.unresolved[0]['arguments'][0]
    assert argument['sort'] == 'Real' and argument['array'] and not argument['values']


@pytest.mark.parametrize('stem,count', [
    ('blackbox_bounds_default', 1), ('blackbox_bounds_reason', 1),
    ('blackbox_multi_list', 1), ('blackbox_value_exec', 1),
    ('blackbox_value_fn_dll', 1), ('named_args_default_flatzinc', 1),
    ('most_specific_reif', 3),
])
def test_original_external_models_preserve_all_calls(stem, count):
    path = ROOT / 'languages/flatzinc/instances/upstream' / (stem + '.fzn')
    result = sp.import_module(str(path))
    assert result.ok, [d.message for d in result.diagnostics]
    assert len(result.unresolved) == count
    # Independent source-level oracle for these flat compiler fixtures: every
    # call argument is a scalar or a declared flat array of scalars. Compare
    # all values, not just predicate names/counts (a dropped coefficient would
    # otherwise look like successful dependency reporting).
    arrays = {}
    for line in path.read_text().splitlines():
        match = re.match(r'^array .*?:\s*(\w+).*?=\s*\[([^\]]*)\];$', line)
        if match:
            arrays[match[1]] = [v.strip() for v in match[2].split(',') if v.strip()]
    expected_arguments = []
    names = {call['predicate'] for call in result.unresolved}
    for line in path.read_text().splitlines():
        match = re.match(r'^constraint (\w+)\(([^()]*)\)', line)
        if match and match[1] in names:
            args = [value.strip() for value in match[2].split(',')]
            expected_arguments.append([[] if value == '[]' else arrays.get(value, [value]) for value in args])
    actual_arguments = [[[value['name'] if value['name'] else str(value['bool_value']).lower()
                          for value in arg['values']] for arg in call['arguments']]
                        for call in result.unresolved]
    assert actual_arguments == expected_arguments
    assert not sp.translate(str(path), language='flatzinc').ok
    if stem == 'most_specific_reif':
        assert [c['predicate'] for c in result.unresolved] == ['my_pred_reif', 'my_pred_imp', 'my_pred_reif']
        assert result.unresolved[0]['arguments'][1]['parameter']
        assert not result.unresolved[2]['arguments'][1]['parameter']


@pytest.mark.parametrize('stem,integers,reals', [
    ('blackbox_bounds_default', ['X_INTRODUCED_16_', 'X_INTRODUCED_17_'], []),
    ('blackbox_bounds_reason', ['X_INTRODUCED_16_', 'X_INTRODUCED_17_'], []),
    ('blackbox_multi_list', ['X_INTRODUCED_17_', 'X_INTRODUCED_18_'],
     ['X_INTRODUCED_19_', 'X_INTRODUCED_20_']),
    ('blackbox_value_exec', ['X_INTRODUCED_17_', 'X_INTRODUCED_18_', 'X_INTRODUCED_19_'], []),
    ('blackbox_value_fn_dll', ['X_INTRODUCED_17_', 'X_INTRODUCED_18_', 'X_INTRODUCED_19_'], []),
])
def test_original_blackbox_known_part_matches_source_domains(stem, integers, reals):
    path = ROOT / 'languages/flatzinc/instances/upstream' / (stem + '.fzn')
    module = sp.import_module(str(path))
    assert module.ok
    expected = z3.And(*[bound for name in integers for bound in (z3.Int(name) >= 1, z3.Int(name) <= 10)],
                      *[bound for name in reals for bound in (z3.Real(name) >= 0, z3.Real(name) <= 1)])
    equivalent(module.known_constraints_smt2(), expected)


def test_original_foo_and_reification_known_constraints_are_not_dropped():
    directory = ROOT / 'languages/flatzinc/instances/upstream'
    foo = sp.import_module(str(directory / 'named_args_default_flatzinc.fzn'))
    equivalent(foo.known_constraints_smt2(), z3.And(z3.Int('a') >= 0, z3.Int('a') <= 10))
    reif = sp.import_module(str(directory / 'most_specific_reif.fzn'))
    b, c0, c1, c2 = z3.Bools('b X_INTRODUCED_0_ X_INTRODUCED_1_ X_INTRODUCED_2_')
    equivalent(reif.known_constraints_smt2(),
               z3.And(z3.Int('x') >= 1, z3.Int('x') <= 10, z3.Or(b,c0), z3.Or(b,c1), b == z3.Not(c2)))
