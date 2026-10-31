"""Query-free exports checked by an independent SMT implementation."""
import json
import re
from pathlib import Path

import pytest
import z3
import somtparser as sp

ROOT = Path(__file__).resolve().parents[2]


def exported(source=None, language=None, path=None):
    module = sp.import_module(str(path) if path else '', source=source or '', language=language or '')
    assert module.ok, [d.message for d in module.diagnostics]
    text = module.to_smt2()
    interface = json.loads(text.splitlines()[0].removeprefix('; SOMT module interface '))
    assert not re.search(r'^\s*\((check-sat|exit)\b', text, re.M)
    assert interface['query'] is False
    return text, interface


def relation(text, interface, index, label):
    system = interface['systems'][index]
    declarations = '\n'.join(f"(declare-const {p['symbol']} {p['sort']})" for p in system['parameters'])
    symbol = system['relations'][label]
    args = ' '.join(p['symbol'] for p in system['parameters'])
    call = f'({symbol} {args})' if args else symbol
    return z3.And(*z3.parse_smt2_string(text + declarations + f'\n(assert {call})'))


def equivalent(actual, expected):
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(actual != expected)
    assert solver.check() == z3.unsat


def test_library_definitions_are_separate_callable_functions():
    text, meta = exported('''(declare-const c Int)
      (declare-fun rigid (Int) Int)
      (define-system S :output ((x Int)) :init (= x c) :trans (= x' (rigid x)))
      (define-system S :output ((x Bool)) :init x :trans (= x' (not x)))''', 'moxi')
    assert len(meta['systems']) == 2
    assert len({s['relations']['init'] for s in meta['systems']}) == 2
    assert len(z3.parse_smt2_string(text)) == 0  # no chosen relation asserted
    x, xp, c = z3.Ints("x x.moxi.next c")
    rigid = z3.Function('rigid', z3.IntSort(), z3.IntSort())
    equivalent(relation(text, meta, 0, 'init'), x == c)
    equivalent(relation(text, meta, 0, 'trans'), xp == rigid(x))
    equivalent(relation(text, meta, 1, 'init'), z3.Bool('x'))
    equivalent(relation(text, meta, 1, 'trans'), z3.Bool("x.moxi.next") == z3.Not(z3.Bool('x')))


def test_circuit_exports_reset_transition_outputs_and_bad():
    text, meta = exported('aag 2 1 1 1 0 1\n2\n4 3\n4\n5\n', 'aiger')
    i, x, xp = z3.Bools('v1@0 v2@0 v2@1')
    equivalent(relation(text, meta, 0, 'init'), z3.Not(x))
    equivalent(relation(text, meta, 0, 'trans'), xp == z3.Not(i))
    equivalent(relation(text, meta, 0, 'output.0'), x)
    equivalent(relation(text, meta, 0, 'bad.0'), z3.Not(x))


def test_open_scalar_retains_call_domains_objective_and_linkage():
    text, meta = exported('''predicate foo(var int: x, int: k);
      var 1..5: x; constraint int_le(x,3);
      constraint foo(x,2)::blackbox_exec("a%;b.py",[]); solve minimize x;''', 'flatzinc')
    symbol = meta['imports'][0]['symbol']
    assert meta['imports'][0]['predicate'] == 'foo'
    assert 'a%;b.py' in meta['imports'][0]['annotations']
    assert meta['objective_count'] == 1 and '(minimize x)' in text
    x = z3.Int('x')
    function = z3.Function(symbol, z3.IntSort(), z3.IntSort(), z3.BoolSort())
    equivalent(z3.And(*z3.parse_smt2_string(text)), z3.And(x >= 1, x <= 3, function(x, 2)))
    optimizer = z3.Optimize()
    optimizer.from_string(text)
    assert len(optimizer.objectives()) == 1


def test_array_encoding_is_injective_and_shared_across_lengths():
    text, meta = exported('''predicate p(array [int] of var int: a);
      var 1..2: x;
      constraint p([]); constraint p([1]); constraint p([x,2]);
      constraint p([2,x]); constraint p([x,2]); solve satisfy;''', 'flatzinc')
    assert len(meta['imports']) == 1 and len(meta['calls']) == 5
    enc = meta['array_encodings'][0]
    p = meta['imports'][0]['symbol']
    nil, cons = enc['nil'], enc['cons']
    # With x=1, [1,1] differs from [], [1], [1,2], and [2,1].
    solver = z3.Solver()
    solver.from_string(text + f'\n(assert (= x 1))\n(assert (not ({p} ({cons} 1 ({cons} 1 {nil})))))')
    assert solver.check() == z3.sat
    solver = z3.Solver()
    solver.from_string(text + f'\n(assert (= x 1))\n(assert (not ({p} ({cons} 1 ({cons} 2 {nil})))))')
    assert solver.check() == z3.unsat  # original call must actually be present


def test_callbacks_and_overloads_have_distinct_linkage():
    text, meta = exported('''predicate p(var int: x); predicate p(int: x);
      var int: x; constraint p(x); constraint p(1);
      constraint p(x)::blackbox_exec("first.py",[]);
      constraint p(x)::blackbox_exec("second.py",[]); solve satisfy;''', 'flatzinc')
    assert len(meta['imports']) == 4
    assert len({c['symbol'] for c in meta['calls']}) == 4
    z3.parse_smt2_string(text)


def test_export_names_do_not_capture_source_globals():
    text, meta = exported('''(declare-const |somt.module.system.0.init| Bool)
      (define-system S :output ((x Bool)) :init (= x |somt.module.system.0.init|))''', 'moxi')
    assert meta['systems'][0]['relations']['init'] != 'somt.module.system.0.init'
    equivalent(relation(text, meta, 0, 'init'), z3.Bool('x') == z3.Bool('somt.module.system.0.init'))


@pytest.mark.parametrize('language,stem', [
    ('aiger', 'empty.aag'),
    *[('moxi', s + '.moxi') for s in [
        'QF_LIA_LightStatusModified', 'QF_LIA_SmallSystems',
        'QF_LRA_LightStatusModified', 'QF_LRA_SmallSystems',
        'QF_NIA_Silly', 'QF_NRA_Silly1', 'QF_NRA_Silly2']],
    *[('flatzinc', s + '.fzn') for s in [
        'blackbox_bounds_default', 'blackbox_bounds_reason', 'blackbox_multi_list',
        'blackbox_value_exec', 'blackbox_value_fn_dll', 'most_specific_reif', 'named_args_default_flatzinc']],
])
def test_every_original_module_exports(language, stem):
    text, meta = exported(path=ROOT / 'languages' / language / 'instances/upstream' / stem)
    z3.parse_smt2_string(text)
    if language == 'flatzinc':
        assert meta['imports'] and meta['calls']
    else:
        assert meta['systems']
