"""Closed helper sharing preserves every scope and the full replayable definition."""
import pytest
import z3
from tools.semantic_checks.closed_helpers import retain_closed_helpers
from tools.semantic_checks.source_oracles.xcsp_source import Source
from tools.semantic_checks.source_oracles.xcsp_relation import target_model, compare


def parsed(module):
    data, binding = retain_closed_helpers(module.encode())
    target = z3.Optimize(); target.from_string(data.decode())
    return target, binding, data


def equivalent(a, b):
    solver = z3.Solver(); solver.add(z3.Xor(a, b)); assert solver.check() == z3.unsat


@pytest.mark.parametrize('body,expected', [
    ('(> a 4)', lambda x: x > 4),
    ('(let ((v (+ a 1))) (> v 5))', lambda x: x > 4),
    ('(let ((a (+ a 2))) (= a 5))', lambda x: x == 3),
    ('(let ((a 2) (v a)) (= v a))', lambda x: x == 2),
    ('(or (= a (- 123456789012345678901234567890)) (= a 2))',
     lambda x: z3.Or(x == -123456789012345678901234567890, x == 2)),
    ('(forall ((v Int)) (>= (+ v a) v))', lambda x: x >= 0),
])
def test_closed_complete_body_and_roundtrip(body, expected):
    original = '(declare-const x Int)(define-fun-rec f ((a Int)) Bool '+body+')(assert (f x))'
    target, binding, data = parsed(original)
    assert len(binding['shared']) == 1
    x = z3.Int('x'); equivalent(target.assertions()[0], expected(x))
    solver = z3.Solver(); solver.add(z3.Xor(target.assertions()[0], expected(x)))
    text = solver.to_smt2()
    assert 'define-funs-rec' in text or 'define-fun-rec' in text
    ctx = z3.Context(); replay = z3.Solver(ctx=ctx); replay.from_string(text)
    assert replay.check() == z3.unsat
    assert b'define-fun-rec' in data


def test_same_context_repeated_name_different_bodies_cannot_change_earlier_formula():
    x = z3.Int('x'); earlier = []; names = set()
    for i in range(12):
        target, binding, _ = parsed('(declare-const x Int)(define-fun-rec f ((a Int)) Bool (> a '+str(i)+'))(assert (f x))')
        name = binding['shared'][0]['fresh']; assert name not in names; names.add(name)
        earlier.append((target.assertions()[0], x > i))
    for actual, wanted in earlier: equivalent(actual, wanted)


@pytest.mark.parametrize('name', ['f', '|helper with spaces|', '|helper;bar|'])
def test_complete_symbol_rename_keeps_strings_and_similar_names(name):
    original = ('(set-info :source "f |helper with spaces| with ""quotes""")'
                '(declare-const x Int)(declare-const f_suffix Int)'
                '(define-fun-rec '+name+' ((a Int)) Bool (> a 4))'
                '(assert (and ('+name+' x) (= f_suffix 7)))')
    target, binding, data = parsed(original)
    assert b'"f |helper with spaces| with ""quotes"""' in data
    assert b'f_suffix' in data
    equivalent(target.assertions()[0], z3.And(z3.Int('x') > 4, z3.Int('f_suffix') == 7))


def test_shadowed_helper_name_is_renamed_at_binder_and_uses_together():
    target, binding, _ = parsed('(declare-const x Int)'
        '(define-fun-rec f ((a Int)) Bool (> a 4))'
        '(define-fun-rec g ((f Int)) Bool (< f 2))'
        '(assert (or (f x) (g x)))')
    assert len(binding['shared']) == 2
    equivalent(target.assertions()[0], z3.Or(z3.Int('x') > 4, z3.Int('x') < 2))


@pytest.mark.parametrize('body', ['(> g a)', '(let ((v g)) (> v a))',
                                  '(let ((g a) (v g)) (> v 0))'])
def test_captured_globals_use_macro_expansion_before_existential_projection(body):
    target, binding, _ = parsed('(declare-const g Int)(declare-const x Int)'
        '(define-fun-rec f ((a Int)) Bool '+body+')(assert (f x))')
    assert binding['shared'] == []
    g, x = z3.Ints('g x')
    projected = z3.Exists([g], target.assertions()[0])
    equivalent(projected, z3.BoolVal(True))


def test_local_shadow_is_closed_even_if_same_name_is_also_declared_globally():
    target, binding, _ = parsed('(declare-const g Int)(declare-const x Int)'
        '(define-fun-rec f ((a Int)) Bool (let ((g a)) (> g 0)))(assert (f x))')
    assert len(binding['shared']) == 1
    equivalent(target.assertions()[0], z3.Int('x') > 0)


def test_dependent_helper_falls_back_without_capturing_global():
    target, binding, _ = parsed('(declare-const x Int)'
        '(define-fun-rec f ((a Int)) Bool (> a 4))'
        '(define-fun-rec g ((a Int)) Bool (and (f a) (< a 9)))'
        '(assert (g x))')
    assert [row['original'] for row in binding['shared']] == ['f']
    equivalent(target.assertions()[0], z3.And(z3.Int('x') > 4, z3.Int('x') < 9))


@pytest.mark.parametrize('definition', [
    '(define-fun-rec f ((a Int)) Bool (f a))',
    '(define-fun-rec f ((f Int)) Bool (> f 0))',
    '(define-fun-rec f ((a Int)) Bool (> a 0))(define-fun-rec f ((a Int)) Bool (< a 0))',
])
def test_unsupported_recursive_or_duplicate_definitions_are_not_weakened(definition):
    with pytest.raises(ValueError):retain_closed_helpers(definition.encode())


def test_real_parameters_keep_existing_exact_expansion():
    target, binding, _ = parsed('(declare-const x Real)(define-fun-rec f ((a Real)) Bool (> a (/ 1 3)))(assert (f x))')
    assert binding['shared'] == []
    equivalent(target.assertions()[0], z3.Real('x') > z3.RealVal('1/3'))


@pytest.mark.parametrize('polarity', [False, True])
def test_every_scope_kept_and_omission_has_a_counterexample(polarity):
    clauses = ['(f x y)', '(f y z)', '(f z x)']
    if polarity:clauses = ['(not '+term+')' for term in clauses]
    prefix = '(declare-const x Int)(declare-const y Int)(declare-const z Int)(define-fun-rec f ((a Int)(b Int)) Bool (< a b))'
    # Use two independent scopes: a cycle of < would be vacuously false.
    clauses = clauses[:2]
    full, binding, _ = parsed(prefix+''.join('(assert '+term+')' for term in clauses))
    x,y,z=z3.Ints('x y z'); expected=[x<y,y<z]
    if polarity:expected=[z3.Not(term) for term in expected]
    equivalent(z3.And(*full.assertions()),z3.And(*expected))
    for index in range(2):
        missing, _, _ = parsed(prefix+'(assert '+clauses[1-index]+')')
        solver=z3.Solver();solver.add(z3.Xor(z3.And(*full.assertions()),z3.And(*missing.assertions())))
        assert solver.check()==z3.sat


def test_changed_body_and_argument_order_have_counterexamples():
    a, _, _=parsed('(declare-const x Int)(declare-const y Int)(define-fun-rec f ((a Int)(b Int)) Bool (< a b))(assert (f x y))')
    b, _, _=parsed('(declare-const x Int)(declare-const y Int)(define-fun-rec f ((a Int)(b Int)) Bool (< a b))(assert (f y x))')
    solver=z3.Solver();solver.add(z3.Xor(a.assertions()[0],b.assertions()[0]));assert solver.check()==z3.sat


def model(objectives=()):
    x=z3.Int('x')
    return Source({'x':x},{'x':((-10,10),)},[z3.And(x>=-10,x<=10),x>=0],list(objectives),1,'CSP')


@pytest.mark.parametrize('direction', ['minimize','maximize'])
def test_public_full_relation_signed_cost_and_complete_callback(direction):
    x=z3.Int('x');source=model([(direction,x+1)])
    data=('(declare-const x Int)(define-fun-rec eligible ((a Int)) Bool (>= a 0))'
          '(define-fun-rec cost ((a Int)) Int (+ a 1))'
          '(assert (and (>= x (- 10)) (<= x 10)))(assert (eligible x))'
          '('+direction+' (cost x))(check-sat)(exit)').encode()
    seen=[]
    def callback(a,b):
        solver=z3.Solver();solver.add(z3.Xor(a,b));text=solver.to_smt2();assert 'define-funs-rec' in text
        ctx=z3.Context();replay=z3.Solver(ctx=ctx);replay.from_string(text);assert replay.check()==z3.unsat
        seen.append(text)
    result=compare(source,data,solve=True,project_private_scalars=True,complete_relation_callback=callback)
    assert result['equivalent'] is True and result['signed_cost_equal'] is True and len(seen)==1
    assert len(result['closed_helpers']['shared'])==2


def test_target_reader_does_not_register_incomplete_module():
    with pytest.raises(ValueError):target_model(b'(define-fun-rec f ((a Int)) Bool (> a 0))(check-sat)',model())


def test_repeated_uuid_cannot_reuse_a_helper_name(monkeypatch):
    from types import SimpleNamespace
    from tools.semantic_checks import closed_helpers
    monkeypatch.setattr(closed_helpers.uuid, 'uuid4', lambda: SimpleNamespace(hex='repeated_uuid'))
    a, first, _ = parsed('(declare-const x Int)(define-fun-rec f ((a Int)) Bool (> a 4))(assert (f x))')
    b, second, _ = parsed('(declare-const x Int)(define-fun-rec f ((a Int)) Bool (< a 2))(assert (f x))')
    assert first['shared'][0]['fresh'] != second['shared'][0]['fresh']
    equivalent(a.assertions()[0], z3.Int('x') > 4)
    equivalent(b.assertions()[0], z3.Int('x') < 2)


def test_generated_name_collision_with_input_is_skipped(monkeypatch):
    from itertools import count
    from types import SimpleNamespace
    from tools.semantic_checks import closed_helpers
    monkeypatch.setattr(closed_helpers.uuid, 'uuid4', lambda: SimpleNamespace(hex='input_collision'))
    monkeypatch.setattr(closed_helpers, '_fresh_serial', count())
    target, binding, _ = parsed('(declare-const x Int)(declare-const __somt_oracle_closed_input_collision_0 Int)'
        '(define-fun-rec f ((a Int)) Bool (> a 4))'
        '(assert (and (f x) (= __somt_oracle_closed_input_collision_0 7)))')
    assert binding['shared'][0]['fresh'] != '__somt_oracle_closed_input_collision_0'
    equivalent(target.assertions()[0], z3.And(z3.Int('x') > 4, z3.Int('__somt_oracle_closed_input_collision_0') == 7))
