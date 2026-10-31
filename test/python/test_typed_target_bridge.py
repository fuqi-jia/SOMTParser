import pytest
from tools.semantic_checks.typed_target_bridge import check


def script(declarations, formula='true', objectives=''):
    return ('(set-logic ALL)\n' + declarations + '\n(assert ' + formula + ')\n' +
            objectives + '\n(check-sat)\n(exit)\n').encode()


@pytest.mark.parametrize('sort,value', [('Int', '4'), ('Real', '(/ 3.0 2.0)'), ('Bool', 'true'),
                                      ('(Array Int Bool)', '((as const (Array Int Bool)) false)')])
def test_typed_private_witness_full_relation(sort, value):
    public = '(declare-const x ' + sort + ')'
    old = script(public, '(exists ((w ' + sort + ')) (and (= w x) (= w ' + value + ')))')
    new = script(public + '(declare-const !somt_exists_0 ' + sort + ')',
                 '(and (= !somt_exists_0 x) (= !somt_exists_0 ' + value + '))')
    result = check(old, new)
    assert result['full_relation_bridge'], result
    assert result['solver_queries'] == 0
    changed = script(public + '(declare-const !somt_exists_0 ' + sort + ')',
                     '(and (= !somt_exists_0 x) (not (= !somt_exists_0 ' + value + ')))')
    assert not check(old, changed)['full_relation_bridge']


def test_original_prefix_symbol_remains_public():
    old = script('(declare-const !somt_exists_0 Int)', '(= !somt_exists_0 3)')
    assert not check(old, script('(declare-const !somt_exists_0 Int)', '(= !somt_exists_0 4)'))['full_relation_bridge']
    assert not check(old, script(''))['full_relation_bridge']


@pytest.mark.parametrize('replacement', [
    '(minimize (- x))(maximize y)', '(maximize x)(maximize y)',
    '(maximize y)(minimize x)', '(minimize x)', '(minimize x)(maximize (+ y 1))',
])
def test_all_ordered_objectives_retained(replacement):
    declarations = '(declare-const x Int)(declare-const y Int)'
    old = script(declarations, '(and (<= 0 x) (<= 0 y))', '(minimize x)(maximize y)')
    assert check(old, old)['full_relation_bridge']
    assert not check(old, script(declarations, '(and (<= 0 x) (<= 0 y))', replacement))['full_relation_bridge']


def test_private_witness_in_cost_is_bound_with_constraints():
    old = script('(declare-const x Int)', '(<= 0 x)', '(minimize x)')
    changed = script('(declare-const x Int)(declare-const !somt_exists_0 Int)',
                     '(<= 0 x)', '(minimize !somt_exists_0)')
    assert not check(old, changed)['full_relation_bridge']


def test_let_inlining_and_conjunct_permutation():
    decls = '(declare-const x Int)(declare-const y Int)'
    old = script(decls, '(let ((a (<= x y))) (and a (or a (= x 0))))', '(maximize (+ x y))')
    new = script(decls, '(and (or (= x 0) (>= y x)) (<= x y))', '(maximize (+ y x))')
    assert check(old, new)['full_relation_bridge']


@pytest.mark.parametrize('declarations', ['', '(declare-const x Bool)',
                                         '(declare-const x Int)(declare-const helper Int)'])
def test_no_public_coordinate_loss_retyping_or_unmarked_private(declarations):
    assert not check(script('(declare-const x Int)'), script(declarations))['full_relation_bridge']


@pytest.mark.parametrize('tail', ['(assert false)', '(check-sat)', '(push 1)', 'garbage'])
def test_no_unchecked_suffix(tail):
    good = script('(declare-const x Int)', '(= x 1)')
    assert not check(good, good + tail.encode())['full_relation_bridge']


@pytest.mark.parametrize('command', ['(set-option :opt.priority pareto)', '(push 1)', '(reset)',
                                    '(assert-soft true)', '(check-sat-assuming ())'])
def test_semantic_commands_refused(command):
    good = script('(declare-const x Int)', '(= x 1)')
    changed = good.replace(b'(check-sat)', command.encode() + b'\n(check-sat)')
    assert not check(good, changed)['full_relation_bridge']


@pytest.mark.parametrize('context', ['(not (exists ((w Int)) (= w x)))',
                                    '(forall ((w Int)) (= w x))',
                                    '(or p (exists ((w Int)) (< w x)))'])
def test_binders_not_moved_out_of_other_contexts(context):
    decls = '(declare-const x Int)(declare-const p Bool)'
    changed = script(decls + '(declare-const !somt_exists_0 Int)', '(= !somt_exists_0 x)')
    assert not check(script(decls, context), changed)['full_relation_bridge']


def test_late_assertion_and_missing_exit_refused():
    good = script('(declare-const x Int)', '(= x 1)')
    assert not check(good, good.replace(b'(exit)', b'(assert false)(exit)'))['full_relation_bridge']
    assert not check(good, good.replace(b'(exit)', b''))['full_relation_bridge']


def test_no_forward_scope_forgery():
    good = script('(declare-const x Int)', '(= x 1)')
    bad = b'(set-logic ALL)(assert (= x 1))(declare-const x Int)(check-sat)(exit)'
    assert not check(good, bad)['full_relation_bridge']


@pytest.mark.parametrize('direction', ['minimize', 'maximize'])
def test_solver_obligations_cover_whole_domain_and_signed_cost(direction):
    decls = '(declare-const x Int)'
    old = script(decls, '(and (<= 0 x) (<= x 1))', '(' + direction + ' x)')
    new = script(decls, '(or (= x 0) (= x 1))', '(' + direction + ' x)')
    captured = []
    result = check(old, new, solve=True, complete_relation_callback=lambda a,b:captured.append((a,b)))
    assert result['full_relation_bridge'] and result['solver_queries'] > 0, result
    assert len(captured) == 1
    import z3
    solver=z3.Solver();solver.add(z3.Xor(*captured[0]));assert solver.check()==z3.unsat
    changed=script(decls, '(or (= x 0) (= x 2))', '(' + direction + ' x)')
    assert not check(old, changed, solve=True)['full_relation_bridge']


def test_unknown_and_archive_callback_cannot_supply_a_proof(monkeypatch):
    import z3
    decls='(declare-const x Int)'
    old=script(decls, '(and (<= 0 x) (<= x 1))')
    new=script(decls, '(or (= x 0) (= x 1))')
    monkeypatch.setattr(type(z3.Solver()), 'check', lambda self:z3.unknown)
    result=check(old,new,solve=True,complete_relation_callback=lambda a,b:dict(equivalent=True))
    assert not result['full_relation_bridge']
    assert result['solver_queries'] > 0


def test_integer_step_bridge_includes_unbounded_before_event_region():
    decls='(declare-const a Int)(declare-const h Int)(declare-const cap Int)'
    load='(ite (and (<= a t) (< t (+ a 2))) h 0)'
    old=script(decls,'(forall ((t Int)) (<= '+load+' cap))')
    new=script(decls,'(and (<= 0 cap) (<= h cap))')
    result=check(old,new,solve=True)
    assert result['full_relation_bridge'],result
    assert result['proof']['body_certificate']['integer_step_expansion'][0]['expanded_quantifiers']==1
    # Sampling only at start would miss the required outside-region bound.
    assert not check(old,script(decls,'(<= h cap)'),solve=True)['full_relation_bridge']


def test_optimization_mutation_stays_unproved_with_solver_enabled():
    decls='(declare-const x Int)(declare-const y Int)'
    old=script(decls,'(and (<= 0 x) (<= x 1) (<= 0 y) (<= y 1))','(minimize x)(maximize y)')
    for obj in ['(minimize x)(maximize (- y))','(minimize y)(maximize x)']:
        assert not check(old,script(decls,'(and (<= 0 x) (<= x 1) (<= 0 y) (<= y 1))',obj),solve=True)['full_relation_bridge']


@pytest.mark.parametrize('direction', ['minimize', 'maximize'])
def test_multidimensional_finite_generator_and_ordered_cost(direction):
    decls='(declare-const a (Array Int Int))'
    guard='(and (<= 0 i) (< i 2) (<= 0 j) (< j 3))'
    old=script(decls,'(forall ((i Int)(j Int)) (=> '+guard+' (= (select a (+ (* i 3) j)) (+ i j))))','('+direction+' (select a 5))')
    entries=['(= (select a '+str(3*i+j)+') '+str(i+j)+')' for i in range(2) for j in range(3)]
    new=script(decls,'(and '+' '.join(entries)+')','('+direction+' (select a 5))')
    result=check(old,new,solve=True)
    assert result['full_relation_bridge'],result
    stats=result['proof']['body_certificate']['finite_guard_expansion'][0]
    assert stats['expanded_quantifiers']==1 and stats['enumerated_tuples']==6
    changed=script(decls,'(and '+' '.join(entries[:-1]+['(= (select a 5) 99)'])+')','('+direction+' (select a 5))')
    assert not check(old,changed,solve=True)['full_relation_bridge']


def test_unbounded_array_generator_is_never_truncated():
    decls='(declare-const a (Array Int Int))'
    old=script(decls,'(forall ((i Int)) (=> (<= 0 i) (= (select a i) 0)))')
    new=script(decls,'(and (= (select a 0) 0)(= (select a 1) 0))')
    result=check(old,new,solve=True)
    assert not result['full_relation_bridge']


@pytest.mark.parametrize('wrong', [False, True])
def test_public_incidence_bridge_reorders_private_witnesses(wrong):
    decls='(declare-const x Int)(declare-const y Int)'
    old=script(decls, '(and (exists ((a Int)) (and (<= 0 a)(<= a 2)(= x (* a a)))) (exists ((b Int)) (and (<= 1 b)(<= b 3)(= y (* b b)))))', '(minimize (+ x (* 2 y)))')
    new=script(decls+'(declare-const !somt_exists_0 Int)(declare-const !somt_exists_1 Int)', '(and (<= 1 !somt_exists_0)(<= !somt_exists_0 3)(= y (* !somt_exists_0 !somt_exists_0))(<= 0 !somt_exists_1)(<= !somt_exists_1 2)(= x (* !somt_exists_1 !somt_exists_1)))', '(minimize (+ x (* '+('3' if wrong else '2')+' y)))')
    result=check(old,new,solve=True,witness_strategy='public-incidence')
    assert result['full_relation_bridge'] is (not wrong), result


def test_invalid_witness_strategy_rejected():
    good=script('(declare-const x Int)', '(= x 1)')
    with pytest.raises(ValueError):
        check(good,good,witness_strategy='unproved')
