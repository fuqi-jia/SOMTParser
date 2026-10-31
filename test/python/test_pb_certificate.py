"""Independent positive and mutation controls for complete PB certificates."""
from io import BytesIO
import itertools
import pytest

from tools.semantic_checks.pb_certificate import CertificateError, verify_streams


def checked(source, target):
    return verify_streams(BytesIO(source.encode()), BytesIO(target.encode()))


def envelope(body, variables=('x1', 'x2')):
    return '(set-logic ALL)\n' + ''.join(
        f'(declare-fun {name} () Int)\n' for name in variables
    ) + ''.join(f'(assert (>= {name} 0))(assert (<= {name} 1))\n'
                for name in variables) + body + '\n(check-sat)(exit)'


@pytest.mark.parametrize('source,body', [
    ('+1 x1 +2 x2 >= 1;', '(assert (<= 1 (+ (* 2 x2) x1)))'),
    ('+1 x1 +2 x2 >= 1;', '(assert (>= (+ (to_real x1) (* 2.000 (to_real x2))) 1.0))'),
    ('min: +3 x1 -2 x2; +1 x1 +2 x2 >= 1;', '(assert (>= (+ x1 (* 2 x2)) 1))(minimize (+ (* 3.0 (to_real x1)) (* (- 2.0) (to_real x2))))'),
    ('+1 x1 +2 x2 = 1;', '(assert (= (+ (* 4 x2) (* 2 x1)) 2))'),
    ('+1 x1 +2 x2 != 1;', '(assert (not (= (+ x1 (* 2 x2)) 1)))'),
    ('+1 x1 +2 x2 > 1;', '(assert (>= (+ x1 (* 2 x2)) 2))'),
    ('+1 x1 +2 x2 < 1;', '(assert (<= (+ x1 (* 2 x2)) 0))'),
    ('+1 x1 +2 x2 <= 1;', '(assert (>= 1 (+ x1 (* 2 x2))))'),
    ('+1 x1 +2 x2 ≥ 1;', '(assert (>= (+ x1 (* 2 x2)) 1))'),
    ('+1 ~x1 +2 x2 >= 1;', '(assert (>= (+ (- 1 x1) (* 2 x2)) 1))'),
    ('+3 x1 ~x2 -2 x2 >= -1;', '(assert (>= (+ (* 3 x1) (* (- 3) x1 x2) (* (- 2) x2)) (- 1)))'),
    ('+3 x1 x1 +2 x2 >= 1;', '(assert (>= (+ (* 3 x1) (* 2 x2)) 1))'),
    ('+1 x1 ~x1 +2 x2 >= 1;', '(assert (>= (* 2 x2) 1))'),
    ('+1 x1 +2 x2 >= 1;', '(assert (let ((a (* 2 x2))) (>= (+ a x1) 1)))'),
    ('min: +3 x1 -2 x2; +1 x1 +2 x2 >= 1;', '(assert (>= (+ x1 (* 2 x2)) 1))(minimize (- (* 3 x1) (* 2 x2)))'),
    ('max: +3 x1 -2 x2; +1 x1 +2 x2 >= 1;', '(assert (>= (+ x1 (* 2 x2)) 1))(maximize (- (* 3 x1) (* 2 x2)))'),
    ('min: +999999999999999999999999999999999999 x1 -2 x2; +1 x1 +2 x2 >= 1;', '(assert (>= (+ x1 (* 2 x2)) 1))(minimize (+ (* 999999999999999999999999999999999999 x1) (* (- 2) x2)))'),
    ('soft:; [7] +1 x1 +2 x2 >= 1;', '(assert-soft (>= (+ x1 (* 2 x2)) 1) :weight 7)'),
    ('soft: 8; [7] +1 x1 +2 x2 >= 1;', '(assert-soft (>= (+ x1 (* 2 x2)) 1) :weight 7)'),
    ('soft:; [3] +1 x1 +2 x2 >= 1; [4] +1 x1 +2 x2 >= 1;', '(assert-soft (>= (+ x1 (* 2 x2)) 1) :weight 7)'),
    ('soft: 7; [7] +1 x1 +2 x2 >= 1;', '(assert (< (ite (>= (+ x1 (* 2 x2)) 1) 0 7) 7))(minimize (ite (>= (+ x1 (* 2 x2)) 1) 0 7))'),
])
def test_complete_positive_certificate(source, body):
    proof = checked(source, envelope(body))
    assert proof['status'] == 'verified'
    assert proof['complete_source'] and proof['complete_target']
    assert proof['solver_search_performed'] is False


BASE_SOURCE = 'min: +3 x1 -2 x2; +1 x1 +2 x2 >= 1;'
BASE_TARGET = envelope('(assert (>= (+ x1 (* 2 x2)) 1))(minimize (+ (* 3 x1) (* (- 2) x2)))')


@pytest.mark.parametrize('before,after', [
    ('(* 2 x2)', '(* 3 x2)'),
    ('(* 3 x1)', '(* 4 x1)'),
    ('(* 3 x1)', '(* 3.5 (to_real x1))'),
    ('(* (- 2) x2)', '(* 2 x2)'),
    ('minimize', 'maximize'),
    ('(<= x1 1)', '(<= x1 2)'),
    ('(>= x1 0)', '(>= x1 (- 1))'),
    ('(assert (>= x1 0))', ''),
    ('(assert (<= x2 1))', ''),
    ('(assert (>= (+ x1 (* 2 x2)) 1))', ''),
    ('(minimize (+ (* 3 x1) (* (- 2) x2)))', ''),
    ('(declare-fun x1 () Int)', '(declare-fun x1 () Real)'),
    ('(declare-fun x1 () Int)', ''),
    ('(exit)', '(exit)(assert false)'),
    ('(check-sat)', '(check-sat)(assert false)'),
    ('(check-sat)', '(assert (= x1 x2))(check-sat)'),
    ('(check-sat)', '(push 1)(check-sat)'),
    ('(exit)', '(exit))'),
    ('(exit)', '(exit) junk'),
    ('(exit)', '(exit'),
])
def test_mutations_never_receive_a_certificate(before, after):
    with pytest.raises(CertificateError):
        checked(BASE_SOURCE, BASE_TARGET.replace(before, after))


@pytest.mark.parametrize('body', [
    '(assert-soft (>= (+ x1 (* 2 x2)) 1) :weight 6)',
    '(assert-soft (>= (+ x1 (* 2 x2)) 2) :weight 7)',
    '(assert-soft (>= (+ x1 (* 2 x2)) 1) :weight 7)',  # Missing non-vacuous top.
    '(assert (<= (ite (>= (+ x1 (* 2 x2)) 1) 0 7) 7))(minimize (ite (>= (+ x1 (* 2 x2)) 1) 0 7))',
])
def test_wbo_weight_and_strict_threshold_controls(body):
    with pytest.raises(CertificateError):
        checked('soft: 7; [7] +1 x1 +2 x2 >= 1;', envelope(body))


def test_parallel_let_binding_scope():
    target = envelope('(assert (let ((a 1)) (let ((a 2) (b a)) (>= (+ x1 (* 2 x2)) b))))')
    assert checked('+1 x1 +2 x2 >= 1;', target)['status'] == 'verified'


def test_declarations_can_follow_prior_assertions_before_query():
    target = BASE_TARGET.replace('(set-logic ALL)', '(set-logic ALL)(assert true)')
    assert checked(BASE_SOURCE, target)['status'] == 'verified'
    with pytest.raises(CertificateError):
        checked(BASE_SOURCE, BASE_TARGET.replace('(check-sat)', '(check-sat)(declare-fun late () Int)'))


@pytest.mark.parametrize('objective', ['', '(minimize 0)'])
def test_all_soft_rows_at_the_strict_top_become_hard(objective):
    source = 'soft: 7; [7] +1 x1 +2 x2 >= 1;'
    target = envelope('(assert (>= (+ x1 (* 2 x2)) 1))' + objective)
    proof = checked(source, target)
    assert proof['threshold_implied_hardening']
    assert proof['objective_verified']


@pytest.mark.parametrize('body', [
    '(minimize 0)',  # Mandatory source row cannot be omitted.
    '(assert (>= (+ x1 (* 2 x2)) 1))(minimize 1)',
    '(assert (>= (+ x1 (* 2 x2)) 2))(minimize 0)',
])
def test_hardening_does_not_erase_a_required_row_or_change_cost(body):
    with pytest.raises(CertificateError):
        checked('soft: 7; [7] +1 x1 +2 x2 >= 1;', envelope(body))


def test_remaining_soft_cost_and_strict_top_are_preserved_exhaustively():
    import z3
    source = 'soft: 3; [5] +1 x1 >= 1; [2] +1 x2 >= 1; [2] +1 ~x1 +1 ~x2 >= 1;'
    cost = '(+ (ite (>= x2 1) 0 2) (ite (>= (+ (- 1 x1) (- 1 x2)) 1) 0 2))'
    body = '(assert (>= x1 1))(assert (< ' + cost + ' 3))(minimize ' + cost + ')'
    target = envelope(body)
    assert checked(source, target)['threshold_implied_hardening']
    opt = z3.Optimize()
    opt.from_string(target)
    for x1, x2 in itertools.product((0, 1), repeat=2):
        original_cost = 5*(x1 < 1) + 2*(x2 < 1) + 2*((1-x1)+(1-x2) < 1)
        solver = z3.Solver()
        solver.add(*opt.assertions(), z3.Int('x1') == x1, z3.Int('x2') == x2)
        assert (solver.check() == z3.sat) == (original_cost < 3)
        if original_cost < 3:
            assert solver.model().eval(opt.objectives()[0]).as_long() == original_cost
    for broken in [body.replace('(assert (< ' + cost + ' 3))', ''),
                   body.replace('(< ' + cost + ' 3)', '(<= ' + cost + ' 3)'),
                   body.replace('(assert (>= x1 1))', '')]:
        with pytest.raises(CertificateError):
            checked(source, envelope(broken))


def test_whole_input_hashes():
    import hashlib
    proof = checked(BASE_SOURCE, BASE_TARGET)
    assert proof['source_sha256'] == hashlib.sha256(BASE_SOURCE.encode()).hexdigest()
    assert proof['target_sha256'] == hashlib.sha256(BASE_TARGET.encode()).hexdigest()


def test_polynomial_simplification_cannot_supply_its_own_binary_domain():
    import z3
    source = 'min: +1 x; +1 x >= 0;'
    target = '''(set-logic ALL)(declare-fun x () Int)
        (assert (>= (* x x) 0))(assert (<= (* x x) 1))
        (minimize x)(check-sat)(exit)'''
    with pytest.raises(CertificateError, match='raw target Boolean domains'):
        checked(source, target)
    solver = z3.Solver()
    solver.add(z3.Int('x') * z3.Int('x') >= 0,
               z3.Int('x') * z3.Int('x') <= 1, z3.Int('x') == -1)
    assert solver.check() == z3.sat


def test_exhaustive_polynomial_control_against_independent_arithmetic():
    # Enumerate genuine source/target denotations, separately from the checker.
    import z3
    source = '+3 x1 ~x2 -2 x2 >= -1;'
    target = envelope('(assert (>= (+ (* 3 x1) (* (- 3) x1 x2) (* (- 2) x2)) (- 1)))')
    checked(source, target)
    assertions = z3.parse_smt2_string(target)
    for x1, x2 in itertools.product((0, 1), repeat=2):
        expected = 3*x1*(1-x2)-2*x2 >= -1
        actual = z3.simplify(z3.substitute(z3.And(*assertions),
            (z3.Int('x1'), z3.IntVal(x1)), (z3.Int('x2'), z3.IntVal(x2))))
        assert z3.is_true(actual) == expected


@pytest.mark.parametrize('source', [
    'min: +3 x1 -2 x2; +1 x1 +2 x2 >= 1;',
    '+3 x1 ~x2 -2 x2 >= -1;',
    'soft: 8; [7] +1 x1 +2 x2 >= 1;',
    'soft: 7; [7] +1 x1 +2 x2 >= 1;',
])
def test_real_native_export(tmp_path, source):
    import somtparser as sp
    source_path = tmp_path / 'input.opb'
    source_path.write_text(source)
    model = sp.translate(path=str(source_path), language='opb')
    assert model.ok, [str(x) for x in model.diagnostic_items]
    target_path = tmp_path / 'target.smt2'
    model.write_smt2(str(target_path), sp.OmtDialect.Z3)
    assert checked(source, target_path.read_text())['status'] == 'verified'
