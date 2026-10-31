"""WBO projection controls with independent exhaustive integer evaluation."""
from io import BytesIO
import itertools
import pytest

from tools.semantic_checks.pb_certificate import CertificateError, verify_streams


SOURCE = 'soft: 2; [1] +1 x1 >= 1; [1] +1 x2 >= 1;'


def script():
    declarations = ''.join(f'(declare-fun {name} () Int)' for name in ('x1', 'x2', 'missing_a', 'missing_b', 'cost_first', 'cost_last'))
    bounds = ''.join(f'(assert (>= {name} 0))(assert (<= {name} 1))' for name in ('x1', 'x2', 'missing_a', 'missing_b'))
    return '(set-logic ALL)' + declarations + bounds + '''
    (assert (>= (+ x1 missing_a) 1))
    (assert (<= (+ x1 missing_a) 1))
    (assert (>= (+ x2 missing_b) 1))
    (assert (<= (+ x2 missing_b) 1))
    (assert (= cost_first missing_a))
    (assert (= cost_last (+ cost_first missing_b)))
    (assert (< cost_last 2))
    (minimize cost_last)(check-sat)(exit)
    '''


def check(source=SOURCE, target=None):
    return verify_streams(BytesIO(source.encode()), BytesIO((script() if target is None else target).encode()))


def test_unique_extension_and_cost_prefixes():
    proof = check()
    assert proof['status'] == 'verified'
    assert proof['projection']['binary_violation_indicators'] == 2
    assert proof['projection']['uniquely_defined_cost_coordinates'] == 2


def test_indicator_names_have_no_semantic_role():
    target = script().replace('missing_a', '|hidden-A|').replace('cost_last', '!result')
    assert check(target=target)['status'] == 'verified'


@pytest.mark.parametrize('before,after', [
    ('(>= missing_a 0)', '(>= missing_a (- 1))'),
    ('(<= missing_a 1)', '(<= missing_a 2)'),
    ('(assert (<= missing_a 1))', ''),
    ('(assert (>= (+ x1 missing_a) 1))', ''),
    ('(assert (<= (+ x1 missing_a) 1))', ''),
    ('(<= (+ x1 missing_a) 1)', '(<= (+ x1 missing_a) 2)'),
    ('(>= (+ x2 missing_b) 1)', '(>= (+ x1 missing_b) 1)'),
    ('(= cost_first missing_a)', '(= cost_first (+ missing_a 1))'),
    ('(= cost_first missing_a)', '(= (* 2 cost_first) missing_a)'),
    ('(= cost_first missing_a)', '(= cost_first (+ cost_last missing_a))'),
    ('(= cost_last (+ cost_first missing_b))', '(= cost_last (+ cost_first (* 2 missing_b)))'),
    ('(assert (= cost_first missing_a))', ''),
    ('(< cost_last 2)', '(<= cost_last 2)'),
    ('(assert (< cost_last 2))', ''),
    ('(minimize cost_last)', '(maximize cost_last)'),
    ('(minimize cost_last)', '(minimize (* cost_last cost_last))'),
    ('(check-sat)', '(assert (>= cost_first 1))(check-sat)'),
    ('(check-sat)', '(assert (>= (+ missing_a missing_b) 1))(check-sat)'),
    ('(declare-fun cost_last () Int)', '(declare-fun cost_last () Int)(declare-fun unused () Int)'),
])
def test_changed_domain_branch_definition_threshold_or_cost_is_not_certified(before, after):
    with pytest.raises(CertificateError):
        check(target=script().replace(before, after))


def test_exhaustive_independent_semantics_and_unique_extensions():
    import z3
    check()
    opt = z3.Optimize()
    opt.from_string(script())
    assertions = z3.And(*opt.assertions())
    for x1, x2 in itertools.product((0, 1), repeat=2):
        cost = (1-x1) + (1-x2)
        solver = z3.Solver()
        solver.add(assertions, z3.Int('x1') == x1, z3.Int('x2') == x2)
        assert (solver.check() == z3.sat) == (cost < 2)
        if cost < 2:
            model = solver.model()
            assert model.eval(opt.objectives()[0]).as_long() == cost
            extension = [z3.Int(n) == model.eval(z3.Int(n)) for n in
                         ('missing_a', 'missing_b', 'cost_first', 'cost_last')]
            solver.add(z3.Not(z3.And(*extension)))
            assert solver.check() == z3.unsat


def test_equality_uses_disjoint_violation_indicators():
    source = 'soft:; [7] +1 x1 -1 x2 = 0;'
    declarations = ''.join(f'(declare-fun {n} () Int)' for n in ('x1','x2','below','above','cost'))
    bounds = ''.join(f'(assert (>= {n} 0))(assert (<= {n} 1))' for n in ('x1','x2','below','above'))
    target = '(set-logic ALL)' + declarations + bounds + '''
        (assert (>= (+ x1 (- x2) below) 0))
        (assert (<= (+ x1 (- x2) (* 2 below)) 1))
        (assert (<= (+ x1 (- x2) (- above)) 0))
        (assert (>= (+ x1 (- x2) (* (- 2) above)) (- 1)))
        (assert (= cost (+ (* 7 below) (* 7 above))))
        (minimize cost)(check-sat)(exit)'''
    assert check(source, target)['status'] == 'verified'


def test_unbounded_private_coordinate_multiplication_is_never_reduced_to_binary():
    target = script().replace('(= cost_first missing_a)', '(= (* cost_first cost_first) missing_a)')
    with pytest.raises(CertificateError, match='nonlinear product of private'):
        check(target=target)


def test_projected_certificate_also_requires_raw_public_domains():
    target = script().replace('(>= x1 0)', '(>= (* x1 x1) 0)').replace('(<= x1 1)', '(<= (* x1 x1) 1)')
    with pytest.raises(CertificateError, match='raw target Boolean domains'):
        check(target=target)


def equivalence_script():
    return script().replace('''(assert (>= (+ x1 missing_a) 1))
    (assert (<= (+ x1 missing_a) 1))''',
        '(assert (= (= missing_a 0) (>= x1 1)))').replace(
        '''(assert (>= (+ x2 missing_b) 1))
    (assert (<= (+ x2 missing_b) 1))''',
        '(assert (= (>= x2 1) (= 0 missing_b)))')


def test_boolean_equivalence_defines_both_integer_indicator_branches():
    import z3
    target = equivalence_script()
    assert check(target=target)['status'] == 'verified'
    opt = z3.Optimize()
    opt.from_string(target)
    for x1, x2 in itertools.product((0, 1), repeat=2):
        solver = z3.Solver()
        solver.add(*opt.assertions(), z3.Int('x1') == x1, z3.Int('x2') == x2)
        cost = 2-x1-x2
        assert (solver.check() == z3.sat) == (cost < 2)
        if cost < 2:
            model = solver.model()
            assert model.eval(opt.objectives()[0]).as_long() == cost
            solver.add(z3.Or(z3.Int('missing_a') != 1-x1,
                             z3.Int('missing_b') != 1-x2,
                             z3.Int('cost_first') != 1-x1,
                             z3.Int('cost_last') != cost))
            assert solver.check() == z3.unsat


@pytest.mark.parametrize('before,after', [
    ('(= missing_a 0)', '(= missing_a 1)'),
    ('(>= x1 1)', '(>= x1 0)'),
    ('(>= x1 1)', '(>= x2 1)'),
    ('(assert (= (= missing_a 0) (>= x1 1)))', ''),
    ('(assert (<= missing_a 1))', ''),
    ('(>= x1 1)', '(= missing_b 0)'),
    ('(check-sat)', '(assert (= missing_a 0))(check-sat)'),
    ('(minimize cost_last)', '(minimize (+ cost_last 1))'),
    ('(< cost_last 2)', '(<= cost_last 2)'),
])
def test_boolean_reification_mutations_are_not_certified(before, after):
    target = equivalence_script()
    assert before in target
    with pytest.raises(CertificateError):
        check(target=target.replace(before, after))


def test_equivalence_with_one_tests_has_the_correct_polarity():
    target = equivalence_script().replace('''(= (= missing_a 0) (>= x1 1))''',
        '(= (= missing_a 1) (not (>= x1 1)))')
    assert check(target=target)['status'] == 'verified'


def assert_native_public_cost_projection(target, public_names, source_cost, top):
    """Check every source assignment and its minimum cost over target auxiliaries."""
    import z3
    parsed = z3.Optimize()
    parsed.from_string(target)
    assert len(parsed.objectives()) == 1
    objective = parsed.objectives()[0]
    variables = [z3.Int(name) for name in public_names]
    domain = z3.Solver()
    domain.add(*parsed.assertions())
    domain.add(z3.Or(*[z3.Or(var < 0, var > 1) for var in variables]))
    assert domain.check() == z3.unsat
    for values in itertools.product((0, 1), repeat=len(variables)):
        expected_cost = source_cost(*values)
        fixed = [var == value for var, value in zip(variables, values)]
        optimizer = z3.Optimize()
        optimizer.add(*parsed.assertions(), *fixed)
        optimizer.minimize(objective)
        status = optimizer.check()
        assert status == (z3.sat if expected_cost < top else z3.unsat)
        if status == z3.sat:
            assert optimizer.model().eval(objective).as_long() == expected_cost
            # Independently rule out a cheaper extension for this source state.
            lower = z3.Solver()
            lower.add(*parsed.assertions(), *fixed, objective < expected_cost)
            assert lower.check() == z3.unsat


@pytest.mark.parametrize('source, public_names, source_cost, top, certificate_supported', [
    ('soft: 5; [5] +1 x1 >= 1; [2] +1 x2 >= 1;',
     ('x1', 'x2'), lambda x1, x2: 5*(1-x1) + 2*(1-x2), 5, False),
    ('soft: 3; [5] +1 x1 >= 1; [2] +1 x2 >= 1; [2] +1 x3 >= 1;',
     ('x1', 'x2', 'x3'), lambda x1, x2, x3: 5*(1-x1) + 2*(1-x2) + 2*(1-x3), 3, False),
    ('soft: 9; [7] +1 x1 -1 x2 = 0;',
     ('x1', 'x2'), lambda x1, x2: 7*(x1 != x2), 9, True),
])
def test_real_native_finite_top_cost_projection(tmp_path, source, public_names, source_cost, top, certificate_supported):
    import somtparser as sp
    path = tmp_path / 'finite-top.wbo'
    path.write_text(source)
    model = sp.translate(path=str(path), language='opb')
    assert model.ok, [str(x) for x in model.diagnostic_items]
    target = tmp_path / 'target.smt2'
    model.write_smt2(str(target), sp.OmtDialect.Z3)
    assert check(source, target.read_text())['status'] == 'verified'
    assert_native_public_cost_projection(target.read_text(), public_names, source_cost, top)


def test_real_native_packed_weighted_model(tmp_path):
    import somtparser as sp
    # Enough terms to exercise the real compact weighted-row encoder, with
    # unique costs and both comparison directions across the source rows.
    terms = ' '.join('+1 x' + str(i) for i in range(1, 33001))
    source = 'soft:; [7] ' + terms + ' >= 2000; [11] ' + terms + ' <= 3000;'
    path = tmp_path / 'input.wbo'
    path.write_text(source)
    model = sp.translate(path=str(path), language='opb')
    assert model.ok, [str(x) for x in model.diagnostic_items]
    target = tmp_path / 'target.smt2'
    model.write_smt2(str(target), sp.OmtDialect.Z3)
    proof = check(source, target.read_text())
    assert proof['projection']['binary_violation_indicators'] == 2


def mandatory_duplicate_script():
    return script().replace('(= cost_first missing_a)',
        '(= cost_first (* 2 missing_a))').replace('(< cost_last 2)',
        '(< cost_last 3)').replace('(minimize cost_last)',
        '(assert (>= x1 1))(minimize cost_last)')


@pytest.mark.parametrize('mandatory', ['[3] +1 x1 >= 1;', '+1 x1 >= 1;'])
def test_retained_indicator_for_mandatory_duplicate_has_zero_feasible_cost(mandatory):
    import z3
    source = 'soft: 3; ' + mandatory + ' [2] +1 x1 >= 1; [1] +1 x2 >= 1;'
    target = mandatory_duplicate_script()
    assert check(source, target)['status'] == 'verified'
    opt = z3.Optimize()
    opt.from_string(target)
    for x1, x2 in itertools.product((0, 1), repeat=2):
        solver = z3.Solver()
        solver.add(*opt.assertions(), z3.Int('x1') == x1, z3.Int('x2') == x2)
        source_cost = 5*(1-x1) + (1-x2)
        assert (solver.check() == z3.sat) == (x1 == 1 and source_cost < 3)
        if x1 == 1:
            model = solver.model()
            assert model.eval(opt.objectives()[0]).as_long() == source_cost
            solver.add(z3.Or(z3.Int('missing_a') != 0,
                             z3.Int('missing_b') != 1-x2,
                             z3.Int('cost_first') != 0,
                             z3.Int('cost_last') != source_cost))
            assert solver.check() == z3.unsat


@pytest.mark.parametrize('before,after', [
    ('(assert (>= x1 1))', ''),
    ('(assert (>= x1 1))', '(assert (>= x2 1))'),
    ('(assert (<= missing_a 1))', ''),
    ('(<= (+ x1 missing_a) 1)', '(<= (+ x1 missing_a) 2)'),
    ('(= cost_last (+ cost_first missing_b))',
     '(= cost_last (+ cost_first (* 2 missing_b)))'),
    ('(minimize cost_last)', '(minimize (+ cost_last 1))'),
])
def test_retained_mandatory_indicator_still_checks_hard_rows_branches_and_cost(before, after):
    source = 'soft: 3; [3] +1 x1 >= 1; [2] +1 x1 >= 1; [1] +1 x2 >= 1;'
    target = mandatory_duplicate_script()
    assert before in target
    with pytest.raises(CertificateError):
        check(source, target.replace(before, after))


@pytest.mark.parametrize('predicate', ['+1 x1 >= 1', '+1 x1 -1 x2 = 0'])
def test_real_native_retains_soft_duplicate_of_hardened_row(tmp_path, predicate):
    import somtparser as sp
    source = f'soft: 7; [7] {predicate}; [3] {predicate}; [1] +1 x3 >= 1;'
    path = tmp_path / 'mandatory-duplicate.wbo'
    path.write_text(source)
    model = sp.translate(path=str(path), language='opb')
    assert model.ok, [str(x) for x in model.diagnostic_items]
    target = tmp_path / 'target.smt2'
    model.write_smt2(str(target), sp.OmtDialect.Z3)
    assert check(source, target.read_text())['status'] == 'verified'
    text = target.read_text()
    if predicate == '+1 x1 >= 1':
        public_names = ('x1', 'x3')
        source_cost = lambda x1, x3: 10*(1-x1) + (1-x3)
    else:
        public_names = ('x1', 'x2', 'x3')
        source_cost = lambda x1, x2, x3: 10*(x1 != x2) + (1-x3)
    assert_native_public_cost_projection(text, public_names, source_cost, 7)
