import z3
from tools.semantic_checks.typed_target_bridge import check


def script(formula):
    return ('(set-logic ALL)(declare-const a (Array Int Int))'
            '(assert '+formula+')(minimize (select a 1))(check-sat)(exit)').encode()


def test_actual_expansion_normalization_and_group_progress_preserves_joint_relation():
    old = script('(forall ((i Int)) (=> (and (<= 0 i)(< i 2)) (or (= (select a i) 0)(= (select a i) 1))))')
    new = script('(and (<= 0 (select a 0))(<= (select a 0) 1)(<= 0 (select a 1))(<= (select a 1) 1))')
    events, originals = [], []
    proof = check(old, new, solve=True, progress_callback=events.append,
                  complete_relation_callback=lambda a, b: originals.append((a, b)))
    assert proof['full_relation_bridge'], proof
    phases = [r['phase'] for r in events]
    for phase in ['integer-step-expansion', 'integer-step-expansion-complete',
                  'finite-guard-expansion', 'finite-guard-expansion-complete',
                  'integer-normalization', 'integer-normalization-complete',
                  'qf-signatures', 'qf-grouping', 'qf-groups-ready', 'qf-complete']:
        assert phase in phases
    assert [r['side'] for r in events if r['phase'] == 'finite-guard-expansion'] == ['old', 'new']
    solver = z3.Solver(); solver.add(z3.Xor(*originals[0]))
    assert solver.check() == z3.unsat


def test_observation_return_value_cannot_bypass_changed_cost():
    old = script('(= (select a 0) 0)')
    new = old.replace(b'(minimize (select a 1))', b'(minimize (+ (select a 1) 1))')
    proof = check(old, new, solve=True,
                  progress_callback=lambda event: dict(equivalent=True, full_relation_bridge=True))
    assert not proof['full_relation_bridge']
