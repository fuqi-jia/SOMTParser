"""Skip duplicate diagnostics only after a complete certificate succeeded."""
import pytest
import z3

from tools.semantic_checks.source_oracles import xcsp_relation
from tools.semantic_checks.source_oracles.xcsp_source import Source


def model(direction=None):
    x = z3.Int('x')
    objectives = [(direction, x)] if direction else []
    return Source({'x': x}, {'x': ((0, 1),)},
                  [z3.And(x >= 0, x <= 1), x == 0], objectives, 1,
                  'COP' if objectives else 'CSP')


def target(direction=None, cost='x', private=False, extra_constraint=''):
    return ('(declare-const x Int)'+('(declare-const unused Bool)' if private else '')+
            '(assert (and (>= x 0)(<= x 1)))(assert (= x 0))'+extra_constraint+
            ('('+direction+' '+cost+')' if direction else '')+'(check-sat)(exit)').encode()


def proof_succeeded(result):
    return (result.get('conjunction_certificate', {}).get('equivalent') is True or
            result.get('universal_certificate', {}).get('equivalent') is True or
            (result.get('domain_cost_certificate', {}).get('equivalent') is True and
             result.get('composed_feasibility_certificate', {}).get('equivalent') is True))


def no_diagnostic(*args):
    raise AssertionError('complete relations were traversed again for diagnostics')


@pytest.mark.parametrize('direction', [None, 'minimize', 'maximize'])
@pytest.mark.parametrize('private', [False, True])
def test_complete_certificate_does_not_rerun_structural_diagnostics(monkeypatch, direction, private):
    monkeypatch.setattr(xcsp_relation, 'structural_equivalence', no_diagnostic)
    result = xcsp_relation.compare(model(direction), target(direction, private=private),
                                   solve=True, project_private_scalars=private)
    assert proof_succeeded(result) and result['equivalent']
    assert result['structural']['executed'] is False
    assert result['structural']['equivalent'] is None
    assert 'certificate' in result['structural']['reason']


@pytest.mark.parametrize('direction', ['minimize', 'maximize'])
def test_stronger_scalar_cost_still_rejects_a_counterexample_outside_feasible_set(monkeypatch, direction):
    calls = []
    original = xcsp_relation.structural_equivalence
    def record(left, right):
        calls.append((left, right))
        return original(left, right)
    monkeypatch.setattr(xcsp_relation, 'structural_equivalence', record)
    result = xcsp_relation.compare(model(direction), target(direction, cost='(* 2 x)'), solve=True)
    # At the only feasible point x=0 the joint cost is identical, so that full
    # certificate is valid. The public scalar API also checks domain point x=1.
    assert proof_succeeded(result) and result['relation_equivalent'] is True
    assert result['signed_cost_equal'] is False and result['equivalent'] is False
    assert result['cost_answer'] == 'sat' and '1' in result['cost_counterexample']
    assert result['structural']['executed'] is False
    assert result['structural']['equivalent'] is None
    assert len(calls) == 1  # The independent signed-cost structural attempt.
    assert result['signed_cost_scope'] == 'ordered signed-cost equality on all source-domain assignments'


@pytest.mark.parametrize('direction', ['minimize', 'maximize'])
def test_private_projection_keeps_joint_feasible_cost_contract(monkeypatch, direction):
    monkeypatch.setattr(xcsp_relation, 'structural_equivalence', no_diagnostic)
    result = xcsp_relation.compare(model(direction), target(direction, cost='(* 2 x)', private=True),
                                   solve=True, project_private_scalars=True)
    assert proof_succeeded(result) and result['equivalent'] and result['signed_cost_equal']
    assert result['structural']['executed'] is False
    assert result['signed_cost_scope'] == 'complete joint feasible relation and ordered signed-cost values'


def test_without_complete_certificate_the_existing_structural_check_still_executes(monkeypatch):
    calls = []
    original = xcsp_relation.structural_equivalence
    def record(left, right):
        calls.append((left, right))
        return original(left, right)
    monkeypatch.setattr(xcsp_relation, 'structural_equivalence', record)
    result = xcsp_relation.compare(model(), target(), solve=False)
    assert result['equivalent'] and len(calls) == 1
    assert result['structural']['equivalent'] is True
    assert result['structural'].get('executed') is not False


def test_failed_complete_relation_still_reaches_original_counterexample_check(monkeypatch):
    calls = []
    original = xcsp_relation.structural_equivalence
    def record(left, right):
        calls.append((left, right))
        return original(left, right)
    monkeypatch.setattr(xcsp_relation, 'structural_equivalence', record)
    result = xcsp_relation.compare(model(), target(extra_constraint='(assert false)'), solve=True)
    assert not proof_succeeded(result) and not result['equivalent']
    assert result['relation_equivalent'] is False and result['relation_answer'] == 'sat'
    assert calls and result['structural'].get('executed') is not False
