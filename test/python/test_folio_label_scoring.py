"""The public dataset's Unknown label is not a solver unknown outcome."""
from copy import deepcopy
import pytest
from somtparser._nl_model import ModelError
from somtparser.folio import score_label, FolParser, classify


@pytest.mark.parametrize('spelling', ['Unknown', 'Uncertain'])
def test_unknown_label_alias_preserves_solver_evidence_and_input(spelling):
    parser=FolParser()
    result=classify([parser.parse('P(a)')],parser.parse('Q(a)'))
    original=deepcopy(result)
    scored=score_label(result,spelling)
    assert result==original
    assert scored['status']=='label-agreement'
    assert scored['expected_label']==spelling
    assert scored['expected_label_canonical']=='Uncertain'
    assert scored['consistency']==scored['negated_conclusion']==scored['positive_conclusion']=='sat'
    assert score_label(scored,spelling)==scored


@pytest.mark.parametrize('status', ['solver-unknown','inconsistent-premises','translation-refused','generation-failed'])
def test_nonclassified_outcomes_never_become_correct_unknown_predictions(status):
    row=score_label(dict(status=status,label=None),'Unknown')
    assert row['status']==status
    assert row['label'] is None


@pytest.mark.parametrize('label', ['unknown','UNCERTAIN','',True,None,'Unknown '])
def test_unrecognized_label_spellings_are_not_guessed(label):
    with pytest.raises(ModelError):score_label(dict(status='solver-unknown'),label)


def test_published_label_alias_does_not_change_true_or_false_predictions():
    parser=FolParser()
    premises=[parser.parse('P(a)')]
    true=classify(premises,parser.parse('P(a)'))
    false=classify(premises,parser.parse('¬P(a)'))
    assert score_label(true,'True')['status']=='label-agreement'
    assert score_label(false,'False')['status']=='label-agreement'
    assert score_label(true,'Unknown')['status']=='label-disagreement'


def test_unknown_needs_two_satisfiable_polarities():
    with pytest.raises(ModelError):
        score_label(dict(status='classified',label='Uncertain',consistency='sat',
                         positive_conclusion='unknown',negated_conclusion='sat'),'Unknown')
