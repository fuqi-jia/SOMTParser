import pytest
from somtparser.folio import FolParser, classify, folio_reference
from somtparser._nl_model import ModelError


def test_open_domain_is_not_grounded_to_named_constants():
    p = FolParser()
    result = classify([p.parse("P(alice)")], p.parse("∀x P(x)"))
    assert result["label"] == "Uncertain"


def test_entailment_and_contradiction():
    p = FolParser()
    premises = [p.parse("∀x (P(x) → Q(x))"), p.parse("P(alice)")]
    assert classify(premises, p.parse("Q(alice)"))["label"] == "True"
    assert classify(premises, p.parse("¬Q(alice)"))["label"] == "False"


def test_inconsistent_premises_are_separate():
    p = FolParser()
    assert (
        classify([p.parse("P(a)"), p.parse("¬P(a)")], p.parse("Q(a)"))["status"]
        == "inconsistent-premises"
    )


def test_equality_and_nested_quantifier():
    p = FolParser()
    assert classify([], p.parse("∀x ∃y (x = y)"))["label"] == "True"
    assert classify([p.parse("a ≠ b")], p.parse("∃x ∃y (x ≠ y)"))["label"] == "True"


@pytest.mark.parametrize(
    "text", ["P(x))", "P(x) junk", "P(x); import os", "(P(x)", "∀ (P(x))"]
)
def test_malformed_annotation_is_not_repaired(text):
    with pytest.raises(ModelError):
        FolParser().parse(text)


def test_published_identifier_characters_and_connective_spellings():
    p = FolParser()
    premises = [
        p.parse("∀x (Project(x) → WrittenIn(x, c++))"),
        p.parse("Project(l-2021)"),
    ]
    assert classify(premises, p.parse("WrittenIn(l-2021, c++)"))["label"] == "True"
    assert classify([], p.parse("∀x (P(x) ^ Q(x) ⟷ Q(x) ∧ P(x))"))["label"] == "True"
