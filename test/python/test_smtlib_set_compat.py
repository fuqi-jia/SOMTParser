"""Opt-in cvc5 set syntax and exact preservation of a terminal query."""
import shutil
import subprocess
import pytest
import somtparser as sp


def translate(source, enabled=True):
    return sp.translate(source=source, language="smtlib2",
                        options={"cvc5_sets": "1"} if enabled else {})


def verdict(source):
    solver = shutil.which("cvc5")
    if not solver:
        pytest.skip("cvc5 unavailable")
    result = subprocess.run([solver, "--lang=smt2"], input=source, text=True,
                            capture_output=True, timeout=10)
    assert result.returncode == 0, result.stderr
    answers = [line for line in result.stdout.splitlines() if line in {"sat", "unsat", "unknown"}]
    assert len(answers) == 1 and answers[0] != "unknown", result.stdout
    return answers[0]


@pytest.mark.parametrize("sort,member", [("Bool", "true"), ("Bool", "false")])
def test_contextual_empty_preserves_nonempty_query(sort, member):
    source = f"""(set-logic ALL)
    (declare-const x (Set {sort}))
    (assert (= x (set.singleton {member})))
    (check-sat-assuming ((= set.empty x)))"""
    assert not translate(source, False).ok
    t = translate(source)
    assert t.ok, [d.message for d in t.diagnostic_items]
    # Dropping check-sat-assuming makes this SAT; acceptance alone misses it.
    assert verdict(source) == verdict(t.to_smt2()) == "unsat"


@pytest.mark.parametrize("body,answer", [
    ("(set.is_empty x)", "sat"),
    ("(and (set.member 1 x) (set.is_empty x))", "unsat"),
    ("(not (set.is_empty (set.singleton 1)))", "sat"),
])
def test_empty_predicate(body, answer):
    source = f"(set-logic ALL)(declare-const x (Set Int))(assert {body})(check-sat)"
    t = translate(source)
    assert t.ok, [d.message for d in t.diagnostic_items]
    assert verdict(source) == verdict(t.to_smt2()) == answer


def test_quoted_symbol_and_string_are_not_rewritten():
    source = '(declare-const |set.empty label| String)(assert (= |set.empty label| "set.is_empty"))(check-sat)'
    t = translate(source)
    assert t.ok
    assert '"set.is_empty"' in t.to_smt2()
    assert verdict(source) == verdict(t.to_smt2()) == "sat"


def test_untyped_empty_uses_cvc5_boolean_default():
    t = translate('(set-logic ALL)(assert (= set.empty set.empty))(check-sat)')
    assert t.ok
    assert verdict(t.to_smt2()) == "sat"
    for sort in ["Int", "Real"]:
        assert not translate(f'(declare-const x (Set {sort}))(assert (= set.empty x))(check-sat)').ok
    assert not translate('(assert (= set.empty 1))(check-sat)').ok


@pytest.mark.parametrize("tail", ["(check-sat)", "(assert false)", "(reset-assertions)"])
def test_assumption_query_is_not_silently_combined_or_moved(tail):
    t = translate('(declare-const x Bool)(check-sat-assuming (x))' + tail)
    assert not t.ok
    assert any("terminal query" in d.message for d in t.diagnostic_items)


def test_standard_assumptions_are_preserved_without_compatibility():
    t = translate('(declare-const x Bool)(assert x)(check-sat-assuming ((not x)))', False)
    assert t.ok
    assert verdict(t.to_smt2()) == "unsat"

