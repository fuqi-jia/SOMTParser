"""Independent cvc5 checks for datatype type parameters under containers."""
import shutil
import subprocess

import pytest
import somtparser as sp


def solve(source):
    executable = shutil.which("cvc5")
    if executable is None:
        pytest.skip("cvc5 is required for parametric datatype semantics")
    result = subprocess.run(
        [executable, "--lang=smt2", "--arrays-exp", "--tlimit=5000"],
        input=source,
        text=True,
        capture_output=True,
        timeout=10,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    answers = [line for line in result.stdout.splitlines()
               if line in {"sat", "unsat", "unknown"}]
    assert len(answers) == 1 and answers[0] != "unknown", result.stdout
    return answers[0]


def check_source_and_roundtrip(source, expected):
    translated = sp.translate(
        source=source,
        language="smtlib2",
        options={"cvc5_sets": "1"},
    )
    assert translated.ok, [item.message for item in translated.diagnostic_items]
    target = translated.to_smt2()
    if "(check-sat)" not in target:
        target += "\n(check-sat)\n"
    assert solve(source) == expected
    assert solve(target) == expected


def check_pair(base, query):
    # The base facts determine the datatype value. Ask the positive and
    # negative query in separate scripts, so UNSAT depends on selector
    # semantics rather than asserting a proposition and its negation together.
    check_source_and_roundtrip(base + f"(assert {query})\n(check-sat)\n", "sat")
    check_source_and_roundtrip(base + f"(assert (not {query}))\n(check-sat)\n", "unsat")


def test_parameter_substitution_under_array_fields():
    base = f"""(set-logic ALL)
(declare-datatypes ((ArrayBox 1))
  ((par (T) ((arraybox (payload (Array Int T)))))))
(declare-const value (ArrayBox Bool))
"""
    base += "(assert (= value (arraybox (store ((as const (Array Int Bool)) false) 0 true))))\n"
    check_pair(base, "(= (select (payload value) 0) true)")
    check_pair(base, "(= (select (payload value) 1) false)")


def test_parameter_substitution_under_array_index_sorts():
    base = f"""(set-logic ALL)
(declare-datatypes ((ArrayIndexBox 1))
  ((par (T) ((arrayindexbox (payload (Array T Bool)))))))
(declare-const value (ArrayIndexBox Bool))
"""
    base += """(assert (= value (arrayindexbox
  (store (store ((as const (Array Bool Bool)) false) true true) false false))))
"""
    check_pair(base, "(= (select (payload value) true) true)")
    check_pair(base, "(= (select (payload value) false) false)")


def test_parameter_substitution_under_set_fields():
    base = f"""(set-logic ALL)
(declare-datatypes ((SetBox 1))
  ((par (T) ((setbox (contents (Set T)))))))
(declare-const value (SetBox Bool))
"""
    base += "(assert (= value (setbox (set.singleton false))))\n"
    check_pair(base, "(set.member false (contents value))")
    check_pair(base, "(not (set.member true (contents value)))")
