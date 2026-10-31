"""Preserve greatest fixed points through both parser and typed HIR round trips."""
from pathlib import Path
import shutil
import subprocess

import pytest
import somtparser as sp


def solve(source):
    executable = shutil.which('cvc5')
    if executable is None:
        pytest.skip('cvc5 is required for native codatatype semantics')
    result = subprocess.run([executable, '--lang=smt2', '--tlimit=10000'], input=source,
                            text=True, capture_output=True, timeout=15)
    assert result.returncode == 0, result.stdout + result.stderr
    answers = [line for line in result.stdout.splitlines() if line in ('sat', 'unsat', 'unknown')]
    assert len(answers) == 1 and answers[0] != 'unknown', result.stdout + result.stderr
    return answers[0]


STREAM = '(declare-codatatypes ((Stream 0)) (((cons (head Int) (tail Stream)))))'
PARAMETRIC = '(declare-codatatypes ((Stream 1)) ((par (X) ((cons (head X) (tail (Stream X)))))))'


@pytest.mark.parametrize('declarations,constraints,expected', [
    (STREAM + '(declare-const s Stream)', '(= s (cons 1 s))', 'sat'),
    (STREAM + '(declare-const s Stream)', '(and (= s (cons 1 s)) (= (head s) 2))', 'unsat'),
    (STREAM + '(declare-const s Stream)(declare-const t Stream)',
     '(and (= s (cons 1 t)) (= t (cons 2 s)))', 'sat'),
    (STREAM + '(declare-const s Stream)', '(not ((_ is cons) s))', 'unsat'),
    (PARAMETRIC + '(declare-const s (Stream Int))', '(= s (cons 3 s))', 'sat'),
    (PARAMETRIC + '(declare-const s (Stream Int))',
     '(and (= s (cons 3 s)) (= (head s) 4))', 'unsat'),
    ('(declare-codatatypes ((S 0) (T 0)) (((A (a T))) ((B (b S)))))'
     '(declare-const s S)(declare-const t T)', '(and (= s (A t)) (= t (B s)))', 'sat'),
    (STREAM + '(declare-datatype Box ((box (stream Stream))))'
     '(declare-const b Box)', '(= (stream b) (cons 1 (stream b)))', 'sat'),
])
def test_source_and_two_hir_roundtrips_agree(declarations, constraints, expected):
    source = '(set-logic ALL)' + declarations + '(assert ' + constraints + ')(check-sat)'
    assert solve(source) == expected
    for _ in range(2):
        result = sp.translate(source=source, language='smtlib2')
        assert result.ok, [d.message for d in result.diagnostic_items]
        assert result.report.fidelity.sound and result.report.fidelity.complete
        source = result.to_smt2()
        assert '(declare-codatatypes ' in source
        assert solve(source) == expected


def test_original_codatatype_regression_roundtrip():
    path = Path(__file__).resolve().parents[2] / (
        'languages/smtlib2/instances/upstream/datatypes_cdt-enum-type-mismatch.smt2')
    source = path.read_text()
    result = sp.translate(source=source, language='smtlib2')
    assert result.ok, [d.message for d in result.diagnostic_items]
    target = result.to_smt2()
    assert '(declare-datatypes ' not in target
    assert solve(source) == solve(target) == 'sat'


def test_coinduction_is_not_replaced_by_induction():
    source = ('(set-logic ALL)(declare-codatatypes ((S 0)) (((end) (step (tail S)))))'
              '(declare-const s S)(assert (= s (step s)))(check-sat)')
    assert solve(source) == 'sat'
    assert solve(source.replace('declare-codatatypes', 'declare-datatypes')) == 'unsat'
    result = sp.translate(source=source, language='smtlib2')
    assert result.ok, [d.message for d in result.diagnostic_items]
    assert solve(result.to_smt2()) == 'sat'


def test_command_log_distinguishes_coinductive_declaration():
    parser = sp.Parser()
    parser.set_command_logging(True)
    parser.parse_string('(set-logic ALL)' + STREAM + '(check-sat)')
    commands = list(parser.script)
    assert commands[1].type == sp.CmdType.DECLARE_CODATATYPES
