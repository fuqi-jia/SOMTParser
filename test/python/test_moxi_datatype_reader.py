"""Explicit datatype syntax compatibility and independent relation oracles."""
import json
from pathlib import Path
import shutil
import subprocess

import pytest
import z3
import somtparser as sp

ROOT = Path(__file__).resolve().parents[2]
ORIGINAL = ROOT / 'languages/moxi/instances/upstream/QF_LRA_LossyIntChannelX.moxi'
OPTION = {'flat_datatype_constructors': 'true'}


def export(source=None, path=None, options=None):
    module = sp.import_module(str(path) if path else '', source=source or '',
                              language='moxi', options=options or {})
    assert module.ok, [d.message for d in module.diagnostics]
    text = module.to_smt2()
    return text, json.loads(text.splitlines()[0].removeprefix('; SOMT module interface '))


def relation_query(text, metadata, index, label, reference):
    entry = metadata['systems'][index]
    declarations = ''.join(f"(declare-const {p['symbol']} {p['sort']})"
                           for p in entry['parameters'])
    arguments = ' '.join(p['symbol'] for p in entry['parameters'])
    call = f"({entry['relations'][label]} {arguments})"
    return text + declarations + f'(assert (xor {call} {reference}))(check-sat)'


def original_relation_checks(text, metadata):
    assert [s['name'] for s in metadata['systems']] == ['LossyRealChannel'] * 2
    assert [len(s['parameters']) for s in metadata['systems']] == [4, 6]
    checks = []
    for index in range(2):
        for label in ['init', 'trans', 'invariant']:
            expected = 'true'
            if label == 'invariant':
                expected = ('(or (= out in) (= out (as Absent (Event Real))))' if index == 0
                            else '(= out (ite s in (as Absent (Event Real))))')
            script = relation_query(text, metadata, index, label, expected)
            solver = z3.Solver()
            solver.set(timeout=5000)
            solver.from_string(script)
            assert solver.check() == z3.unsat, (index, label)
            checks.append((index, label, script))
    return checks


def test_original_library_is_explicitly_normalized_and_all_relations_exported():
    assert not sp.import_module(str(ORIGINAL)).ok
    text, metadata = export(path=ORIGINAL, options=OPTION)
    assert '(check-sat)' not in text
    rewrites = metadata['source_rewrites']
    assert len(rewrites) == 1 and rewrites[0]['line'] == 6
    assert rewrites[0]['rule'] == 'explicit-flat-datatype-constructors'
    assert rewrites[0]['original'] == '(declare-datatype Event (par (X) (Absent) (Present (val X))))'
    assert rewrites[0]['replacement'] == '(declare-datatype Event (par (X) ((Absent) (Present (val X)))))'
    original_relation_checks(text, metadata)


@pytest.mark.parametrize('declaration', [
    '(declare-datatype E (par (T) (none) (some (value T))))',
    '(declare-datatype E (par (T) (none)))',
    '(declare-datatypes ((E 1)) ((par (T) (none) (some (value T)))))',
    '(declare-datatypes ((E 1) (F 0)) ((par (T) (none) (some (value T))) ((done))))',
    '(declare-datatype E (par (T) ; (comment)\n (none) (some (value T))))',
])
def test_general_constructor_lists_not_a_filename_patch(declaration):
    source = declaration + '(define-system S :input ((x (E Int))) :inv (= x none))'
    text, metadata = export(source, options=OPTION)
    assert len(metadata['source_rewrites']) == 1
    solver = z3.Solver()
    solver.from_string(relation_query(text, metadata, 0, 'invariant', '(= x (as none (E Int)))'))
    assert solver.check() == z3.unsat


def test_standard_syntax_is_unchanged_even_with_option():
    source = '(declare-datatype E (par (T) ((none) (some (value T)))))' \
             '(define-system S :input ((x (E Int))) :inv (= x none))'
    normal, metadata = export(source)
    selected, selected_metadata = export(source, options=OPTION)
    assert normal == selected and metadata == selected_metadata
    assert 'source_rewrites' not in metadata


def test_multiple_rewrite_locations_and_quoted_constructor_names():
    source = '''; initial comment
(declare-datatype E (par (T) (|none;()|) (some (value T))))
; intervening line

(declare-datatype F (par (T) (empty) (full (payload T))))
(define-system S :input ((x (E Int)) (y (F Bool)))
 :inv (and (= x |none;()|) (= y empty)))'''
    text, metadata = export(source, options=OPTION)
    assert [r['line'] for r in metadata['source_rewrites']] == [2, 5]
    assert '|none;()|' in metadata['source_rewrites'][0]['replacement']
    assert len(z3.parse_smt2_string(text)) == 0


@pytest.mark.parametrize('options', [
    {'flat_datatype_constructors': 'false'},
    {'flat_datatype_constructors': 'yes'},
    {'flat_datatype_constructor': 'true'},
    {'bmc_depth': '1'},
])
def test_disabled_invalid_and_irrelevant_module_options_fail(options):
    result = sp.import_module(str(ORIGINAL), options=options)
    assert not result.ok
    assert all(d.code != sp.ErrorCode.E_INTERNAL for d in result.diagnostics)


@pytest.mark.parametrize('language,source', [('aiger', 'aag 0 0 0 0 0\n'),
                                           ('flatzinc', 'solve satisfy;')])
def test_module_options_cannot_be_silently_ignored(language, source):
    result = sp.import_module(source=source, language=language, options=OPTION)
    assert not result.ok


@pytest.mark.parametrize('body', [
    '(par (T) (none) (some (value Missing)))',
    '(par (T) (none) (some (value T extra)))',
    '(par (T) (none) extra)',
])
def test_layout_option_does_not_mask_malformed_declarations(body):
    source = '(declare-datatype E ' + body + ')(define-system S :input ((x (E Int))))'
    result = sp.import_module(source=source, language='moxi', options=OPTION)
    assert not result.ok
    assert all(d.code != sp.ErrorCode.E_INTERNAL for d in result.diagnostics)


def test_same_dialect_is_available_for_bounded_queries_and_reported():
    source = '''(declare-datatype E (par (T) (none) (some (value T))))
      (define-system S :input ((x (E Int))) :inv (= x none))
      (check-system S :input ((x (E Int))) :reachable (r ((_ is some) x)) :query (q (r)))'''
    result = sp.translate(source=source, language='moxi', profile='bmc',
                          options={**OPTION, 'bmc_depth': '1'})
    assert result.ok, [d.message for d in result.diagnostic_items]
    assert any(c.strategy == 'explicit-flat-datatype-constructors' for c in result.report.choices)
    solver = z3.Solver()
    solver.from_string(result.to_smt2())
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('term', [
    '(= x none)', '(= none x)', '(= none x none)',
    '(distinct none x)', '(distinct x none)',
    '(= x (ite b x none))', '(= x (ite b none x))',
])
def test_nullary_constructor_inference_preserves_formula(term):
    declarations = '''(set-logic ALL)
      (declare-datatype E (par (T) ((none) (some (value T)))))
      (declare-const x (E Int))(declare-const b Bool)'''
    result = sp.translate(source=declarations + '(assert ' + term + ')', language='smtlib2')
    assert result.ok, [d.message for d in result.diagnostic_items]
    # The explicitly typed source is an independent reference accepted by Z3.
    reference = z3.And(*z3.parse_smt2_string(declarations + '(assert ' +
                         term.replace('none', '(as none (E Int))') + ')'))
    actual = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    solver = z3.Solver()
    solver.add(reference != actual)
    assert solver.check() == z3.unsat


def test_separate_nullary_occurrences_keep_separate_instances():
    source = '''(set-logic ALL)
      (declare-datatype E (par (T) ((none) (some (value T)))))
      (declare-const x (E Int))(declare-const y (E Bool))
      (assert (= x none))(assert (= y none))
      (assert ((_ is none) x))(assert ((_ is none) y))'''
    result = sp.translate(source=source, language='smtlib2')
    assert result.ok, [d.message for d in result.diagnostic_items]
    # Z3's indexed tester lookup is ambiguous after the same parametric nullary
    # constructor has been instantiated twice, including on the typed reference
    # below. cvc5 can check the complete source and output, including both testers.
    executable = shutil.which('cvc5')
    if executable is None:
        pytest.skip('cvc5 is required for polymorphic indexed testers')
    reference = source.replace('(= x none)', '(= x (as none (E Int)))') \
                      .replace('(= y none)', '(= y (as none (E Bool)))') + '(check-sat)'
    for text in [reference, result.to_smt2()]:
        solved = subprocess.run([executable, '--lang=smt2', '--tlimit=5000'],
                                input=text, text=True, capture_output=True, timeout=10)
        assert solved.returncode == 0 and solved.stdout.strip() == 'sat', solved.stdout + solved.stderr


@pytest.mark.parametrize('term', [
    '(= x (as none (E Bool)))', '(= (as none (E Bool)) x none)',
    '(distinct none x (as none (E Bool)))',
    '(= x (ite b x (as none (E Bool))))',
])
def test_inference_never_overwrites_explicit_incompatible_types(term):
    source = '''(set-logic ALL)(declare-datatype E (par (T) ((none) (some (value T)))))
      (declare-const x (E Int))(declare-const b Bool)(assert ''' + term + ')'
    result = sp.translate(source=source, language='smtlib2')
    assert not result.ok
