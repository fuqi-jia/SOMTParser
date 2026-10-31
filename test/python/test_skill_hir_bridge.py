"""End-to-end skill bridge checks, including incorrect snapshots and types."""
from pathlib import Path
import json
import os
import subprocess
import sys

import z3
import pytest


BRIDGE = Path(__file__).resolve().parents[2] / 'skills/somtparser-nl-hir/scripts/hir_bridge.py'


def invoke(*arguments):
    return subprocess.run([sys.executable, str(BRIDGE), *map(str, arguments)],
                          capture_output=True, text=True, env=os.environ.copy())


def fixture(tmp_path):
    source = tmp_path / 'problem.txt'
    source.write_text('The assertion is true.', encoding='utf-8')
    model = {'schema': 'somt-hir-model-v1', 'language': 'hir',
             'decision': 'satisfiability', 'declarations': [], 'functions': [],
             'constraints': [{'expr': {'literal': True, 'sort': 'Bool'},
                              'span': [0, len(source.read_text())]}],
             'objectives': [], 'objective_order': 'single', 'goal': None,
             'assumptions': [], 'unresolved': []}
    model_path = tmp_path / 'model.json'
    model_path.write_text(json.dumps(model), encoding='utf-8')
    return source, model_path


def test_request_and_export_use_real_api(tmp_path):
    source, model = fixture(tmp_path)
    request = invoke('request', source)
    assert request.returncode == 0, request.stderr
    payload = json.loads(request.stdout)
    assert payload['source'] == source.read_text()
    assert payload['language'] == 'hir'
    assert payload['operator_catalog']['operations']
    attempt = tmp_path / 'attempt'
    validated = invoke('validate', source, model, '--out', attempt)
    assert validated.returncode == 0, validated.stderr + validated.stdout
    candidate = json.loads((attempt / 'candidate.json').read_text())
    output = tmp_path / 'export'
    exported = invoke('compile', attempt / 'candidate.json', '--digest', candidate['digest'], '--out', output)
    assert exported.returncode == 0, exported.stderr + exported.stdout
    assertions = z3.parse_smt2_file(str(output / 'model.smt2'))
    solver = z3.Solver()
    solver.add(assertions)
    assert solver.check() == z3.sat
    assert json.loads((output / 'report.json').read_text())['intent_preservation'] == 'not-proved'


def test_wrong_snapshot_never_exports(tmp_path):
    source, model = fixture(tmp_path)
    attempt = tmp_path / 'attempt'
    assert invoke('validate', source, model, '--out', attempt).returncode == 0
    output = tmp_path / 'rejected'
    assert invoke('compile', attempt / 'candidate.json', '--digest', 'incorrect', '--out', output).returncode == 2
    assert not (output / 'model.smt2').exists()


def test_invalid_construction_returns_located_feedback(tmp_path):
    source, path = fixture(tmp_path)
    model = json.loads(path.read_text())
    model['constraints'][0]['expr'] = {'var': 'undeclared'}
    path.write_text(json.dumps(model))
    attempt = tmp_path / 'invalid'
    result = invoke('validate', source, path, '--out', attempt)
    assert result.returncode == 2, result.stdout + result.stderr
    feedback = json.loads((attempt / 'validation.json').read_text())
    assert not feedback['valid'] and feedback['diagnostics']
    assert feedback['diagnostic_details']


def test_unresolved_interpretation_cannot_export(tmp_path):
    source, path = fixture(tmp_path)
    model = json.loads(path.read_text())
    model['unresolved'] = ['The source permits two incompatible interpretations.']
    path.write_text(json.dumps(model))
    attempt = tmp_path / 'unresolved'
    assert invoke('validate', source, path, '--out', attempt).returncode == 2
    candidate = json.loads((attempt / 'candidate.json').read_text())
    output = tmp_path / 'export'
    assert invoke('compile', attempt / 'candidate.json', '--digest', candidate['digest'], '--out', output).returncode == 2
    assert not (output / 'model.smt2').exists()


def smt_fixture(tmp_path, program, decision='satisfiability'):
    source = tmp_path / 'problem.txt'
    source.write_text('Choose x between zero and three; maximize x.', encoding='utf-8')
    model = dict(schema='somt-nl-formal-v1', language='smtlib2', program=program,
                 decision=decision, assumptions=[], unresolved=[],
                 links=[dict(span=[0, len(source.read_text())], fragment=program)])
    path = tmp_path / 'model.json'
    path.write_text(json.dumps(model), encoding='utf-8')
    return source, path


def test_direct_smt_request_has_no_hir_catalog_and_exports_the_selected_model(tmp_path):
    source, path = smt_fixture(tmp_path,
        '(declare-const x Int)(assert (and (>= x 0) (<= x 3)))(maximize x)(check-sat)',
        'optimization')
    request = invoke('request', source, '--language', 'smtlib2')
    assert request.returncode == 0, request.stderr
    payload = json.loads(request.stdout)
    assert payload['language'] == 'smtlib2' and 'operator_catalog' not in payload
    assert payload['schema']['properties']['program']['type'] == 'string'
    attempt = tmp_path / 'attempt'
    response = invoke('validate', source, path, '--language', 'smtlib2', '--out', attempt)
    assert response.returncode == 0, response.stderr + response.stdout
    validation = json.loads(response.stdout)
    assert validation['valid'] and validation['language_configuration'] == 'smtlib2'
    output = tmp_path / 'export'
    response = invoke('compile', attempt / 'candidate.json', '--digest', validation['digest'], '--out', output)
    assert response.returncode == 0, response.stderr + response.stdout
    solver = z3.Optimize()
    solver.from_file(str(output / 'model.smt2'))
    assert solver.check() == z3.sat
    assert solver.model().eval(z3.Int('x')).as_long() == 3
    report = json.loads((output / 'report.json').read_text())
    assert report['language_configuration'] == 'smtlib2'
    assert report['intent_preservation'] == 'not-proved'


@pytest.mark.parametrize('program,decision', [
    ('(declare-const x Int)(assert', 'satisfiability'),
    ('(declare-const x Int)(assert (and x true))', 'satisfiability'),
    ('(declare-const x Int)(maximize x)', 'satisfiability'),
])
def test_direct_smt_validation_returns_native_errors_as_json(tmp_path, program, decision):
    source, path = smt_fixture(tmp_path, program, decision)
    attempt = tmp_path / 'invalid'
    response = invoke('validate', source, path, '--language', 'smtlib2', '--out', attempt)
    assert response.returncode == 2, response.stdout + response.stderr
    feedback = json.loads(response.stdout)
    assert not feedback['valid'] and feedback['diagnostics']
    assert feedback['diagnostic_details'][0]['json_pointer'] in ('/program', '/decision')
    assert not (attempt / 'model.smt2').exists()


def test_direct_smt_does_not_silently_ignore_hir_output_contract(tmp_path):
    source, _ = smt_fixture(tmp_path, '(assert true)')
    contract = tmp_path / 'outputs.json'
    contract.write_text('[]')
    response = invoke('request', source, '--language', 'smtlib2', '--required-outputs', contract)
    assert response.returncode == 2
    assert 'requires --language hir' in response.stderr
