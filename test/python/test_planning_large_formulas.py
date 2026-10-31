"""Large finite quantifiers and fact tables preserve the last source literal."""
import json
import os
from pathlib import Path
import subprocess
import sys

import pytest


@pytest.mark.parametrize('quantifier,last,expected', [
    ('forall', True, 'sat'),
    ('forall', False, 'unsat'),
    ('exists', True, 'sat'),
    ('exists', False, 'unsat'),
])
def test_large_finite_quantifier(tmp_path, quantifier, last, expected):
    # More terms than fit in the native stack when expanded into a left fold.
    # Isolate the process so a regression reports a failed check, not a killed
    # pytest suite. Both truth values depend on the last quantified object.
    count = 40000
    constants = ' '.join(f'c{i}' for i in range(count))
    domain = ('(define (domain d) (:requirements :hierarchy :adl) '
              f'(:constants {constants}) (:predicates (p ?x)) '
              f'(:action act :precondition ({quantifier} (?x) (p ?x)) '
              ':effect (and)))')
    true_objects = list(range(count - 1)) if quantifier == 'forall' else []
    if last:
        true_objects.append(count - 1)
    initial = ' '.join(f'(p c{i})' for i in true_objects)
    (tmp_path / 'domain.hddl').write_text(domain)
    (tmp_path / 'problem.hddl').write_text(
        '(define (problem p) (:domain d) (:htn :ordered-subtasks (act)) '
        f'(:init {initial}) (:goal (and)))')
    script = '''
import json, somtparser as sp, z3
result = sp.translate(path='domain.hddl', data=['problem.hddl'], language='hddl',
                      profile='bmc', options={'plan_horizon': '1', 'decomposition_depth': '1'})
assert result.ok, [d.message for d in result.diagnostics]
solver = z3.Solver()
solver.set(timeout=10000)
solver.add(z3.parse_smt2_string(result.to_smt2()))
print(json.dumps({'answer': str(solver.check())}))
'''
    env = os.environ.copy()
    env['PYTHONPATH'] = os.pathsep.join(str(Path(p).resolve()) for p in sys.path if p)
    completed = subprocess.run([sys.executable, '-c', script], cwd=tmp_path, env=env,
                               capture_output=True, text=True, timeout=60)
    assert completed.returncode == 0, completed.stderr
    assert json.loads(completed.stdout)['answer'] == expected
