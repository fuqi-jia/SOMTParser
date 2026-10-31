"""Server-only exercise of the same entry used for original corpus files."""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys
import z3

arguments = argparse.ArgumentParser()
arguments.add_argument('binary', type=Path)
arguments.add_argument('parent', type=Path)
arguments.add_argument('--models', type=Path)
arguments.add_argument('--dispatch-entry')
args = arguments.parse_args()
binary, parent = args.binary, args.parent
prefix = [str(binary)] + ([args.dispatch_entry] if args.dispatch_entry else [])
root = parent / 'public-driver'
root.mkdir()
examples = args.models or parent / 'joint_frontend_temporal'
domain = examples / 'duration_update.domain.pddl'
problem = examples / 'duration_update.problem.pddl'
target, report = root / 'duration.smt2', root / 'duration.json'
argv = [*prefix, str(domain), str(problem), '1',
        str(target), str(report), 'strict']
with (root / 'duration.stdout').open('xb') as stdout, (root / 'duration.stderr').open('xb') as stderr:
    completed = subprocess.run(argv, stdout=stdout, stderr=stderr)
assert completed.returncode == 0, completed.returncode
metadata = json.loads(report.read_text())
assert metadata['fidelity']['sound'] and not metadata['fidelity']['complete']
parsed = z3.Optimize()
parsed.from_file(str(target))
assert len(parsed.objectives()) == 1
solver = z3.Solver()
solver.add(*parsed.assertions())
assert solver.check() == z3.sat
solver.add(parsed.objectives()[0] != z3.RealVal('7/2'))
assert solver.check() == z3.unsat

# A rejected original input must retain diagnostics and report, and must
# never leave a success-shaped SMT artifact behind.
bad = root / 'wrong-domain.pddl'
bad.write_text(problem.read_text().replace('(:domain temporal)', '(:domain missing)'))
bad_target, bad_report = root / 'rejected.smt2', root / 'rejected.json'
rejected = subprocess.run([*prefix, str(domain), str(bad), '1',
                          str(bad_target), str(bad_report), 'lenient'], capture_output=True)
assert rejected.returncode == 2, (rejected.returncode, rejected.stderr)
assert not bad_target.exists() and bad_report.is_file()
json.loads(bad_report.read_text())
(root / 'rejected.stderr').write_bytes(rejected.stderr)
before = hashlib.sha256(target.read_bytes()).hexdigest()
overwrite = subprocess.run(argv, capture_output=True)
assert overwrite.returncode == 74
assert hashlib.sha256(target.read_bytes()).hexdigest() == before

# Lexically different paths can still name the same not-yet-created output.
# Reject them before writing the report or SMT, including through a directory
# symlink; a successful run must never replace its own JSON report with SMT.
alias_directory = root / 'output-alias'
alias_directory.symlink_to(root.resolve(), target_is_directory=True)
for name, alias in (
    ('dot', str(root) + '/./dot.json'),
    ('symlink', str(alias_directory / 'symlink.json')),
):
    same_output = root / (name + '.json')
    collision = subprocess.run([*prefix, str(domain), str(problem), '1',
                                str(same_output), alias, 'strict'], capture_output=True)
    assert collision.returncode == 64, (collision.returncode, collision.stderr)
    assert not same_output.exists(), same_output
(root / 'driver-verification.json').write_text(json.dumps({
    'passed': True, 'full_public_translation': True, 'complete_module_loaded': True,
    'exact_metric': '7/2', 'domain_mismatch_preserved': True,
    'overwrite_refused': True, 'aliased_output_refused': True, 'resource_limits': None,
}, indent=2) + '\n')
