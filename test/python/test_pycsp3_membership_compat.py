"""Exercise the real PyCSP3 exporter and compare complete projected relations."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

import pytest

from tools.pycsp3_membership_compat import normalize_scalar_membership


def test_no_membership_is_byte_identical():
    source = '"""model docs"""\nfrom __future__ import annotations\nx = [1, 2]\n'
    result = normalize_scalar_membership(source)
    assert result.source == source
    assert result.original_sha256 == result.transformed_sha256
    assert result.edits == ()


def test_recorded_edit_preserves_comments_unicode_and_future_imports():
    source = ('"""测试模型"""\nfrom __future__ import annotations\n'
              '_somt_pycsp3_scalar_membership = 17\n'
              'flag = 1 in {1, 2}  # ordinary membership remains Boolean\n'
              '标记 = True; answer = x not in [1, 2]\n')
    result = normalize_scalar_membership(source)
    assert '# ordinary membership remains Boolean' in result.source
    assert '_somt_pycsp3_scalar_membership = 17' in result.source
    assert 'def _somt_pycsp3_scalar_membership_(' in result.source
    assert result.source.index('from __future__') < result.source.index('def _somt')
    assert len(result.edits) == 1  # numeric literals need no CP dispatch
    assert result.edits[0]['original'] == 'x not in [1, 2]'


def test_tuple_table_chained_and_overlapping_memberships_are_not_rewritten():
    source = ('a = (x, y) in table\nb = lo < x in values\n'
              'c = x in [y in domain]\n')
    assert normalize_scalar_membership(source).source == source


@pytest.mark.parametrize('negative', [False, True])
@pytest.mark.parametrize('members', ['{1, 2}', 'range(1, 3)', '[]'])
def test_composed_membership_preserves_all_observable_assignments(negative, members, tmp_path):
    if importlib.util.find_spec('pycsp3') is None:
        pytest.skip('pycsp3 reference exporter is not installed')
    z3 = pytest.importorskip('z3')
    import somtparser as sp
    operator = 'not in' if negative else 'in'
    source = ('from pycsp3 import *\n'
              'x = Var(dom=range(4))\ny = Var(dom=range(2))\nb = Var(dom=range(2))\n'
              'plain_values = [i for i in range(4) if i not in {0, 3}]\n'
              'assert plain_values == [1, 2]\n'
              f'satisfy(b == conjunction(x {operator} {members}, y == 0, True))\n')
    result = normalize_scalar_membership(source)
    (tmp_path/'original.py').write_text(source)
    model = tmp_path/'model.py'
    model.write_text(result.source)
    xml = tmp_path/'reference.xml'
    (tmp_path/'edits.json').write_text(json.dumps(result.edits, indent=2))
    exported = subprocess.run([sys.executable, str(model), '-output=' + str(xml)],
                              cwd=tmp_path, capture_output=True, text=True)
    assert exported.returncode == 0 and xml.exists(), exported.stdout + exported.stderr
    translated = sp.translate(path=str(xml), language='xcsp3', dialect=sp.OmtDialect.Z3)
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    actual = z3.And(*z3.parse_smt2_string(translated.to_smt2(dialect=sp.OmtDialect.Z3)))
    x, y, b = z3.Ints('x y b')
    membership = z3.BoolVal(False) if members == '[]' else z3.Or(x == 1, x == 2)
    if negative:
        membership = z3.Not(membership)
    expected = z3.And(x >= 0, x <= 3, y >= 0, y <= 1, b >= 0, b <= 1,
                      b == z3.If(z3.And(membership, y == 0), 1, 0))
    # PyCSP3 may introduce helper scalars; those are existential witnesses.
    from z3.z3util import get_vars
    private = [value for value in get_vars(actual) if str(value) not in {'x', 'y', 'b'}]
    projected = z3.Exists(private, actual) if private else actual
    solver = z3.Solver()
    solver.add(z3.Xor(projected, expected))
    assert solver.check() == z3.unsat
