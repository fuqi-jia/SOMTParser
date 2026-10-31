"""Allocation failure is a resource diagnostic, not an internal parser error."""
import os
import subprocess
import sys

import pytest


@pytest.mark.skipif(sys.platform != "linux", reason="requires Linux RLIMIT_AS")
@pytest.mark.parametrize("language,source", [
    ("dimacs", "p cnf 20000000 1\n1 0\n"),
    ("wcnf", "p wcnf 20000000 1 10\n1 1 0\n"),
])
def test_large_declaration_domain_reports_resource_exhaustion(language, source):
    code = '''
import json, resource, sys
import somtparser as sp
resource.setrlimit(resource.RLIMIT_AS, (512 * 1024**2,) * 2)
result = sp.translate(language=sys.argv[1], source=sys.argv[2], options={"packed": "0"})
assert not result.ok
assert any(d.code == sp.ErrorCode.E_RESOURCE for d in result.diagnostic_items), [d.message for d in result.diagnostic_items]
assert all(d.code != sp.ErrorCode.E_INTERNAL for d in result.diagnostic_items)
'''
    completed = subprocess.run([sys.executable, "-c", code, language, source],
                               env=os.environ.copy(), capture_output=True, text=True, timeout=30)
    assert completed.returncode == 0, completed.stdout + completed.stderr
