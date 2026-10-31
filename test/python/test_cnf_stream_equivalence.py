"""Independent SAT certificates cover full inputs and reject altered formulas."""
import hashlib
import importlib.util
import io
from pathlib import Path
import sys

import pytest


directory = Path(__file__).resolve().parents[2] / "tools/semantic_checks"
for name in ("wcnf_stream_equivalence", "cnf_stream_equivalence"):
    spec = importlib.util.spec_from_file_location(name, directory / (name + ".py"))
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
checker = module

SOURCE = b"c example\np cnf 3 3\n1\nc embedded comment\n-2 0 -1 2 0\n0\n"
TARGET = (b"(declare-const x1 Bool)\n(declare-const x2 Bool)\n(declare-const x3 Bool)\n"
          b"(assert (or x1 (not x2)))\n(assert (or (not x1) x2))\n"
          b"(assert false)\n(check-sat)\n(exit)\n")


def verify(source=SOURCE, target=TARGET):
    return checker.verify_streams(io.BytesIO(source), io.BytesIO(target))


def test_multiline_and_multiple_clauses_per_line_preserve_all_content():
    result = verify()
    assert result["feasibility_equivalent"]
    assert result["variables"] == result["clauses"] == result["hard_clauses"] == 3
    assert result["literals"] == 4 and result["soft_clauses"] == 0
    assert result["source_sha256"] == hashlib.sha256(SOURCE).hexdigest()
    assert result["target_sha256"] == hashlib.sha256(TARGET).hexdigest()
    assert result["counting_semantics"] == "not-checked"


@pytest.mark.parametrize("target", [
    TARGET.replace(b"(not x2)", b"x2"),
    TARGET.replace(b"(assert false)", b"(assert-soft false :weight 1)"),
    TARGET.replace(b"(assert false)", b"(assert (or))"),
    TARGET.replace(b"(assert false)\n", b""),
    TARGET.replace(b"(declare-const x3 Bool)\n", b""),
    TARGET + b"(assert false)\n",
])
def test_altered_target_fails(target):
    with pytest.raises(checker.VerificationError):
        verify(target=target)


@pytest.mark.parametrize("source", [
    SOURCE.replace(b"p cnf 3 3", b"p cnf 3 2"),
    SOURCE.replace(b"p cnf 3 3", b"p cnf 1 3"),
    SOURCE.replace(b"p cnf 3 3", b"p wcnf 3 3"),
    SOURCE + b"1\n",  # Do not silently drop an unfinished final clause.
    SOURCE.replace(b"-2 0", b"x 0"),
    SOURCE.replace(b"p cnf 3 3\n", b""),
    SOURCE + b"p cnf 0 0\n",
])
def test_invalid_source_fails(source):
    with pytest.raises(checker.VerificationError):
        verify(source=source)


def test_empty_conjunction_and_empty_clause_remain_distinct():
    assert verify(b"p cnf 0 0\n", b"(check-sat)\n")["clauses"] == 0
    assert verify(b"p cnf 0 1\n0\n", b"(assert false)\n")["clauses"] == 1
    with pytest.raises(checker.VerificationError):
        verify(b"p cnf 0 1\n0\n", b"(check-sat)\n")


def test_counting_directives_are_outside_the_boolean_certificate_claim():
    result = verify(b"c t pwmc\nc p weight 1 0.5 0\n" + SOURCE)
    assert result["has_counting_directives"]
    assert result["counting_semantics"] == "not-checked"
