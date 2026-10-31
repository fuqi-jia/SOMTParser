"""Actual CRIL d4 counts through the public DIMACS/SMT-to-CNF API."""
import pytest
import somtparser as sp

pytestmark = pytest.mark.skipif(sp.backend_path("d4") is None, reason="d4 unavailable")


@pytest.mark.parametrize("source,expected", [
    ("p cnf 0 0\n", 1),
    ("p cnf 2 1\n1 2 0\n", 3),
    ("p cnf 1 2\n1 0\n-1 0\n", 0),
    ("p cnf 3 1\n1 0\n", 4),
    ("p cnf 2 2\n1 2 0\n1 2 0\n", 3),
    ("p cnf 80 1\n1 0\n", 2**79),
])
def test_d4_default_invocation_returns_exact_target_count(source, expected):
    result = sp.read(source=source, language="dimacs").to("d4").count(scope="target")
    assert result.count == expected, result


def test_d4_counts_tseitin_extensions_and_unused_source_booleans_once():
    source = ("(set-logic QF_UF)(declare-const a Bool)(declare-const b Bool)"
              "(declare-const c Bool)(declare-const unused Bool)"
              "(assert (or a (and b c)))")
    formula = sp.read(source=source, language="smtlib2").to("d4")
    assert formula.count(scope="target").count == 10
    assert formula.count(scope="target").count == 10
