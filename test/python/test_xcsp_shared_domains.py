"""Shared domain storage must not couple variables or lose exact membership."""
import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


def _relation(variables, constraints=""):
    result = sp.translate(
        source=(f'<instance format="XCSP3" type="CSP"><variables>{variables}'
                f'</variables><constraints>{constraints}</constraints></instance>'),
        language="xcsp3")
    assert result.ok, [d.message for d in result.diagnostic_items]
    return z3.And(*z3.parse_smt2_string(result.to_smt2()))


def _equivalent(actual, expected):
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


def test_sparse_array_and_domain_aliases_remain_independent_variables():
    actual = _relation(
        '<array id="a" size="[2]">-1 1</array>'
        '<var id="b" as="a"/><var id="c" as="b[1]"/>',
        '<intension>ne(a[0],b[0])</intension>')
    names = ["a[0]", "a[1]", "b[0]", "b[1]", "c"]
    _equivalent(actual, z3.And(
        *[z3.Or(z3.Int(n) == -1, z3.Int(n) == 1) for n in names],
        z3.Int("a[0]") != z3.Int("b[0]")))


def test_selector_domains_and_others_keep_exact_sets_after_assignment_consumption():
    actual = _relation(
        '<array id="x" size="[4]" startIndex="2">'
        '<domain for="x[2..3]">-2 0 2</domain>'
        '<domain for="x[4]">0..1</domain>'
        '<domain for="others">3 4 7</domain></array>'
        '<var id="z" as="x[5]"/>',
        '<extension><list>x[2] x[5]</list>'
        '<supports>(*,7)(0,*)</supports></extension>')
    domains = {"x[2]": [-2, 0, 2], "x[3]": [-2, 0, 2],
               "x[4]": [0, 1], "x[5]": [3, 4, 7], "z": [3, 4, 7]}
    _equivalent(actual, z3.And(
        *[z3.Or(*[z3.Int(n) == v for v in members])
          for n, members in domains.items()],
        z3.Or(z3.Int("x[5]") == 7, z3.Int("x[2]") == 0)))


@pytest.mark.parametrize("domains, message", [
    ('<domain for="x[0..1]">0..1</domain>'
     '<domain for="x[1]">2..3</domain>', "more than one domain"),
    ('<domain for="others">0..1</domain>'
     '<domain for="x[0]">2..3</domain>', "once and last"),
])
def test_sharing_preserves_selector_errors(domains, message):
    result = sp.translate(
        source=('<instance format="XCSP3" type="CSP"><variables>'
                f'<array id="x" size="[2]">{domains}</array>'
                '</variables></instance>'), language="xcsp3")
    assert not result.ok
    assert any(message in d.message for d in result.diagnostic_items)
