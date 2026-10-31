"""Whole-model XOR checks for disjoint interval table-label factoring."""
import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


def _member(variable, domain):
    return z3.Or(*[variable == value for value in domain])


def _check_interval_union(domain, domain_values, values, polarity):
    rows = "".join(f"({value},1,0)" for value in values)
    domain_text = domain if isinstance(domain, str) else " ".join(map(str, domain))
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              f'<var id="x">{domain_text}</var><var id="y">0..1</var>'
              '<var id="z">0..1</var></variables><constraints><extension>'
              '<list>x y z</list><' + polarity + '>' + rows + '</' + polarity
              + '></extension></constraints></instance>')
    result = sp.translate(source=source, language="xcsp3")

    x, y, z = z3.Ints("x y z")
    x_domain = (z3.And(x >= int(domain.split("..")[0]),
                       x <= int(domain.split("..")[1]))
                if isinstance(domain, str) else _member(x, domain_values))
    relation = z3.And(z3.Or(*[x == value for value in values]), y == 1, z == 0)
    expected = z3.And(x_domain, y >= 0, y <= 1, z >= 0, z <= 1,
                      relation if polarity == "supports" else z3.Not(relation))
    assert result.ok, [diagnostic.message for diagnostic in result.diagnostic_items]
    emitted = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    solver = z3.Solver()
    solver.add(z3.Xor(emitted, expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("polarity", ["supports", "conflicts"])
@pytest.mark.parametrize("domain,domain_values", [
    ("-20..20", None),
    ([-12, -11, -10, -9, -8, 3, 4, 6, 7, 15],
     [-12, -11, -10, -9, -8, 3, 4, 6, 7, 15]),
])
def test_two_dense_runs_and_sparse_outlier_are_exact(polarity, domain, domain_values):
    # The table suffix is shared by every row. Its first-column labels are two
    # intervals and one singleton; the sparse domain case excludes 5 from the
    # middle interval, so equivalence depends on the global domain constraint.
    values = [-12, -11, -10, -9, -8, 3, 4, 5, 6, 15]
    _check_interval_union(domain, domain_values, values, polarity)
