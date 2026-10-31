"""Independent relation checks for arithmetic-progression table factoring."""
import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


def _check_progression(domain, values, polarity="supports"):
    rows = "".join(f"({value},1,0)" for value in values)
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              f'<var id="x">{domain}</var><var id="y">0..1</var>'
              '<var id="z">0..1</var></variables><constraints><extension>'
              '<list>x y z</list><' + polarity + '>' + rows
              + '</' + polarity + '></extension></constraints></instance>')
    result = sp.translate(source=source, language="xcsp3")
    x, y, z = z3.Ints("x y z")
    if ".." in domain:
        low, high = map(int, domain.split(".."))
        x_domain = z3.And(x >= low, x <= high)
    else:
        domain_values = list(map(int, domain.split()))
        x_domain = z3.Or(*[x == v for v in domain_values])
    relation = z3.And(z3.Or(*[x == v for v in values]), y == 1, z == 0)
    expected = z3.And(x_domain, y >= 0, y <= 1, z >= 0, z <= 1,
                      relation if polarity == "supports" else z3.Not(relation))
    assert result.ok, [d.message for d in result.diagnostic_items]
    emitted = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    solver = z3.Solver()
    solver.add(z3.Xor(emitted, expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("polarity", ["supports", "conflicts"])
def test_shared_suffix_factors_a_negative_arithmetic_progression(polarity):
    _check_progression("-10..15", [-8, -4, 0, 4, 8, 12], polarity)


def test_progression_step_and_offset_do_not_overflow_signed_endpoints():
    low = -(1 << 63)
    step = 3_000_000_000_000_000_000
    values = [low + step * i for i in range(6)]
    assert values[-1] <= (1 << 63) - 1
    _check_progression(f"{low}..{(1 << 63) - 1}", values)


def test_non_progression_shared_suffix_keeps_exact_equality_fallback():
    _check_progression("-10..10", [-8, -3, 1, 7])


def test_progression_labels_covering_sparse_domain_need_no_local_guard():
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              '<var id="x">0 2 4 6</var><var id="y">0..1000000000</var>'
              '</variables><constraints><extension><list>x y</list>'
              '<supports>(0,1)(2,1)(4,1)(6,1)</supports>'
              '</extension></constraints></instance>')
    result = sp.translate(source=source, language="xcsp3")
    x, y = z3.Ints("x y")
    expected = z3.And(z3.Or(x == 0, x == 2, x == 4, x == 6),
                      y >= 0, y <= 1_000_000_000, y == 1)
    assert result.ok, [d.message for d in result.diagnostic_items]
    emitted = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    solver = z3.Solver()
    solver.add(z3.Xor(emitted, expected))
    assert solver.check() == z3.unsat
