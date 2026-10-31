"""Open GCC semantics from Savile Row manual Table 1 (arXiv:2201.03472)."""
import pytest
import somtparser as sp
import z3


def translated(declarations, constraint):
    result = sp.translate(source="language ESSENCE' 1.0\n" + declarations +
                          "\nsuch that " + constraint, language="essence")
    assert result.ok, [d.message for d in result.diagnostic_items]
    assert result.report.fidelity.sound and result.report.fidelity.complete
    return z3.And(list(z3.parse_smt2_string(result.to_smt2())))


def equivalent(actual, expected):
    check = z3.Solver()
    check.add(z3.Xor(actual, expected))
    assert check.check() == z3.unsat


@pytest.mark.parametrize("constraint,expected,satisfiable", [
    ("gcc([x,y,x], [1], [c])", lambda x, y, c: c == 2*z3.If(x == 1, 1, 0) + z3.If(y == 1, 1, 0), True),
    ("!gcc([x,y,x], [1], [c])", lambda x, y, c: c != 2*z3.If(x == 1, 1, 0) + z3.If(y == 1, 1, 0), True),
    ("gcc([x,y], [1,1], [c,1])", lambda x, y, c: z3.And(c == 1, z3.If(x == 1, 1, 0) + z3.If(y == 1, 1, 0) == 1), True),
    ("gcc([x], [1,1], [1,1])", lambda x, y, c: x == 1, True),
    ("gcc([x], [1,1], [0,1])", lambda x, y, c: z3.BoolVal(False), False),
    ("gcc([x,y], [], [])", lambda x, y, c: z3.BoolVal(True), True),
    ("gcc([], [1,2], [c,0])", lambda x, y, c: c == 0, True),
    ("gcc([], [1], [-1])", lambda x, y, c: z3.BoolVal(False), False),
    ("gcc([x,y], [1+1], [c+1])", lambda x, y, c: c + 1 == z3.If(x == 2, 1, 0) + z3.If(y == 2, 1, 0), True),
])
def test_open_cardinality_matches_full_relation(constraint, expected, satisfiable):
    actual = translated("find x,y : int(0..2)\nfind c : int(-1..3)", constraint)
    x, y, c = z3.Ints("x y c")
    equivalent(actual, z3.And(x >= 0, x <= 2, y >= 0, y <= 2,
                              c >= -1, c <= 3, expected(x, y, c)))
    witness = z3.Solver()
    witness.add(actual)
    assert witness.check() == (z3.sat if satisfiable else z3.unsat)


def test_named_matrices_and_comprehensions_preserve_occurrence_order():
    actual = translated("letting values = [2,1; int(-1..0)]\n"
                        "find a : matrix indexed by [int(3..4)] of int(0..2)\n"
                        "find c : matrix indexed by [int(-2..-1)] of int(0..2)",
                        "gcc([a[i] | i : int(3..4)], values, c)")
    a = z3.Array("a", z3.IntSort(), z3.IntSort())
    c = z3.Array("c", z3.IntSort(), z3.IntSort())
    domain = [z3.And(v >= 0, v <= 2) for v in [a[3], a[4], c[-2], c[-1]]]
    equivalent(actual, z3.And(*domain,
        c[-2] == z3.If(a[3] == 2, 1, 0) + z3.If(a[4] == 2, 1, 0),
        c[-1] == z3.If(a[3] == 1, 1, 0) + z3.If(a[4] == 1, 1, 0)))


@pytest.mark.parametrize("negated", [False, True])
def test_symbolic_slice_partiality_stays_inside_boolean_context(negated):
    actual = translated("find a : matrix indexed by [int(1..2), int(1..2)] of int(0..2)\n"
                        "find i : int(0..3)",
                        ("!" if negated else "") + "gcc(a[i,..], [1], [1])")
    a = z3.Array("a", z3.IntSort(), z3.IntSort())
    i = z3.Int("i")
    predicate = z3.And(i >= 1, i <= 2,
        z3.If(a[(i-1)*2] == 1, 1, 0) + z3.If(a[(i-1)*2+1] == 1, 1, 0) == 1)
    equivalent(actual, z3.And(i >= 0, i <= 3,
        *[z3.And(a[k] >= 0, a[k] <= 2) for k in range(4)],
        z3.Not(predicate) if negated else predicate))


def test_boolean_targets_and_reified_count():
    actual = translated("find a,b,accepted : bool", "accepted = gcc([a,b], [true], [1])")
    a, b, accepted = z3.Bools("a b accepted")
    equivalent(actual, accepted == z3.Xor(a, b))


@pytest.mark.parametrize("negated", [False, True])
def test_constant_parameter_row_slice_uses_source_indices(tmp_path, negated):
    data = tmp_path / "counts.param"
    data.write_text("letting counts = [[1,2], [2,0]]")
    result = sp.translate(source="language ESSENCE' 1.0\n"
        "given counts : matrix indexed by [int(-1..0), int(3..4)] of int(0..3)\n"
        "find a : matrix indexed by [int(1..3)] of int(0..2)\nfind row : int(-2..1)\n"
        "such that " + ("!" if negated else "") + "gcc(a, [0,1], counts[row,..])",
        data=[str(data)], language="essence")
    assert result.ok, [d.message for d in result.diagnostic_items]
    actual = z3.And(list(z3.parse_smt2_string(result.to_smt2())))
    a = z3.Array("a", z3.IntSort(), z3.IntSort())
    row = z3.Int("row")
    zeros = z3.Sum([z3.If(a[i] == 0, 1, 0) for i in range(1, 4)])
    ones = z3.Sum([z3.If(a[i] == 1, 1, 0) for i in range(1, 4)])
    predicate = z3.Or(z3.And(row == -1, zeros == 1, ones == 2),
                      z3.And(row == 0, zeros == 2, ones == 0))
    equivalent(actual, z3.And(row >= -2, row <= 1,
        *[z3.And(a[i] >= 0, a[i] <= 2) for i in range(1, 4)],
        z3.Not(predicate) if negated else predicate))


def test_constant_column_slice_preserves_row_order_and_repeated_coverage():
    actual = translated("letting P = [[1,9; int(3..4)], [1,8; int(3..4)]; int(-1..0)]\n"
                        "find x : int(0..2)", "gcc([x], P[..,3], [1,1])")
    equivalent(actual, z3.Int("x") == 1)


def test_constant_boolean_slice_closes_invalid_cells_before_integer_coercion():
    actual = translated("letting P = [[true,false]]\nfind row : int(0..2)",
                        "gcc(P[row,..], [1], [0])")
    row = z3.Int("row")
    # An undefined Boolean cell is false before Bool-to-Int conversion.
    equivalent(actual, z3.Or(row == 0, row == 2))


def test_constant_slice_survives_its_name_being_shadowed_in_subscript():
    actual = translated("letting P = [[1,2], [3,4]]",
                        "sum(P[(sum P : int(1..1) . P),..]) = 3")
    equivalent(actual, z3.BoolVal(True))


@pytest.mark.parametrize("constraint,diagnostic", [
    ("gcc([x], [1,2], [1])", "equal lengths"),
    ("gcc([x], [x], [1])", "non-decision"),
    ("gcc([x], [1])", "expected ','"),
])
def test_bad_cardinality_arguments_report_the_specific_error(constraint, diagnostic):
    result = sp.translate(source="language ESSENCE' 1.0\nfind x : int(0..2)\nsuch that " + constraint,
                          language="essence")
    assert not result.ok
    assert any(diagnostic in item.message for item in result.diagnostic_items)
