"""Exact distinct-count semantics and partiality for linear nvalue."""
import pytest
z3 = pytest.importorskip("z3")
import somtparser as sp


def _script(source):
    result = sp.translate(source=source, language="minizinc", dialect=sp.OmtDialect.Z3)
    assert result.ok, [d.message for d in result.diagnostic_items]
    return result.to_smt2(sp.OmtDialect.Z3)


def _check(source):
    solver = z3.Solver()
    solver.set(timeout=10000)
    solver.add(*z3.parse_smt2_string(_script(source)))
    return solver.check()


def test_complete_nvalue_relation_matches_pairwise_definition():
    source = """
array[1..5] of var int: x;
var int: c;
constraint c = nvalue(x);
solve satisfy;
"""
    actual = z3.And(*z3.parse_smt2_string(_script(source)))
    x = z3.Array("x", z3.IntSort(), z3.IntSort())
    c = z3.Int("c")
    indicators = [z3.If(z3.And(*[x[i] != x[j] for j in range(1, i)]), 1, 0)
                  for i in range(1, 6)]
    expected = c == z3.Sum(indicators)
    solver = z3.Solver()
    solver.set(timeout=10000)
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


def test_integer_duplicates_negative_and_large_values():
    prefix = "array[1..5] of int: x = [-7,-7,0,1000000000000,-7];\n"
    assert _check(prefix + "constraint nvalue(x) = 3; solve satisfy;\n") == z3.sat
    assert _check(prefix + "constraint nvalue(x) = 4; solve satisfy;\n") == z3.unsat


def test_enum_ordinals_count_repeated_members():
    prefix = "enum E = {a,b,c}; array[1..4] of E: x = [a,b,a,c];\n"
    assert _check(prefix + "constraint nvalue(x) = 3; solve satisfy;\n") == z3.sat
    assert _check(prefix + "constraint nvalue(x) = 2; solve satisfy;\n") == z3.unsat


def test_empty_integer_array_has_zero_distinct_values():
    source = "array[1..0] of int: x = []; constraint nvalue(x) = 0; solve satisfy;"
    assert _check(source) == z3.sat
    assert _check(source.replace("= 0", "= 1")) == z3.unsat


@pytest.mark.parametrize("op,negated,expected", [("=", False, z3.unsat), ("!=", False, z3.unsat), ("=", True, z3.sat)])
def test_duplicate_out_of_range_index_retains_partial_definedness(op, negated, expected):
    source = f"""
array[1..1] of int: a = [5];
var int: i;
constraint i = 2;
constraint {"not (" if negated else ""}nvalue([a[i], a[i]]) {op} 1{")" if negated else ""};
solve satisfy;
"""
    assert _check(source) == expected


@pytest.mark.parametrize("op,negated,expected", [("=", False, z3.unsat), ("!=", False, z3.unsat), ("=", True, z3.sat)])
def test_duplicate_undefined_division_retains_definedness(op, negated, expected):
    source = f"""
var int: d;
constraint d = 0;
constraint {"not (" if negated else ""}nvalue([1 div d, 1 div d]) {op} 1{")" if negated else ""};
solve satisfy;
"""
    assert _check(source) == expected


def test_reified_nvalue_constraint_has_both_polarities():
    source = """
array[1..3] of int: x = [-2,-2,4];
var bool: r;
constraint r <-> (nvalue(x) = 2);
constraint r;
solve satisfy;
"""
    assert _check(source) == z3.sat
    assert _check(source.replace("constraint r;", "constraint not r;")) == z3.unsat
