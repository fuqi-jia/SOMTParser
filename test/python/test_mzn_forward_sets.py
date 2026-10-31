"""Forward fixed-set dependencies must retain source domains and nominal types."""
import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


def status(source):
    result = sp.translate(source=source, language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(z3.parse_smt2_string(result.to_smt2()))
    return solver.check()


@pytest.mark.parametrize("total,expected", [(3, "sat"), (6, "unsat")])
def test_forward_array_domain_preserves_every_cell(total, expected):
    source = (
        "array[S] of var 0..1: x;"
        f"constraint sum(i in S)(x[i]) = {total};"
        "set of int: S = lo..hi; int: hi=2; int: lo=-2; solve satisfy;"
    )
    assert str(status(source)) == expected


@pytest.mark.parametrize("length", [1, 8, 40])
def test_dependency_resolution_has_no_four_round_limit(length):
    source = "array[S0] of var 0..1: x; constraint sum(i in S0)(x[i])=3;"
    source += "".join(f"set of int: S{i}=S{i+1};" for i in range(length))
    source += f"set of int: S{length}=0..n0;"
    source += "".join(f"int: n{i}=n{i+1};" for i in range(length))
    source += f"int: n{length}=4; solve satisfy;"
    assert status(source) == z3.sat


def test_forward_enum_set_preserves_nominal_index_type():
    assert status(
        "enum E={A,B}; array[S] of var 0..1: x;"
        "constraint x[B]=1; set of E: S={A,B}; solve satisfy;"
    ) == z3.sat
    bad = sp.translate(
        source="enum E={A,B}; enum F={C,D}; array[S] of var int: x;"
               "constraint x[C]=1; set of E:S={A,B}; solve satisfy;",
        language="minizinc",
    )
    assert not bad.ok


@pytest.mark.parametrize("domain,value,accepted", [
    ("1..3", "{1,3}", True),
    ("1..3", "{0,3}", False),
    ("{1,3}", "{1,3}", True),
    ("{1,3}", "1..3", False),
    ("1..0", "{}", True),
    ("1..0", "{1}", False),
])
def test_finite_set_element_domains_check_holes_and_bounds(domain, value, accepted):
    result = sp.translate(
        source=f"set of D:S={value}; set of int:D={domain}; solve satisfy;",
        language="minizinc",
    )
    assert result.ok == accepted, [d.message for d in result.diagnostic_items]
    if not accepted:
        assert any("outside its element domain" in d.message for d in result.diagnostic_items)


def test_separate_data_assignment_obeys_declared_element_domain():
    assert status("set of 1..3:S; S={1,3}; solve satisfy;") == z3.sat
    result = sp.translate(source="set of 1..3:S; S={1,4}; solve satisfy;",
                          language="minizinc")
    assert not result.ok
    assert any("outside its element domain" in d.message for d in result.diagnostic_items)


@pytest.mark.parametrize("source", [
    "set of int:S={1}; set of int:S={2}; solve satisfy;",
    "set of int:S={1}; int:S=2; solve satisfy;",
    "array[S] of var int:x; set of int:S=T; set of int:T=S; solve satisfy;",
    "array[S] of var int:x; set of int:S=; solve satisfy;",
    "enum E={A,B}; enum F={C,D}; array[S] of var int:x;"
    "set of E:S={C,D}; solve satisfy;",
])
def test_bad_or_cyclic_declarations_remain_errors(source):
    result = sp.translate(source=source, language="minizinc")
    assert not result.ok


def test_empty_forward_domain_is_not_replaced_by_a_nonempty_default():
    assert status(
        "array[S] of var int:x; constraint sum(i in S)(x[i])=0;"
        "set of int:S=1..0; solve satisfy;"
    ) == z3.sat
    assert status(
        "array[S] of var int:x; constraint sum(i in S)(x[i])=1;"
        "set of int:S=1..0; solve satisfy;"
    ) == z3.unsat


def test_forward_sets_across_include_frames(tmp_path):
    included = tmp_path / "domains.mzn"
    included.write_text("set of int:S=0..n; int:n=2;")
    source = (
        "array[S] of var 0..1:x; constraint sum(i in S)(x[i])=3;"
        f'include "{included.as_posix()}"; solve satisfy;'
    )
    assert status(source) == z3.sat
