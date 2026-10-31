"""TPTP ordinary names keep their meanings through SMT symbol encoding."""
import pytest
import somtparser as sp
import z3


def translate(source):
    return sp.translate(source=source, language="tptp")


@pytest.mark.parametrize("source, expected", [
    ("fof(a,axiom,true != false & abs(true) != true).", z3.sat),
    ("fof(a,axiom,~ true & $true).", z3.sat),
    ("fof(a,axiom,~ '$true' & $true).", z3.sat),
    ("fof(a,axiom,p & ~ 'p').", z3.unsat),
    ("fof(a,axiom,and(a,b) != or(a,b) & not(a) != a & ~p).", z3.sat),
    ("fof(a,axiom,and(a,b) != 'and'(a,b) & not(a) != a & ~p).", z3.unsat),
    ("tff(p_type,type,'$true':$o). tff(a,axiom,~ '$true' & $true).", z3.sat),
    ("tff(f_type,type,'$let':$i > $i). tff(a,axiom,'$let'(x) != x).", z3.sat),
    ("tff(s_type,type,'$i':$tType). tff(a_type,type,a:'$i'). "
     "tff(b_type,type,b:'$i'). tff(a,axiom,a != b).", z3.sat),
])
def test_ordinary_names_preserve_satisfiability(source, expected):
    result = translate(source)
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(z3.parse_smt2_string(result.to_smt2()))
    assert solver.check() == expected


@pytest.mark.parametrize("other_sort", ["$i", "'tptp$sort$2469'", "'_tptp_quoted_dollar_2469'"])
def test_quoted_individual_sort_cannot_alias_system_or_encoded_name(other_sort):
    result = translate(
        "tff(a_type,type,a:'$i'). "
        + "tff(b_type,type,b:" + other_sort + "). tff(a,axiom,a = b)."
    )
    assert not result.ok
    assert any("type" in str(d.code).lower() for d in result.diagnostic_items)


def test_ordinary_name_resembling_function_encoding_stays_independent():
    # This is the exact candidate target spelling for the ordinary source true.
    source = "fof(a,axiom,true != 'tptp$symbol$74727565$0')."
    result = translate(source)
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(z3.parse_smt2_string(result.to_smt2()))
    assert solver.check() == z3.sat
