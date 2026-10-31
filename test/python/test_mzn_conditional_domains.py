"""Conditional simplification preserves values and branch-local partiality."""
import json

import pytest
import z3

import somtparser as sp


def _equivalent(source, expected, **kwargs):
    result = sp.translate(source=source + "solve satisfy;", language="minizinc", **kwargs)
    assert result.ok, [d.message for d in result.diagnostic_items]
    actual = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    check = z3.Solver()
    check.set(timeout=10000)
    check.add(z3.Xor(actual, expected))
    assert check.check() == z3.unsat


def test_repeated_record_conditionals_preserve_complete_sum_relation(tmp_path):
    data = tmp_path / "rows.json"
    rows = [{"yes": i, "no": -i} for i in range(1, 25)]
    data.write_text(json.dumps({"rows": rows}), encoding="utf-8")
    b, c = z3.Bools("b c")
    expected = z3.Int("total") == sum(
        z3.If(b, row["yes"], z3.If(c, row["no"], 0)) for row in rows)
    _equivalent("""
type Row = record(int: yes, int: no);
list of Row: rows;
var bool: b; var bool: c; var int: total;
constraint total = sum(row in rows)(if b then row.yes
  else if c then row.no else 0 endif endif);
""", expected, data=[str(data)])


@pytest.mark.parametrize("negated", [False, True])
def test_partial_branch_domain_is_only_required_when_selected(negated):
    b = z3.Bool("b")
    i, value = z3.Ints("i value")
    inside = z3.And(i >= 1, i <= 2)
    relation = z3.And(z3.Or(z3.Not(b), inside),
                      value == z3.If(b, z3.If(i == 1, 3, 5), 7))
    expression = "(if b then a[i] else 7 endif) = value"
    if negated:
        expression = f"not ({expression})"
        relation = z3.Not(relation)
    _equivalent("array[1..2] of int: a = [3,5];"
                "var bool: b; var int: i; var int: value;"
                f"constraint {expression};", relation)
