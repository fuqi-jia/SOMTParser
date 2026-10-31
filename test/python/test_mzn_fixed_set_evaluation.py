"""MiniZinc fixed finite-set evaluation against the emitted SMT relation."""

import shutil
import subprocess

import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


def _translation(source):
    result = sp.translate(source=source, language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]
    return result


def _solve(result, extra=()):
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.set(timeout=5000)
    solver.add(*z3.parse_smt2_string(result.to_smt2(sp.OmtDialect.Z3), ctx=context))
    solver.add(*extra)
    status = solver.check()
    assert status != z3.unknown, solver.reason_unknown()
    return solver


def _cvc5_status(script):
    executable = shutil.which("cvc5")
    if executable is None:
        pytest.skip("cvc5 is required for the symbolic Set preservation check")
    if "(set-option :sets-exp true)" not in script:
        lines = script.splitlines()
        for i, line in enumerate(lines):
            if line.startswith("(set-logic "):
                lines.insert(i + 1, "(set-option :sets-exp true)")
                break
        else:
            lines.insert(0, "(set-option :sets-exp true)")
        script = "\n".join(lines) + "\n"
    result = subprocess.run(
        [executable, "--lang=smt2", "--arrays-exp", "--tlimit=5000"], input=script,
        text=True, capture_output=True, timeout=10,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    answers = [line for line in result.stdout.splitlines()
               if line in {"sat", "unsat", "unknown"}]
    assert len(answers) == 1 and answers[0] != "unknown", result.stdout + result.stderr
    return answers[0]


def test_official_is_dominated_fixed_set_array_equality_and_subset():
    source = """
int: numMatches = 2;
set of int: allMatches = 1..numMatches;
array[allMatches] of set of int: dataDefinedByMatch = [{1}, {1}];
function bool: is_dominated(int: m2) =
  dataDefinedByMatch[1] = dataDefinedByMatch[m2] /\\
  ((0..1) subset (0..1));
constraint forall(m in allMatches)(is_dominated(m));
solve satisfy;
"""
    assert _solve(_translation(source)).check() == z3.sat


def test_complete_set_operands_fold_with_union_intersection_and_difference():
    source = """
set of int: A = {1, 2};
array[1..1] of set of int: cells = [{1, 2}];
constraint A subset {1} union {2};
constraint A = {1} union {2};
constraint A = {1, 2, 3} diff {3};
constraint cells[1] subset {1} union {2};
constraint A subset ({1} union ({2} intersect {2, 3}));
solve satisfy;
"""
    assert _solve(_translation(source)).check() == z3.sat

    wrong_rhs = source.replace("A = {1} union {2};", "A = {1} union {3};")
    assert _solve(_translation(wrong_rhs)).check() == z3.unsat


@pytest.mark.parametrize("relation,expected", [
    ("1 in {1, 2} diff {2} intersect {2}", z3.sat),
    ("2 in {1} union {2} intersect {2}", z3.sat),
    ("1 in {1} union {2} diff {1}", z3.unsat),
    ("1 in {1} union {2} intersect {2}", z3.sat),
])
def test_set_operator_precedence_matches_mini_zinc(relation, expected):
    source = f"constraint {relation}; solve satisfy;"
    assert _solve(_translation(source)).check() == expected


@pytest.mark.parametrize("value, expected", [(0, "sat"), (1, "sat"), (2, "unsat"),
                                             (3, "sat"), (4, "sat"), (5, "unsat")])
def test_grouped_comprehension_union_and_difference_preserve_membership(value, expected):
    source = """
set of int: DAYS = 1..3;
set of int: XDAYS = 0..4;
var int: x;
constraint x in ({d | d in DAYS where d != 2} union (XDAYS diff DAYS));
""" + f"constraint x = {value}; solve satisfy;"
    assert _cvc5_status(_translation(source).to_smt2()) == expected


def test_grouped_symbolic_sets_preserve_union_intersection_precedence():
    source = """
var set of int: S;
constraint S = {1};
constraint 2 in ((S union {2}) intersect {2, 3});
constraint not (1 in ((S union {2}) intersect {2, 3}));
solve satisfy;
"""
    assert _cvc5_status(_translation(source).to_smt2()) == "sat"


def test_grouped_membership_keeps_large_fixed_intervals_compact():
    source = """
set of int: Huge = 1..1000000000;
var int: x;
constraint x in (Huge diff {1000000000} union {i | i in 1..0});
solve satisfy;
"""
    script = _translation(source).to_smt2(sp.OmtDialect.Z3)
    assert len(script) < 10000
    formula = z3.And(*z3.parse_smt2_string(script))
    x = z3.Int("x")
    solver = z3.Solver()
    solver.add(z3.Xor(formula, z3.And(x >= 1, x < 1000000000)))
    assert solver.check() == z3.unsat


def test_grouped_union_does_not_hide_an_undefined_set_operand():
    source = """
var int: z;
constraint not (1 in ({1} union {1 div z}));
constraint z = 0;
solve satisfy;
"""
    assert _cvc5_status(_translation(source).to_smt2()) == "sat"
    assert _cvc5_status(_translation(source.replace("z = 0", "z = 1")).to_smt2()) == "unsat"


@pytest.mark.parametrize("relation,expected", [
    ("A = {}", z3.sat),
    ("A subset {}", z3.sat),
    ("A = {}", z3.unsat),
])
def test_empty_enum_set_context_is_preserved(relation, expected):
    value = "{}" if expected == z3.sat else "{e0}"
    source = f"enum E = {{e0, e1}}; set of E: A = {value}; constraint {relation}; solve satisfy;"
    assert _solve(_translation(source)).check() == expected


def test_different_enum_set_element_types_are_rejected_even_when_one_is_empty():
    source = """
enum E = {e0, e1};
enum F = {f0, f1};
set of E: empty_E = {};
set of F: one_F = {f0};
constraint empty_E = one_F;
solve satisfy;
"""
    result = sp.translate(source=source, language="minizinc")
    assert not result.ok
    assert any(d.severity == sp.Severity.ERROR for d in result.diagnostic_items)


def test_decision_set_terms_remain_symbolic_instead_of_being_constant_folded():
    source = """
var set of int: decision_set;
constraint decision_set = {1};
constraint decision_set subset {1, 2};
solve satisfy;
"""
    result = _translation(source)
    smt = result.to_smt2(sp.OmtDialect.SmtLib2025)
    assert "set.subset" in smt
    assert "set.insert" in smt
    assert _cvc5_status(smt) == "sat"


@pytest.mark.parametrize("member, expected", [(4, "sat"), (5, "unsat")])
def test_decision_set_array_domain_has_exact_membership_boundary(member, expected):
    result = _translation(
        "array[2..3] of var set of 1..4: choices;"
        f"constraint {member} in choices[2]; solve satisfy;"
    )
    script = result.to_smt2()
    if expected == "sat":
        # Supply a complete witness, so proving satisfiability does not depend
        # on the solver discovering a model of quantified set-array domains.
        witness = "(assert (= choices ((as const (Array Int (Set Int))) (set.singleton 4))))"
        script = script.replace("(check-sat)", witness + "\n(check-sat)")
    assert _cvc5_status(script) == expected


@pytest.mark.parametrize("extra", ["1 in choices[1,1]", "not (2 in choices[1,1])"])
def test_set_array_slice_equality_excludes_extra_and_missing_members(extra):
    result = _translation(
        "array[1..2,1..2] of var set of 0..4: choices;"
        "array[1..2] of set of int: expected = [{0,2},{1,3}];"
        "constraint choices[1,..] = expected;"
        f"constraint {extra}; solve satisfy;"
    )
    assert _cvc5_status(result.to_smt2()) == "unsat"


@pytest.mark.parametrize("extra, expected", [("", "sat"), ("constraint 2 in choices[1];", "unsat")])
def test_empty_set_array_cell_has_no_members(extra, expected):
    result = _translation(
        "array[1..1] of var set of 0..3: choices;"
        "constraint choices[1] = {};" + extra + "solve satisfy;"
    )
    assert _cvc5_status(result.to_smt2()) == expected


@pytest.mark.parametrize("extra, expected", [("", "sat"), ("constraint 1 in s;", "unsat")])
def test_subset_of_empty_literal_forbids_every_member(extra, expected):
    result = _translation(
        "var set of int: s; constraint s subset {};" + extra + "solve satisfy;"
    )
    assert _cvc5_status(result.to_smt2()) == expected
