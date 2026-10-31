"""MiniZinc's emitted integer all-different alias preserves the full relation."""
import pytest
import somtparser as sp
import z3


def equivalent(source, expected, profile="default"):
    translated = sp.translate(
        source=source + "\nsolve satisfy;", language="flatzinc", profile=profile)
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    assert translated.report.fidelity.sound
    assert translated.report.fidelity.complete
    actual = z3.And(*z3.parse_smt2_string(translated.to_smt2()))
    solver = z3.Solver()
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


def guarded_relation(mode, relation):
    if mode == "_reif":
        return z3.Bool("b") == relation
    if mode == "_imp":
        return z3.Implies(z3.Bool("b"), relation)
    return relation


@pytest.mark.parametrize("items,truth", [
    ("[]", True), ("[4]", True), ("[4,4]", False),
    ("[4,6,4]", False), ("[4,6,-1]", True),
])
@pytest.mark.parametrize("mode", ["", "_reif", "_imp"])
def test_empty_singleton_and_literal_duplicates(items, truth, mode):
    source = "var bool: b;" if mode else ""
    source += (f"constraint fzn_all_different_int{mode}({items}"
               + (",b" if mode else "") + ");")
    equivalent(source, guarded_relation(mode, z3.BoolVal(truth)))


@pytest.mark.parametrize("profile", ["default", "ground", "quantified"])
@pytest.mark.parametrize("mode", ["", "_reif", "_imp"])
def test_variable_relation_matches_independent_distinct(profile, mode):
    x, y, z = z3.Ints("x y z")
    source = "var int: x; var int: y; var int: z;"
    source += "var bool: b;" if mode else ""
    source += (f"constraint fzn_all_different_int{mode}([x,y,z]"
               + (",b" if mode else "") + ");")
    equivalent(source, guarded_relation(mode, z3.Distinct(x, y, z)), profile)


@pytest.mark.parametrize("profile", ["default", "ground", "quantified"])
def test_false_reification_keeps_negation_of_entire_relation(profile):
    x, y, z = z3.Ints("x y z")
    equivalent("var int: x; var int: y; var int: z;"
               "constraint fzn_all_different_int_reif([x,y,z],false);",
               z3.Not(z3.Distinct(x, y, z)), profile)


def test_actual_challenge_alias_uses_pairwise_distinct():
    # Scope and call retained from Challenge 2025/fbd1/FBDk04.dzn's FlatZinc.
    # Unbounded scalar declarations isolate the exact global relation.
    names = [f"X_INTRODUCED_{i}_" for i in (
        16, 17, 18, 19, 36, 37, 38, 39, 40, 41, 28, 29, 30, 31, 32,
        33, 22, 23, 24, 25, 49, 50, 51, 52, 53, 54, 44, 45, 46)] + ["n_star"]
    source = "predicate fzn_all_different_int(array [int] of var int: x);\n"
    source += "\n".join(f"var int: {name};" for name in names)
    source += ("\narray [1..30] of var int: X_INTRODUCED_56_ = ["
               + ",".join(names) + "];\n"
               "constraint fzn_all_different_int(X_INTRODUCED_56_);")
    equivalent(source, z3.Distinct(*[z3.Int(name) for name in names]))


@pytest.mark.parametrize("mode", ["", "_reif", "_imp"])
def test_repeated_variable_alias_is_not_deduplicated(mode):
    source = "var int: x; var int: y; array [1..3] of var int: a = [x,y,x];"
    source += "var bool: b;" if mode else ""
    source += (f"constraint fzn_all_different_int{mode}(a"
               + (",b" if mode else "") + ");")
    equivalent(source, guarded_relation(mode, z3.BoolVal(False)))


def test_unrecognized_fzn_prefix_does_not_become_a_builtin():
    translated = sp.translate(
        source="var int: x; constraint fzn_int_eq(x,1); solve satisfy;",
        language="flatzinc")
    assert not translated.ok
    assert any("fzn_int_eq" in d.message for d in translated.diagnostic_items)
