"""MiniZinc `count` verdict tests -- the decomposition's MEANING, not its shape.

`count(x, y, c)` constrains c to be the number of elements of x equal to y
(MiniZinc stdlib). DecomposeGlobalsPass encodes that as a sum of indicators,
`c = sum_i ite(x_i = y, 1, 0)`, which is exact -- so the property to pin is
arithmetic, not textual: with the array fixed, exactly one value of c is
satisfiable, and every other value is not.

A structural test cannot see this. `(+ (ite ...) (ite ...) (ite ...))` has the
right shape whether the indicators compare against the sought value or against
each other, whether they yield 1/0 or 0/1, and whether one term was dropped.
Each of those is a different count and the same text pattern. Solving is what
separates them.

The encoding is also the SAME under every profile, because there is only one:
a quantified form would need a cardinality operator the HIR does not have. The
last case below pins that rather than leaving it assumed.
"""

import pytest

z3 = pytest.importorskip("z3")

import somtparser as sp


def _model(body, profile="default"):
    t = sp.translate(source=body, language="minizinc", profile=profile)
    assert t.ok, t.diagnostic_items[0].message if t.diagnostic_items else "no model"
    return t.to_smt2()


def _check(body, profile="default"):
    solver = z3.Solver()
    solver.from_string(_model(body, profile))
    return solver.check()


# Three fixed cells, two of them zero. `c` is then pinned to 2 and to nothing
# else -- the base property, asserted from both sides so a decomposition that
# merely BOUNDS the count cannot pass.
_FIXED = (
    "array[1..3] of var 0..9: x;\n"
    "var int: c;\n"
    "constraint x[1] = 0;\n"
    "constraint x[2] = 0;\n"
    "constraint x[3] = 5;\n"
    "constraint count([x[i] | i in 1..3], 0, c);\n"
)


@pytest.mark.parametrize("claim,expected", [
    ("constraint c = 2;\nsolve satisfy;\n", z3.sat),
    ("constraint c = 1;\nsolve satisfy;\n", z3.unsat),
    ("constraint c = 3;\nsolve satisfy;\n", z3.unsat),
    ("constraint c = 0;\nsolve satisfy;\n", z3.unsat),
])
def test_count_is_the_number_of_occurrences(claim, expected):
    assert _check(_FIXED + claim) == expected


def test_count_of_a_value_that_does_not_occur_is_zero():
    # An occurrence count is not "at least one": a sought value absent from
    # every cell gives 0, and a decomposition that conflated the two would
    # make this unsat.
    source = (
        "array[1..3] of var 0..9: x;\n"
        "var int: c;\n"
        "constraint x[1] = 1;\n"
        "constraint x[2] = 2;\n"
        "constraint x[3] = 3;\n"
        "constraint count([x[i] | i in 1..3], 7, c);\n"
        "constraint c = 0;\n"
        "solve satisfy;\n"
    )
    assert _check(source) == z3.sat


def test_count_over_an_empty_comprehension_is_zero():
    # `count` over no terms is `c = 0`, not an error and not unconstrained.
    source = (
        "array[1..3] of var 0..9: x;\n"
        "var int: c;\n"
        "constraint count([x[i] | i in 1..0], 0, c);\n"
        "constraint c != 0;\n"
        "solve satisfy;\n"
    )
    assert _check(source) == z3.unsat


def test_count_constrains_the_array_not_only_the_count():
    # The constraint runs both ways. Demanding three zeros in a three-cell
    # array forces every cell, so asserting a nonzero cell is unsat. A
    # decomposition that only computed `c` from `x` -- rather than relating
    # them -- would leave this satisfiable.
    source = (
        "array[1..3] of var 0..9: x;\n"
        "var int: c;\n"
        "constraint count([x[i] | i in 1..3], 0, c);\n"
        "constraint c = 3;\n"
        "constraint x[2] = 4;\n"
        "solve satisfy;\n"
    )
    assert _check(source) == z3.unsat


def test_indexed_and_list_shapes_agree():
    # `count(x, y, c)` over a declared array reaches the global's INDEXED
    # shape and `count([x[i] | ...], y, c)` reaches the LIST shape. They are
    # the same constraint, so the two must accept and refuse the same values
    # -- a differential check across the shape split, which is where a
    # decomposition is most likely to disagree with itself.
    common = (
        "array[1..3] of var 0..9: x;\n"
        "var int: c;\n"
        "constraint x[1] = 0;\n"
        "constraint x[2] = 0;\n"
        "constraint x[3] = 5;\n"
    )
    indexed = common + "constraint count(x, 0, c);\n"
    listed = common + "constraint count([x[i] | i in 1..3], 0, c);\n"
    for claim, expected in (("constraint c = 2;\nsolve satisfy;\n", z3.sat),
                            ("constraint c = 1;\nsolve satisfy;\n", z3.unsat)):
        assert _check(indexed + claim) == expected
        assert _check(listed + claim) == expected


def test_one_encoding_under_every_profile():
    # alldifferent has a ground and a quantified encoding and the profile
    # picks between them. count has ONE, so the emitted script must not vary
    # -- and asserting that here is what stops a later "quantified count" from
    # being claimed in the report without being built.
    source = _FIXED + "solve satisfy;\n"
    ground = _model(source, "ground")
    quantified = _model(source, "quantified")
    assert ground == quantified
