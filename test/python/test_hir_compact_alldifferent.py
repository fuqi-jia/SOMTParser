"""Shared allDifferent lowering preserves relation and avoids quadratic output."""
import pytest
import z3
import somtparser as sp
from somtparser.hir import HirBuilder


@pytest.mark.parametrize("profile", ["default", "ground", "quantified"])
@pytest.mark.parametrize("negated", [False, True])
def test_explicit_terms_match_pair_relation_in_both_polarities(profile, negated):
    builder = HirBuilder()
    names = [f"x{i}" for i in range(24)]
    for name in names:
        builder.declare(name, "Int")
    distinct = {"op": "all_different", "args": [{"var": n} for n in names]}
    builder.constrain({"op": "not", "args": [distinct]} if negated else distinct)
    result = builder.translate(profile=profile)
    assert result.ok, [d.message for d in result.diagnostic_items]
    values = [z3.Int(name) for name in names]
    expected = z3.And(*[a != b for i, a in enumerate(values) for b in values[i + 1:]])
    if negated:
        expected = z3.Not(expected)
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(z3.Xor(z3.And(*z3.parse_smt2_string(result.to_smt2())), expected))
    assert solver.check() == z3.unsat


def test_large_finite_array_has_linear_translation_size():
    builder = HirBuilder()
    builder.declare("cells", "Int", shape=[5000])
    builder.constrain({"op": "all_different", "args": [{"var": "cells"}]})
    result = builder.translate()
    assert result.ok, [d.message for d in result.diagnostic_items]
    script = result.to_smt2()
    # An independent parser accepts the large result without solving it. This
    # budget catches construction of millions of pairs before solver search.
    assert len(script) < 1_000_000
    assert len(z3.parse_smt2_string(script)) > 0


@pytest.mark.parametrize("profile", ["default", "ground", "quantified"])
def test_indexed_array_preserves_nonzero_start_and_half_open_extent(profile):
    result = sp.translate(
        source="array[-2..1] of var int: a; constraint alldifferent(a); solve satisfy;",
        language="minizinc", profile=profile)
    assert result.ok, [d.message for d in result.diagnostic_items]
    a = z3.Array("a", z3.IntSort(), z3.IntSort())
    expected = z3.And(*[a[i] != a[j] for i in range(-2, 2) for j in range(i + 1, 2)])
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(z3.Xor(z3.And(*z3.parse_smt2_string(result.to_smt2())), expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("sort", ["Int", "Real", "(_ BitVec 8)", "String", "Bool", "(Array Int Int)"])
@pytest.mark.parametrize("operator", ["distinct", "="])
def test_nary_comparison_negation_preserves_source_relation(sort, operator):
    source = ''.join(f'(declare-const {v} {sort})\n' for v in ('a', 'b', 'c'))
    source += f'(assert (not ({operator} a b c)))\n(check-sat)\n'
    result = sp.translate(source=source, language="smtlib2")
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(z3.Xor(z3.And(*z3.parse_smt2_string(source)),
                      z3.And(*z3.parse_smt2_string(result.to_smt2()))))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("operator", ["=", "distinct"])
def test_boolean_comparison_constants_and_complements(operator):
    import itertools
    atoms = ["true", "false", "a", "b", "(not a)", "(not b)"]
    for arity in [2, 3]:
        for operands in itertools.product(atoms, repeat=arity):
            source = ('(declare-const a Bool)(declare-const b Bool)'
                      f'(assert ({operator} ' + ' '.join(operands) + '))(check-sat)')
            result = sp.translate(source=source, language="smtlib2")
            assert result.ok, [d.message for d in result.diagnostic_items]
            solver = z3.Solver()
            solver.set(timeout=5000)
            solver.add(z3.Xor(z3.And(*z3.parse_smt2_string(source)),
                              z3.And(*z3.parse_smt2_string(result.to_smt2()))))
            assert solver.check() == z3.unsat, (operator, operands, result.to_smt2())


@pytest.mark.parametrize("language", ["essence", "minizinc", "flatzinc"])
def test_frontends_keep_every_cell_in_shared_distinct(language):
    if language == "essence":
        source = ("language ESSENCE' 1.0\n"
                  "find q: matrix indexed by [int(1..2), int(1..3)] of int(0..9)\n"
                  "such that allDiff(q)\n")
        q = z3.Array("q", z3.IntSort(), z3.IntSort())
        terms = [q[i] for i in range(6)]
        bounds = [z3.And(t >= 0, t <= 9) for t in terms]
    elif language == "minizinc":
        source = "array[1..2,1..3] of var int: a; constraint alldifferent(a); solve satisfy;"
        a = z3.Array("a", z3.IntSort(), z3.IntSort())
        terms, bounds = [a[i] for i in range(6)], []
    else:
        source = ("array [1..3] of var 1..3: q = [q1,q2,q3];\n"
                  "var 1..3: q1; var 1..3: q2; var 1..3: q3;\n"
                  "constraint all_different_int(q); solve satisfy;\n")
        terms = z3.Ints("q1 q2 q3")
        bounds = [z3.And(t >= 1, t <= 3) for t in terms]
    result = sp.translate(source=source, language=language)
    assert result.ok, [d.message for d in result.diagnostic_items]
    expected = z3.And(*(bounds + [a != b for i, a in enumerate(terms) for b in terms[i + 1:]]))
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(z3.Xor(expected, z3.And(*z3.parse_smt2_string(result.to_smt2()))))
    assert solver.check() == z3.unsat
