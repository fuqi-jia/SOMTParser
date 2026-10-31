"""Full relation and cost after a wide root, then many tiny roots."""
import pytest
import somtparser as sp
import z3


@pytest.mark.parametrize("old_format", [False, True])
def test_wide_then_small_roots_preserve_full_relation_and_signed_cost(old_format):
    width, repeats = 4096, 96
    top = 10**30
    prefix = f"p wcnf {width} {repeats + 3} {top}\n" if old_format else ""
    hard = str(top) if old_format else "h"
    rows = [hard + " " + " ".join(map(str, range(1, width + 1))) + " 0"]
    expected_terms = []
    xs = [z3.Bool(f"x{i}") for i in range(1, width + 1)]
    for i in range(repeats):
        weight = 9007199254740993 + i
        literal = -(i % 4 + 1) if i % 2 == 0 else i % 4 + 1
        rows.append(f"{weight} {literal} 0")
        clause = xs[literal - 1] if literal > 0 else z3.Not(xs[-literal - 1])
        expected_terms.append(z3.If(clause, 0, weight))
    rows.extend([hard + " -1 2 0", hard + " 3 -4 0"])
    translated = sp.translate(source=prefix + "\n".join(rows) + "\n", language="wcnf")
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    target = z3.Optimize()
    target.from_string(translated.to_smt2(dialect=sp.OmtDialect.Z3))
    assert len(target.objectives()) == 1
    relation = z3.And(z3.Or(*xs), z3.Or(z3.Not(xs[0]), xs[1]),
                      z3.Or(xs[2], z3.Not(xs[3])))
    cost = z3.Sum(*expected_terms)
    observed_cost = z3.FreshInt("observed_cost")
    expected = z3.And(relation, observed_cost == cost)
    actual = z3.And(*target.assertions(), observed_cost == target.objectives()[0])
    solver = z3.Solver()
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat
    # Neither dropping a final small root nor changing the cost by one may
    # pass the same complete joint relation check.
    wrong_rel = z3.And(z3.Or(*xs), z3.Or(z3.Not(xs[0]), xs[1]))
    for mutation in (z3.And(wrong_rel, observed_cost == cost),
                     z3.And(relation, observed_cost == cost + 1)):
        negative = z3.Solver()
        negative.add(z3.Xor(actual, mutation))
        assert negative.check() == z3.sat


def test_wide_root_followed_by_bad_literal_retains_source_location():
    wide = "h " + " ".join(map(str, range(1, 4097))) + " 0\n"
    translated = sp.translate(source=wide + "7 1 0\n5 -9223372036854775808 0\n",
                              language="wcnf")
    assert not translated.ok
    error = next(d for d in translated.diagnostic_items if d.severity == sp.Severity.ERROR)
    assert error.line == 3
    assert "magnitude" in error.message
