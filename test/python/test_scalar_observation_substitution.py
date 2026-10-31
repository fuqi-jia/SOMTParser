"""Independent relation oracles and counted scalar-substitution API work."""
from pathlib import Path
import json
import os
import time

import pytest
import z3

from tools.semantic_checks import projection


EVIDENCE = Path(os.environ["PROJECTION_EVIDENCE"]) if "PROJECTION_EVIDENCE" in os.environ else None
if EVIDENCE is not None:
    EVIDENCE.mkdir(exist_ok=True)


def record(name, data):
    if EVIDENCE is not None:
        (EVIDENCE / (name + ".json")).write_text(json.dumps(data, indent=2) + "\n")


def answer(*formulas):
    solver = z3.Solver(ctx=formulas[0].ctx)
    solver.add(*formulas)
    return solver.check()


def same(left, right):
    assert answer(z3.Xor(left, right)) == z3.unsat


def optimized(body, bridges, module=projection):
    return module.optimize_observation_projection(body, bridges, guarded_bool_budget_ms=None)


def body_with_bridges(source, bridges):
    return z3.And(source, *[alias == term for alias, term in bridges])


def counted(module, body, bridges, monkeypatch):
    original = module._substitute
    events = []

    def count(expression, substitutions):
        if substitutions:
            events.append({"binding_pairs": len(substitutions),
                           "scalar_term": module._uninterpreted_constant(expression)})
        return original(expression, substitutions)

    with monkeypatch.context() as scope:
        scope.setattr(module, "_substitute", count)
        started = time.perf_counter()
        result = optimized(body, bridges, module)
        elapsed = time.perf_counter() - started
    return result, dict(substitute_calls=len(events),
                       binding_pairs_marshaled=sum(e["binding_pairs"] for e in events),
                       scalar_term_calls=sum(e["scalar_term"] for e in events),
                       elapsed_seconds=elapsed)


def test_duplicate_mixed_sort_outputs_preserve_full_relation_and_alias_equalities():
    x = z3.Int("dup_private_int")
    y = z3.Real("dup_private_real")
    flag = z3.Bool("dup_private_bool")
    a, a2 = z3.Ints("dup_a dup_a2")
    b, b2 = z3.Reals("dup_b dup_b2")
    c, c2 = z3.Bools("dup_c dup_c2")
    bridges = [(a, x), (b, y), (c, flag), (a2, x), (b2, y), (c2, flag)]
    source = z3.And(x >= 0, x <= 3, y == z3.ToReal(x) / 2, flag == (x > 1))
    body = body_with_bridges(source, bridges)
    result = optimized(body, bridges)
    expected = z3.And(a >= 0, a <= 3, b == z3.ToReal(a) / 2, c == (a > 1),
                      a == a2, b == b2, c == c2)
    same(result.body, expected)
    same(result.body, z3.Exists([x, y, flag], body))
    for first, duplicate in [(a, a2), (b, b2), (c, c2)]:
        assert answer(result.body, first != duplicate) == z3.unsat
    assert answer(result.body, a == 3, b == z3.RealVal("3/2"), c) == z3.sat
    without_duplicate_equations = z3.And(a >= 0, a <= 3, b == z3.ToReal(a) / 2, c == (a > 1))
    assert answer(z3.Xor(result.body, without_duplicate_equations)) == z3.sat
    assert set(result.scalar_terms) == {str(x), str(y), str(flag)}
    record("duplicate-mixed-sorts", dict(original_projection_xor="unsat", independent_oracle_xor="unsat",
        unequal_duplicate_aliases="unsat", omitted_alias_equality_mutant="sat"))


def test_composites_keep_simultaneous_substitution_and_exact_rational_values(monkeypatch):
    x = z3.Int("composite_private_int")
    y = z3.Real("composite_private_real")
    flag = z3.Bool("composite_private_bool")
    a = z3.Int("composite_a")
    b, real_out = z3.Reals("composite_b composite_real_out")
    c = z3.Bool("composite_c")
    int_out = z3.Int("composite_int_out")
    int_term = z3.If(flag, x + 1, x - 1)
    real_term = y + z3.ToReal(x) / 3
    bridges = [(a, x), (b, y), (c, flag), (int_out, int_term), (real_out, real_term)]
    body = body_with_bridges(z3.And(x >= -2, x <= 4), bridges)
    result, counts = counted(projection, body, bridges, monkeypatch)
    expected = z3.And(a >= -2, a <= 4, int_out == z3.If(c, a + 1, a - 1),
                      real_out == b + z3.ToReal(a) / 3)
    same(result.body, expected)
    same(result.body, z3.Exists([x, y, flag], body))
    assert counts["substitute_calls"] == 3  # Whole body and two composites.
    assert counts["binding_pairs_marshaled"] == 9
    assert counts["scalar_term_calls"] == 0
    record("composite-simultaneous", dict(counts=counts, oracle_xor="unsat"))


def test_array_index_receives_scalar_replacement_and_preserves_symbolic_read(monkeypatch):
    index = z3.Int("index_private")
    array = z3.Array("index_private_array", z3.IntSort(), z3.IntSort())
    observed, first, indexed = z3.Ints("index_observed index_first index_read")
    bridges = [(observed, index), (indexed, array[index]), (first, array[0])]
    body = body_with_bridges(z3.And(index >= 0, index <= 1), bridges)
    seen = []
    original_roots = projection._array_roots

    def capture(expression):
        seen.append(expression)
        return original_roots(expression)

    with monkeypatch.context() as scope:
        scope.setattr(projection, "_array_roots", capture)
        result = optimized(body, bridges)
    assert any(term.eq(array[observed]) for term in seen)
    assert not any(term.eq(array[index]) for term in seen)
    # The changed scalar index remains symbolic. It must not become a concrete
    # cell or erase the condition that equal indices have equal read values.
    assert str(array) in result.retained_array_roots
    expected_body = z3.And(observed >= 0, observed <= 1,
                           indexed == array[observed], first == array[0])
    same(result.body, expected_body)
    assert answer(result.body, observed == 0, first != indexed) == z3.unsat
    assert answer(result.body, observed == 1, first == 7, indexed == 11) == z3.sat
    # Construct a total-array witness for every independently allowed output;
    # separately prove necessity without asking a quantified-array XOR solver.
    expected_projection = z3.And(observed >= 0, observed <= 1,
                                  z3.Implies(observed == 0, first == indexed))
    assert answer(result.body, z3.Not(expected_projection)) == z3.unsat
    witness = z3.Store(z3.Store(z3.K(z3.IntSort(), 0), 0, first), observed, indexed)
    same(z3.substitute(result.body, (array, witness)), expected_projection)
    record("scalar-in-array-index", dict(rewritten_index_observed=True, symbolic_array_retained=True,
        full_body_xor="unsat", projection_necessity="unsat", extension_witness_xor="unsat"))


def test_numeral_observations_are_not_mistaken_for_direct_scalar_constants():
    private = z3.Int("numeral_private")
    observed, literal = z3.Ints("numeral_observed numeral_literal")
    bridges = [(observed, private), (literal, z3.IntVal(7))]
    body = body_with_bridges(private > 0, bridges)
    actual = optimized(body, bridges)
    same(actual.body, z3.And(observed > 0, literal == 7))


@pytest.mark.parametrize("size", [8, 32, 128])
def test_substitution_parameter_count_is_linear_for_direct_scalar_bridges(size, monkeypatch):
    terms = [z3.Int(f"scale_{size}_private_{i}") for i in range(size)]
    aliases = [z3.Int(f"scale_{size}_observed_{i}") for i in range(size)]
    bridges = list(zip(aliases, terms))
    body = body_with_bridges(z3.And(*[term >= i for i, term in enumerate(terms)]), bridges)
    new, new_counts = counted(projection, body, bridges, monkeypatch)
    same(new.body, z3.And(*[alias >= i for i, alias in enumerate(aliases)]))
    assert new_counts["substitute_calls"] == 1
    assert new_counts["binding_pairs_marshaled"] == size
    assert new_counts["scalar_term_calls"] == 0
    record(f"scale-{size}", dict(size=size, candidate=new_counts, independent_oracle_xor="unsat"))


def test_3300_scalar_outputs_and_duplicates_keep_one_linear_substitution(monkeypatch):
    size = 3300
    terms = [z3.Int(f"large_private_{i}") for i in range(size)]
    aliases = [z3.Int(f"large_output_{i}") for i in range(size)]
    duplicates = [z3.Int(f"large_duplicate_{i}") for i in range(0, size, 100)]
    duplicate_terms = terms[::100]
    bridges = list(zip(aliases, terms)) + list(zip(duplicates, duplicate_terms))
    body = body_with_bridges(z3.And(*[term >= i for i, term in enumerate(terms)]), bridges)
    new, counts = counted(projection, body, bridges, monkeypatch)
    expected = z3.And(*[alias >= i for i, alias in enumerate(aliases)],
                      *[duplicate == alias for duplicate, alias in zip(duplicates, aliases[::100])])
    same(new.body, expected)
    assert counts["substitute_calls"] == 1
    assert counts["binding_pairs_marshaled"] == size
    assert counts["scalar_term_calls"] == 0
    assert len(new.scalar_terms) == size
    record("scale-3300-duplicates", dict(distinct_scalar_terms=size, observed_bridges=len(bridges),
        candidate=counts, independent_oracle_xor="unsat", resource_limits=None))
