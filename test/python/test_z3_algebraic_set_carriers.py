"""Whole exported formulas for exact algebraic finite-set carriers."""
import itertools

import pytest
import z3

import somtparser as sp


def integer(value):
    return str(value) if value >= 0 else f"(- {-value})"


def finite(values):
    empty = "(as set.empty (Set Int))"
    return f"(set.insert {' '.join(map(integer, values))} {empty})" if values else empty


def export(body, declarations="(declare-const S (Set Int))"):
    translation = sp.translate(source=declarations + body, language="smtlib2")
    assert translation.ok, [d.message for d in translation.diagnostic_items]
    return translation.to_smt2(sp.OmtDialect.Z3)


def assertions(text):
    return z3.And(list(z3.parse_smt2_string(text)))


@pytest.mark.parametrize("domain", [[], [-2, 0, 3]])
@pytest.mark.parametrize("reverse", [False, True])
@pytest.mark.parametrize("form", ["positive", "negative", "reified"])
def test_algebraic_domain_matches_universal_membership_on_all_integers(domain, reverse, form):
    carrier = finite(domain)
    restricted = f"(set.inter S {carrier})"
    equation = f"(= {restricted} S)" if reverse else f"(= S {restricted})"
    declarations = "(declare-const S (Set Int))(declare-const b Bool)"
    condition = equation if form == "positive" else f"(not {equation})" if form == "negative" else f"(= b {equation})"
    text = export(f"(assert {condition})", declarations)
    assert "forall" not in text and "exists" not in text
    S = z3.Array("S", z3.IntSort(), z3.BoolSort())
    value = z3.Int("independent_domain_value")
    original = z3.ForAll(value, z3.Implies(z3.Select(S, value), z3.Or([value == x for x in domain])))
    expected = original if form == "positive" else z3.Not(original) if form == "negative" else z3.Bool("b") == original
    solver = z3.Solver()
    solver.add(z3.Xor(assertions(text), expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("reverse", [False, True])
def test_sparse_signed_carrier_counts_all_subsets_and_rejects_outside_members(reverse):
    domain = [-2, 0, 3]
    D = finite(domain)
    equation = f"(= (set.inter S {D}) S)" if reverse else f"(= S (set.inter S {D}))"
    for flags in itertools.product([False, True], repeat=len(domain)):
        members = [f"(= (set.member {integer(x)} S) {'true' if present else 'false'})" for x, present in zip(domain, flags)]
        base = f"(assert (and {equation} {' '.join(members)}))"
        text = export(base + f"(assert (= (set.card S) {sum(flags)}))")
        assert "forall" not in text and "set.card" not in text
        solver = z3.Solver(); solver.from_string(text)
        assert solver.check() == z3.sat
        S = z3.Array("S", z3.IntSort(), z3.BoolSort())
        # Includes a hole inside the hull as well as values below/above it.
        for outsider in [-3, -1, 1, 4]:
            solver.push(); solver.add(z3.Select(S, outsider))
            assert solver.check() == z3.unsat
            solver.pop()
        bad = export(base + f"(assert (= (set.card S) {sum(flags) + 1}))")
        wrong = z3.Solver(); wrong.from_string(bad)
        assert wrong.check() == z3.unsat


@pytest.mark.parametrize("domain", [[], [-2, 0, 3]])
@pytest.mark.parametrize("reverse", [False, True])
def test_direct_finite_equality_establishes_exact_cardinality(domain, reverse):
    D = finite(domain)
    equality = f"(= {D} S)" if reverse else f"(= S {D})"
    for claimed, expected in [(len(domain), z3.sat), (len(domain) + 1, z3.unsat)]:
        text = export(f"(assert {equality})(assert (= (set.card S) {claimed}))")
        assert "forall" not in text and "set.card" not in text
        solver = z3.Solver(); solver.from_string(text)
        assert solver.check() == expected


@pytest.mark.parametrize("independent_unbounded_set", [False, True])
def test_array_cell_carriers_support_cardinality_and_dynamic_selection(independent_unbounded_set):
    decl = ("(declare-const U (Set Int))" if independent_unbounded_set else "") + "(declare-const A (Array Int (Set Int)))(declare-const i Int)"
    body = "(assert (and (<= 0 i) (<= i 1)))"
    for index, domain in [(0, []), (1, [-2, 3])]:
        cell = f"(select A {index})"
        body += f"(assert (= {cell} (set.inter {cell} {finite(domain)})))"
        body += f"(assert (= (set.card {cell}) {len(domain)}))"
    body += "(assert (= (set.card (select A i)) (* 2 i)))"
    text = export(body, decl)
    assert "forall" not in text and "set.card" not in text
    solver = z3.Solver(); solver.from_string(text)
    for index in (0, 1):
        solver.push(); solver.add(z3.Int("i") == index)
        assert solver.check() == z3.sat
        solver.pop()


@pytest.mark.parametrize("guard", ["(not DOMAIN)", "(or b DOMAIN)", "(= b DOMAIN)", "(=> b DOMAIN)"])
def test_local_or_negated_domain_cannot_supply_global_cardinality_support(guard):
    domain = f"(= S (set.inter S {finite([-2, 3])}))"
    body = f"(assert {guard.replace('DOMAIN', domain)})(assert (= (set.card S) 1))"
    with pytest.raises(RuntimeError, match="finite support|carrier"):
        export(body, "(declare-const S (Set Int))(declare-const b Bool)")


def test_scoped_assertion_does_not_leak_carrier_after_pop():
    body = f"(push 1)(assert (= S {finite([0])}))(pop 1)(assert (= (set.card S) 1))"
    with pytest.raises(RuntimeError, match="asserted interval proofs|finite support|carrier"):
        export(body)
