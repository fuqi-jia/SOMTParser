"""Whole-relation oracles for ordinary lookups over compact scalar arrays."""
import pytest
import time
import somtparser as sp

z3 = pytest.importorskip("z3")

SOLVER_TIMEOUT_MS = 120_000


def _conjuncts(expression):
    pending = [expression]
    while pending:
        current = pending.pop()
        if z3.is_and(current):
            pending.extend(reversed(current.children()))
        else:
            yield current


def _factor_relations(actual, expected):
    # All ASTs remain alive in the same Z3 context; get_id gives exact AST
    # identity, not a hash that could conflate distinct conjuncts.
    # Arithmetic normalization also identifies the equivalent interval forms
    # (-2 <= x) from SMT chained bounds and (x >= -2) from the oracle.
    left = {term.get_id(): term for term in _conjuncts(z3.simplify(actual, arith_lhs=True))}
    right = {term.get_id(): term for term in _conjuncts(z3.simplify(expected, arith_lhs=True))}
    common = [term for identity, term in left.items() if identity in right]
    left_only = [term for identity, term in left.items() if identity not in right]
    right_only = [term for identity, term in right.items() if identity not in left]
    print(f"exact factoring: common={len(common)}, left={len(left_only)}, right={len(right_only)}", flush=True)
    # Exact identity: (C and A) xor (C and B) == C and (A xor B).
    # Keep C: residual equivalence can depend on its variable domains.
    return common, z3.Xor(z3.And(*left_only), z3.And(*right_only))


def _whole_relation_difference(actual, expected):
    common, residual = _factor_relations(actual, expected)
    return z3.And(*common, residual)


def _free_symbols(expression):
    pending, visited, result = [expression], set(), set()
    while pending:
        term = pending.pop()
        if term.get_id() in visited:
            continue
        visited.add(term.get_id())
        assert not z3.is_quantifier(term), "This oracle is for quantifier-free relations"
        if z3.is_app(term) and term.decl().kind() == z3.Z3_OP_UNINTERPRETED:
            assert term.num_args() == 0, "No uninterpreted function symbols in this oracle"
            result.add(term.get_id())
        pending.extend(term.children())
    return result


def _prove_whole_equivalence(actual, expected, bindings, label, observables=()):
    common, residual = _factor_relations(actual, expected)
    solver = z3.Solver()
    solver.set(timeout=SOLVER_TIMEOUT_MS)
    solver.add(residual)
    started = time.monotonic()
    answer = solver.check()
    print(f"{label}: stronger residual proof: {answer}, {time.monotonic()-started:.3f}s", flush=True)
    if answer == z3.unsat:
        # UNSAT(XOR(A,B)) implies UNSAT(C and XOR(A,B)) for every C.
        # The complete actual/reference witness below separately proves non-vacuity.
        return
    if answer == z3.unknown:
        print(f"{label}: residual unknown: {solver.reason_unknown()}; try exact domain closure", flush=True)
    # A SAT/unknown residual is not a counterexample. Keep every common conjunct
    # connected to a residual symbol, including transitive domain dependencies.
    support = [_free_symbols(term) for term in common]
    active = _free_symbols(residual)
    retained = set()
    while True:
        additions = {i for i, symbols in enumerate(support)
                     if i not in retained and symbols & active}
        if not additions:
            break
        retained.update(additions)
        for i in additions:
            active.update(support[i])
    connected = [term for i, term in enumerate(common) if i in retained]
    detached = [term for i, term in enumerate(common) if i not in retained]
    assert all(not (support[i] & active) for i in range(len(common)) if i not in retained)
    # Detached C has disjoint free symbols. A complete concrete valuation proves
    # SAT(C_detached); therefore SAT(full difference) iff SAT(connected difference).
    _evaluate_witness(z3.And(*detached), bindings, label + ": detached domains satisfiable")
    solver = z3.Solver()
    solver.add(residual, *connected)
    _check(solver, z3.unsat, label + ": full relation via domain closure", observables)



def _check(solver, expected, label, observables=()):
    solver.set(timeout=SOLVER_TIMEOUT_MS)
    started = time.monotonic()
    outcome = solver.check()
    print(f"{label}: {outcome}, {time.monotonic() - started:.3f}s", flush=True)
    assert outcome != z3.unknown, (
        f"{label}: {solver.reason_unknown()}; solver timeout={SOLVER_TIMEOUT_MS}ms"
    )
    witness = None
    if outcome == z3.sat and expected != z3.sat:
        model = solver.model()
        witness = {str(term): str(model.eval(term, model_completion=True))
                   for term in observables}
    assert outcome == expected, f"{label}: expected {expected}, got {outcome}, witness={witness}"


def _evaluate_witness(expression, bindings, label, expected_truth=True):
    started = time.monotonic()
    evaluated = z3.simplify(z3.substitute(expression, *bindings))
    print(f"{label}: explicit complete valuation, {time.monotonic() - started:.3f}s", flush=True)
    accepted = z3.is_true(evaluated) if expected_truth else z3.is_false(evaluated)
    assert accepted, f"{label}: complete valuation did not establish {expected_truth}: {str(evaluated)[:400]}"


@pytest.mark.parametrize("file_input", [False, True])
@pytest.mark.parametrize("case", ["mixed", "aliased", "literal", "first"])
def test_positional_scalar_calls_preserve_full_relation(tmp_path, file_input, case):
    first, second, b, i, v = z3.Ints("a[5][5] a[5][6] b i v")
    start = 2 if case == "aliased" else -1
    cell_names = "a[5][5] b a[5][5]" if case in {"aliased", "first"} else "a[5][5] b a[5][6]"
    cells = (first, b, first) if case in {"aliased", "first"} else (first, b, second)
    if case == "literal":
        cell_names, cells = "a[5][5] b -1", (first, b, -1)
    index_name, value_name = ("a[5][5]", "a[5][5]") if case == "aliased" else ("i", "v")
    index, value = (first, first) if case == "aliased" else (i, v)
    rank = ' rank="first"' if case == "first" else ""
    source = (
        '<instance format="XCSP3" type="CSP"><variables>'
        '<array id="a" size="[256][256]" startIndex="5">-2..5</array>'
        '<var id="b">-2..5</var><var id="i">-2..5</var><var id="v">-2..5</var>'
        '</variables><constraints>'
        f'<element><list startIndex="{start}">{cell_names}</list>'
        f'<index{rank}>{index_name}</index><value>{value_name}</value></element>'
        '</constraints></instance>'
    )
    if file_input:
        path = tmp_path / "positional.xml"
        path.write_text(source)
        translated = sp.translate(path=str(path), language="xcsp3")
    else:
        translated = sp.translate(source=source, language="xcsp3")
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    assert translated.uses_packed_smt_stream
    assert translated.report.stats.num_vars == 65539
    script = translated.to_smt2()
    assert translated.to_smt2() == script
    actual = z3.And(*z3.parse_smt2_string(script))
    bounds = []
    zero = z3.IntVal(0)
    bindings = [(b, zero), (i, z3.IntVal(0 if case == "aliased" else start)), (v, zero)]
    for row in range(5, 261):
        for column in range(5, 261):
            coordinate = z3.Int(f"a[{row}][{column}]")
            bounds.append(z3.And(coordinate >= -2, coordinate <= 5))
            assignment = z3.IntVal(2) if case == "aliased" and (row, column) == (5, 5) else zero
            bindings.append((coordinate, assignment))
    assert len(bindings) == 65539
    assert len({term.get_id() for term, _ in bindings}) == 65539
    alternatives = []
    for position, cell in enumerate(cells):
        earlier = [cells[j] != value for j in range(position)] if case == "first" else []
        alternatives.append(z3.And(index == start + position, value == cell, *earlier))
    scalar_domains = (b >= -2, b <= 5, i >= -2, i <= 5, v >= -2, v <= 5)
    relation = z3.Or(*alternatives)
    expected = z3.And(*bounds, *scalar_domains, relation)
    _prove_whole_equivalence(actual, expected, bindings,
                            f"{case}/{file_input}: whole relation",
                            (first, second, b, i, v, z3.Int("a[260][260]")))
    # The independent relation is satisfiable for each arm; an empty or
    # accidentally inconsistent export cannot pass the XOR check vacuously.
    # An explicit complete satisfying valuation proves non-vacuity without
    # asking an SMT solver to search 65,536 independent interval variables.
    _evaluate_witness(expected, bindings, f"{case}/{file_input}: reference non-vacuity")
    _evaluate_witness(actual, bindings, f"{case}/{file_input}: actual non-vacuity")
    solver = z3.Solver()
    solver.add(actual, z3.Int("a[260][260]") == 6)
    _check(solver, z3.unsat, f"{case}/{file_input}: final cell domain")

    if case == "mixed" and not file_input:
        # The same whole-relation checker must expose deliberately wrong exports.
        # Complete counterexample valuations retain all cells and remaining bounds.
        final_cell = z3.Int("a[260][260]")
        outside_domain = [(term, z3.IntVal(6) if term.eq(final_cell) else assigned)
                          for term, assigned in bindings]
        removed_domain = z3.And(*bounds[:-1], *scalar_domains, relation)
        changed_domain = z3.And(*bounds[:-1], final_cell >= -2,
                                final_cell <= 6, *scalar_domains, relation)
        for label, mutant in (("removed domain", removed_domain),
                              ("changed domain", changed_domain)):
            _evaluate_witness(_whole_relation_difference(mutant, expected),
                              outside_domain, label + " mutant detected")
        wrong_value = [(term, z3.IntVal(1) if term.eq(v) else assigned)
                       for term, assigned in bindings]
        removed_element = z3.And(*bounds, *scalar_domains)
        _evaluate_witness(_whole_relation_difference(removed_element, expected),
                          wrong_value, "removed element mutant detected")
        changed_element = z3.And(*bounds, *scalar_domains,
            z3.Or(*(z3.And(index == start + position, value == cell + 1)
                    for position, cell in enumerate(cells))))
        _evaluate_witness(_whole_relation_difference(changed_element, expected),
                          wrong_value, "changed element mutant detected")
        # Dropping the common domain would falsely report a difference at u=-1.
        u = z3.Int("factoring_domain_guard")
        _prove_whole_equivalence(
            z3.And(u >= 0, u == 1), z3.And(u >= 0, z3.Or(u == 1, u == -1)),
            [(u, z3.IntVal(1))], "common domain retained", (u,))
        # Domain relevance must include transitive connections, not only
        # conjuncts that directly mention residual variables.
        linked = z3.Int("factoring_linked_domain")
        _prove_whole_equivalence(
            z3.And(u == linked, linked >= 0, u == 1),
            z3.And(u == linked, linked >= 0, z3.Or(u == 1, u == -1)),
            [(u, z3.IntVal(1)), (linked, z3.IntVal(1))],
            "transitive common domain retained", (u, linked))
