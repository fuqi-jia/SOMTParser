"""Finite output alignment must preserve the complete feasible relation."""
from copy import deepcopy
from itertools import count, product
from unittest.mock import patch

import pytest
import z3

from tools.semantic_checks import coordinate_map
from tools.semantic_checks.checker_adapter import candidate_projection, reference_projection
from tools.semantic_checks.coordinate_map import ObservableMapRefusal
from tools.semantic_checks.finite_observables import align_finite_observables


def reference(name="x", shape=(), sort="Int", ctx=None, stem=None):
    leaf = z3.BoolSort(ctx=ctx) if sort == "Bool" else z3.IntSort(ctx=ctx)
    terms = {}
    elements = []
    for index in product(*(range(size) for size in shape)):
        symbol = (stem or f"reference_{name}") + "".join(f"[{i}]" for i in index)
        terms[index] = z3.Const(symbol, leaf)
        elements.append({"index": list(index), "symbol": symbol, "sort": sort})
    return {"observables": [{"name": name, "shape": list(shape), "elements": elements}]}, terms


def payload(name="x", shape=(), sort="Int"):
    return {"model": {"declarations": [{"name": name, "shape": list(shape), "sort": sort}]}}


def mapping(reference_name, candidate_name, pairs):
    return {"reference_name": reference_name, "candidate_name": candidate_name,
            "coordinates": [{"reference_index": list(ri), "candidate_index": list(ci)}
                            for ri, ci in pairs], "reconstruct": []}


def relations(alignment, references, candidates, reference_cost=None, candidate_cost=None):
    return (reference_projection(references, alignment.reference_bridges, reference_cost),
            candidate_projection(candidates, alignment.candidate_bridges, candidate_cost).formula)


def status(*formulas):
    solver = z3.Solver(ctx=formulas[0].ctx)
    solver.set(timeout=5000)
    solver.add(*formulas)
    return solver.check()


def assert_same_relation(left, right):
    assert status(left, z3.Not(right)) == z3.unsat
    assert status(right, z3.Not(left)) == z3.unsat


@pytest.mark.parametrize("sort", ["Int", "Bool"])
def test_identity_preserves_scalar_relation(sort):
    metadata, refs = reference(sort=sort)
    candidate = z3.Int("x") if sort == "Int" else z3.Bool("x")
    ref_assertions = [refs[()] == (3 if sort == "Int" else True)]
    cand_assertions = [candidate == (3 if sort == "Int" else True)]
    aligned = align_finite_observables(
        metadata, payload(sort=sort), reference_assertions=ref_assertions,
        candidate_assertions=cand_assertions)
    left, right = relations(aligned, ref_assertions, cand_assertions)
    assert_same_relation(left, right)
    assert status(left) == z3.sat
    assert aligned.embeddings == {}
    assert aligned.map_provenance[0]["kind"] == "identity"


def rename_case():
    metadata, refs = reference(shape=(2,))
    candies = z3.Array("candies", z3.IntSort(), z3.IntSort())
    ref_assertions = [refs[(0,)] >= 0, refs[(1,)] >= 0, refs[(0,)] + refs[(1,)] == 1]
    cand_assertions = [candies[0] >= 0, candies[1] >= 0, candies[0] + candies[1] == 1]
    explicit = mapping("x", "candies", [((0,), (0,)), ((1,), (1,))])
    return metadata, payload("candies", (2,)), explicit, ref_assertions, cand_assertions, candies


def test_explicit_rename_exposes_both_feasible_assignments_without_mutating_inputs():
    metadata, candidate, explicit, refs, cands, _ = rename_case()
    frozen_metadata = deepcopy(metadata)
    frozen_candidate = deepcopy(candidate)
    frozen_map = deepcopy(explicit)
    original_formulas = [term.sexpr() for term in refs + cands]
    with pytest.raises(ObservableMapRefusal, match="not declared"):
        align_finite_observables(metadata, candidate, reference_assertions=refs, candidate_assertions=cands)
    aligned = align_finite_observables(metadata, candidate, reference_assertions=refs,
                                      candidate_assertions=cands, coordinate_maps=[explicit])
    left, right = relations(aligned, refs, cands)
    assert_same_relation(left, right)
    first, second = [alias for alias, _ in aligned.reference_bridges]
    for value in (0, 1):
        assert status(left, first == value, second == 1 - value) == z3.sat
        assert status(right, first == value, second == 1 - value) == z3.sat
    assert aligned.map_provenance[0]["coordinates"] == explicit["coordinates"]
    assert aligned.map_provenance[0]["candidate_name"] == "candies"
    assert metadata == frozen_metadata and candidate == frozen_candidate and explicit == frozen_map
    assert [term.sexpr() for term in refs + cands] == original_formulas


def test_rename_cannot_hide_wrong_constraint_even_when_both_models_are_sat():
    metadata, candidate, explicit, refs, cands, candies = rename_case()
    cands[-1] = candies[0] + candies[1] == 0
    aligned = align_finite_observables(metadata, candidate, reference_assertions=refs,
                                      candidate_assertions=cands, coordinate_maps=[explicit])
    left, right = relations(aligned, refs, cands)
    assert status(left) == z3.sat and status(right) == z3.sat
    assert status(left, z3.Not(right)) == z3.sat
    assert status(right, z3.Not(left)) == z3.sat


def test_explicit_transpose_preserves_every_coordinate_and_two_feasible_rows():
    metadata, refs = reference("crew", (2, 3))
    candidate = payload("crew", (3, 2))
    crew = z3.Array("crew", z3.IntSort(), z3.ArraySort(z3.IntSort(), z3.IntSort()))
    ref_assertions = [refs[(0, 0)] >= 0, refs[(0, 0)] <= 1]
    cand_assertions = [crew[0][0] >= 0, crew[0][0] <= 1]
    pairs = []
    for i in range(2):
        for j in range(3):
            pairs.append(((i, j), (j, i)))
            ref_assertions.append(refs[(i, j)] == refs[(0, 0)] + i + j)
            cand_assertions.append(crew[j][i] == crew[0][0] + i + j)
    with pytest.raises(ObservableMapRefusal) as caught:
        align_finite_observables(metadata, candidate, reference_assertions=ref_assertions,
                                 candidate_assertions=cand_assertions)
    assert caught.value.reason == "shape-mismatch"
    aligned = align_finite_observables(
        metadata, candidate, reference_assertions=ref_assertions, candidate_assertions=cand_assertions,
        coordinate_maps=[mapping("crew", "crew", pairs)])
    left, right = relations(aligned, ref_assertions, cand_assertions)
    assert_same_relation(left, right)
    assert len(aligned.reference_bridges) == 6
    first = aligned.reference_bridges[0][0]
    for value in (0, 1):
        assert status(left, first == value) == z3.sat
        assert status(right, first == value) == z3.sat


@pytest.mark.parametrize("change, reason", [
    ("incomplete", "reference-coverage"),
    ("duplicate-reference", "duplicate-reference-coordinate"),
    ("duplicate-candidate", "duplicate-candidate-coordinate"),
    ("out-of-range", "invalid-map"),
    ("unknown-reference", "unknown-reference"),
    ("undeclared-candidate", "undeclared-candidate"),
    ("duplicate-map", "duplicate-map"),
    ("reconstruction", "reconstruction-not-supported"),
    ("missing-reconstruct", "reconstruction-not-supported"),
])
def test_invalid_explicit_maps_are_refused(change, reason):
    metadata, candidate, explicit, refs, cands, _ = rename_case()
    maps = [explicit]
    if change == "incomplete":
        explicit["coordinates"].pop()
    elif change == "duplicate-reference":
        explicit["coordinates"][1]["reference_index"] = [0]
    elif change == "duplicate-candidate":
        explicit["coordinates"][1]["candidate_index"] = [0]
    elif change == "out-of-range":
        explicit["coordinates"][1]["candidate_index"] = [2]
    elif change == "unknown-reference":
        explicit["reference_name"] = "unknown"
    elif change == "undeclared-candidate":
        explicit["candidate_name"] = "unknown"
    elif change == "duplicate-map":
        maps.append(deepcopy(explicit))
    elif change == "reconstruction":
        explicit["reconstruct"] = [{"candidate_index": [1], "value": 0}]
    else:
        del explicit["reconstruct"]
    with pytest.raises(ObservableMapRefusal) as caught:
        align_finite_observables(metadata, candidate, reference_assertions=refs,
                                 candidate_assertions=cands, coordinate_maps=maps)
    assert caught.value.reason == reason


def test_complete_reference_map_cannot_silently_drop_extra_candidate_cell():
    metadata, candidate, explicit, refs, cands, candies = rename_case()
    candidate["model"]["declarations"][0]["shape"] = [3]
    cands.append(candies[2] == 0)
    with pytest.raises(ObservableMapRefusal) as caught:
        align_finite_observables(metadata, candidate, reference_assertions=refs,
                                 candidate_assertions=cands, coordinate_maps=[explicit])
    assert caught.value.reason == "candidate-coverage"


@pytest.mark.parametrize("change", [
    "duplicate-cell", "missing-cell", "out-of-range", "boolean-index", "wrong-rank",
    "zero-shape", "boolean-shape", "fractional-shape", "duplicate-observable", "mixed-sort",
])
def test_malformed_reference_metadata_is_refused(change):
    metadata, _ = reference(shape=(2,))
    observable = metadata["observables"][0]
    if change == "duplicate-cell":
        observable["elements"].append(deepcopy(observable["elements"][0]))
    elif change == "missing-cell":
        observable["elements"].pop()
    elif change == "out-of-range":
        observable["elements"][0]["index"] = [-1]
    elif change == "boolean-index":
        observable["elements"][0]["index"] = [False]
    elif change == "wrong-rank":
        observable["elements"][0]["index"] = [0, 0]
    elif change == "zero-shape":
        observable["shape"] = [0]
    elif change == "boolean-shape":
        observable["shape"] = [True]
    elif change == "fractional-shape":
        observable["shape"] = [2.0]
    elif change == "duplicate-observable":
        metadata["observables"].append(deepcopy(observable))
    else:
        observable["elements"][1]["sort"] = "Bool"
    with pytest.raises(ObservableMapRefusal):
        align_finite_observables(metadata, payload(shape=(2,)),
                                 reference_assertions=[], candidate_assertions=[])


def test_duplicate_candidate_declaration_is_rejected_even_when_hidden():
    metadata, _ = reference()
    candidate = payload()
    candidate["model"]["declarations"] += [{"name": "hidden", "sort": "Int"}] * 2
    with pytest.raises(ObservableMapRefusal) as caught:
        align_finite_observables(metadata, candidate, reference_assertions=[], candidate_assertions=[])
    assert caught.value.reason == "duplicate-declaration"


def test_two_reference_outputs_cannot_reuse_one_candidate_output():
    metadata, _ = reference("x")
    other, _ = reference("y")
    metadata["observables"] += other["observables"]
    with pytest.raises(ObservableMapRefusal) as caught:
        align_finite_observables(
            metadata, payload("y"), reference_assertions=[], candidate_assertions=[],
            coordinate_maps=[mapping("x", "y", [((), ())])])
    assert caught.value.reason == "duplicate-candidate-observable"


@pytest.mark.parametrize("reference_sort,candidate_sort", [("Bool", "Int"), ("Int", "Bool")])
def test_bool_int_embedding_is_exact_in_both_directions(reference_sort, candidate_sort):
    metadata, refs = reference(sort=reference_sort)
    x = z3.Bool("x") if candidate_sort == "Bool" else z3.Int("x")
    ref_assertions = [] if reference_sort == "Bool" else [refs[()] >= 0, refs[()] <= 1]
    cand_assertions = [] if candidate_sort == "Bool" else [x >= 0, x <= 1]
    aligned = align_finite_observables(metadata, payload(sort=candidate_sort),
                                      reference_assertions=ref_assertions, candidate_assertions=cand_assertions)
    left, right = relations(aligned, ref_assertions, cand_assertions)
    assert_same_relation(left, right)
    alias = aligned.reference_bridges[0][0]
    for value in (0, 1):
        assert status(left, alias == value) == z3.sat
        assert status(right, alias == value) == z3.sat
    assert status(left, alias == 2) == z3.unsat
    assert aligned.embeddings == {f"{reference_sort}-to-{candidate_sort}": 1}


@pytest.mark.parametrize("reference_sort,candidate_sort", [("Bool", "Int"), ("Int", "Bool")])
def test_integer_two_is_a_real_counterexample_not_coerced_to_boolean(reference_sort, candidate_sort):
    metadata, refs = reference(sort=reference_sort)
    x = z3.Bool("x") if candidate_sort == "Bool" else z3.Int("x")
    ref_assertions = [] if reference_sort == "Bool" else [refs[()] >= 0, refs[()] <= 2]
    cand_assertions = [] if candidate_sort == "Bool" else [x >= 0, x <= 2]
    aligned = align_finite_observables(metadata, payload(sort=candidate_sort),
                                      reference_assertions=ref_assertions, candidate_assertions=cand_assertions)
    left, right = relations(aligned, ref_assertions, cand_assertions)
    integer_relation, boolean_relation = (left, right) if reference_sort == "Int" else (right, left)
    alias = aligned.reference_bridges[0][0]
    assert status(integer_relation, alias == 2, z3.Not(boolean_relation)) == z3.sat
    assert status(boolean_relation, z3.Not(integer_relation)) == z3.unsat


def test_declared_but_unconstrained_scalar_retains_missing_constraint_counterexample():
    metadata, refs = reference()
    ref_assertions = [refs[()] == 7]
    aligned = align_finite_observables(metadata, payload(), reference_assertions=ref_assertions,
                                      candidate_assertions=[])
    left, right = relations(aligned, ref_assertions, [])
    alias = aligned.reference_bridges[0][0]
    assert status(left, z3.Not(right)) == z3.unsat
    assert status(right, alias == 2, z3.Not(left)) == z3.sat


@pytest.mark.parametrize("sort", ["Bool", "Int"])
def test_unconstrained_nested_array_is_constructed_in_supplied_context(sort):
    ctx = z3.Context()
    metadata, _ = reference(shape=(1, 2), sort=sort, ctx=ctx)
    formulas = [z3.BoolVal(True, ctx=ctx)]
    aligned = align_finite_observables(metadata, payload(shape=(1, 2), sort=sort),
                                      reference_assertions=formulas, candidate_assertions=[])
    left, right = relations(aligned, formulas, [])
    assert_same_relation(left, right)
    first, second = [alias for alias, _ in aligned.reference_bridges]
    values = (False, True) if sort == "Bool" else (-3, 8)
    assert status(right, first == values[0], second == values[1]) == z3.sat
    assert all(alias.ctx is ctx and term.ctx is ctx
               for alias, term in aligned.reference_bridges + aligned.candidate_bridges)


@pytest.mark.parametrize("explicit_shape", [False, True])
def test_missing_or_empty_candidate_shape_denotes_a_scalar(explicit_shape):
    metadata, _ = reference()
    candidate = payload()
    if not explicit_shape:
        del candidate["model"]["declarations"][0]["shape"]
    aligned = align_finite_observables(metadata, candidate, reference_assertions=[], candidate_assertions=[])
    assert z3.is_int(aligned.candidate_bridges[0][1])


@pytest.mark.parametrize("shape", [None, [False], [0], [-1], [1.0], "scalar"])
def test_explicit_invalid_candidate_shape_is_refused(shape):
    metadata, _ = reference()
    candidate = payload()
    candidate["model"]["declarations"][0]["shape"] = shape
    with pytest.raises(ObservableMapRefusal) as caught:
        align_finite_observables(metadata, candidate, reference_assertions=[], candidate_assertions=[])
    assert caught.value.reason == "invalid-metadata"


def test_actual_constant_without_candidate_declaration_is_still_refused():
    metadata, _ = reference()
    with pytest.raises(ObservableMapRefusal) as caught:
        align_finite_observables(metadata, {"model": {"declarations": []}},
                                 reference_assertions=[], candidate_assertions=[z3.Int("x") == 1])
    assert caught.value.reason == "undeclared-candidate"


def test_hidden_empty_array_does_not_restrict_a_valid_scalar_observable():
    metadata, refs = reference()
    candidate = payload()
    candidate["model"]["declarations"].append(
        {"name": "unused", "sort": "Bool", "shape": [0]})
    ref_assertions = [refs[()] == 3]
    cand_assertions = [z3.Int("x") == 3]
    aligned = align_finite_observables(metadata, candidate,
        reference_assertions=ref_assertions, candidate_assertions=cand_assertions)
    assert_same_relation(*relations(aligned, ref_assertions, cand_assertions))


@pytest.mark.parametrize("location", ["assertions", "objectives", "reference", "reference-objective"])
def test_actual_same_name_sort_mismatch_is_refused(location):
    metadata, refs = reference()
    ref_assertions = [z3.Bool(str(refs[()].decl().name()))] if location == "reference" else []
    cand_assertions = [z3.Bool("x")] if location == "assertions" else []
    objectives = [z3.Real("x") + 1] if location == "objectives" else []
    ref_objectives = [z3.Real(str(refs[()].decl().name()))] if location == "reference-objective" else []
    with pytest.raises(ObservableMapRefusal) as caught:
        align_finite_observables(metadata, payload(), reference_assertions=ref_assertions,
                                 candidate_assertions=cand_assertions, candidate_objectives=objectives,
                                 reference_objectives=ref_objectives)
    assert caught.value.reason == "sort-mismatch"


def test_actual_nested_array_rank_must_match_declared_shape():
    metadata, _ = reference(shape=(2, 2))
    x = z3.Array("x", z3.IntSort(), z3.IntSort())
    with pytest.raises(ObservableMapRefusal) as caught:
        align_finite_observables(metadata, payload(shape=(2, 2)), reference_assertions=[],
                                 candidate_assertions=[x[0] == 1])
    assert caught.value.reason == "sort-mismatch"


def test_mixed_contexts_are_rejected_before_constant_discovery():
    metadata, _ = reference()
    ctx = z3.Context()
    with pytest.raises(ObservableMapRefusal) as caught:
        align_finite_observables(metadata, payload(), reference_assertions=[z3.BoolVal(True)],
                                 candidate_assertions=[z3.BoolVal(True, ctx=ctx)])
    assert caught.value.reason == "proof-context-mismatch"


def test_renaming_does_not_align_away_a_wrong_objective():
    metadata, candidate, explicit, refs, cands, candies = rename_case()
    ref_terms = [z3.Int(element["symbol"]) for element in metadata["observables"][0]["elements"]]
    ref_objective = ref_terms[0] + 2 * ref_terms[1]
    correct_objective = candies[0] + 2 * candies[1]
    wrong_objective = 2 * candies[0] + candies[1]
    cost = z3.Int("observable_alignment_cost")
    for objective, equivalent in [(correct_objective, True), (wrong_objective, False)]:
        aligned = align_finite_observables(metadata, candidate, reference_assertions=refs,
                                          candidate_assertions=cands, candidate_objectives=[objective],
                                          reference_objectives=[ref_objective],
                                          coordinate_maps=[explicit])
        assert len(aligned.reference_bridges) == 2
        left, right = relations(aligned, refs, cands, (cost, ref_objective), (cost, objective))
        if equivalent:
            assert_same_relation(left, right)
        else:
            assert status(left, z3.Not(right)) == z3.sat
            assert status(right, z3.Not(left)) == z3.sat


def test_alias_freshness_protects_objective_only_terms_other_maps_and_both_assertion_sets():
    metadata, ref_x = reference()
    extra, _ = reference("later", stem="finite_observable_0_1")
    metadata["observables"] += extra["observables"]
    candidate = payload()
    candidate["model"]["declarations"] += [
        {"name": "later", "sort": "Int"},
        {"name": "finite_observable_0_0", "sort": "Int"},
        {"name": "finite_observable_0_2", "sort": "Int"},
    ]
    objective_only = z3.Int("finite_observable_0_0")
    cand_hidden = z3.Int("finite_observable_0_2")
    ref_hidden = z3.Int("finite_observable_0_3")
    ref_cost = z3.Int("finite_observable_0_4")
    refs = [ref_x[()] == 2, ref_hidden == 5]
    cands = [z3.Int("x") == 2, cand_hidden == 5]
    # Force real symbol collisions, then check the resulting feasible
    # relation; this does not assert how many allocation attempts occur.
    with patch.object(coordinate_map, "_FRESH_ALIAS_COUNTER", count()):
        aligned = align_finite_observables(metadata, candidate, reference_assertions=refs,
                                          candidate_assertions=cands, candidate_objectives=[objective_only],
                                          reference_objectives=[ref_cost])
    cost = z3.Int("separate_alignment_cost")
    left, right = relations(aligned, refs, cands, (cost, ref_cost), (cost, objective_only))
    assert_same_relation(left, right)
    first, later = [alias for alias, _ in aligned.reference_bridges]
    assert status(right, first == 2, later == 7, cost == 9) == z3.sat
    assert status(left, first == 2, later == 7, cost == 9) == z3.sat


@pytest.mark.parametrize("sort", ["Real", "String", {"Array": ["Int", "Int"]}])
def test_unsupported_observable_sort_is_refused(sort):
    metadata, _ = reference()
    with pytest.raises(ObservableMapRefusal) as caught:
        align_finite_observables(metadata, payload(sort=sort), reference_assertions=[], candidate_assertions=[])
    assert caught.value.reason == "unsupported-sort"
