"""Adversarial tests for explicit, proof-gated observable coordinate maps."""
import unittest
from dataclasses import replace

import z3

from tools.semantic_checks.coordinate_map import (
    ObservableMapRefusal,
    build_coordinate_map,
    complete_candidate_bridges,
    fresh_observation_bridges,
    project_candidate_relation,
    project_reference_relation,
    verify_reconstruction,
)
from tools.semantic_checks.checker_adapter import (
    candidate_projection,
    reference_projection,
)


class CoordinateMapTests(unittest.TestCase):
    def small_case(self):
        reference = {"name": "q", "shape": [2], "sort": "Int"}
        candidate = {"name": "queens", "shape": [2, 2], "sort": "Int"}
        mapping = {
            "reference_name": "q",
            "candidate_name": "queens",
            "coordinates": [
                {"reference_index": [0], "candidate_index": [0, 0]},
                {"reference_index": [1], "candidate_index": [1, 0]},
            ],
            "reconstruct": [
                {"candidate_index": [0, 1], "value": 1},
                {"candidate_index": [1, 1], "value": 2},
            ],
        }
        q_array = z3.Array("reference_q", z3.IntSort(), z3.IntSort())
        pair_sort = z3.ArraySort(z3.IntSort(), z3.IntSort())
        c_array = z3.Array("candidate_queens", z3.IntSort(), pair_sort)
        reference_terms = {(i,): z3.Select(q_array, i) for i in range(2)}
        candidate_terms = {
            (i, j): z3.Select(z3.Select(c_array, i), j)
            for i in range(2) for j in range(2)
        }
        plan = build_coordinate_map(reference, candidate, mapping,
                                    reference_terms, candidate_terms)
        reference_assertions = [
            z3.And(q_array[0] >= 1, q_array[0] <= 2),
            z3.And(q_array[1] >= 1, q_array[1] <= 2),
            q_array[0] != q_array[1],
        ]
        candidate_assertions = [
            c_array[0][1] == 1,
            c_array[1][1] == 2,
            z3.And(c_array[0][0] >= 1, c_array[0][0] <= 2),
            z3.And(c_array[1][0] >= 1, c_array[1][0] <= 2),
            c_array[0][0] != c_array[1][0],
        ]
        return (reference, candidate, mapping, q_array, c_array, plan,
                reference_assertions, candidate_assertions)

    def test_full_feasible_relation_is_preserved_not_only_sat(self):
        (_, _, _, q_array, c_array, plan, ref_assertions, cand_assertions) = self.small_case()
        verified = verify_reconstruction(plan, cand_assertions)
        bridges = fresh_observation_bridges(verified, ref_assertions, cand_assertions)
        ref_formula = project_reference_relation(bridges, ref_assertions, reference_projection)
        cand_formula = project_candidate_relation(verified, bridges, cand_assertions, candidate_projection)
        check = z3.Solver()
        check.set(timeout=5000)
        check.add(z3.Xor(ref_formula, cand_formula))
        self.assertEqual(check.check(), z3.unsat)

        # The projection contains both distinct feasible assignments, rather
        # than merely sharing the same SAT/UNSAT bit.
        for first_value in (1, 2):
            check = z3.Solver()
            check.set(timeout=5000)
            check.add(cand_formula, bridges.aliases[0] == first_value)
            self.assertEqual(check.check(), z3.sat)

    def test_missing_reference_cell_is_refused(self):
        ref, cand, mapping, _, _, _, _, _ = self.small_case()
        mapping["coordinates"] = mapping["coordinates"][:-1]
        with self.assertRaises(ObservableMapRefusal) as caught:
            self.small_case_from(ref, cand, mapping)
        self.assertEqual(caught.exception.reason, "reference-coverage")

    def test_duplicate_reference_cell_is_refused(self):
        ref, cand, mapping, _, _, _, _, _ = self.small_case()
        mapping["coordinates"][1]["reference_index"] = [0]
        with self.assertRaises(ObservableMapRefusal) as caught:
            self.small_case_from(ref, cand, mapping)
        self.assertEqual(caught.exception.reason, "duplicate-reference-coordinate")

    def test_duplicate_candidate_cell_is_refused(self):
        ref, cand, mapping, _, _, _, _, _ = self.small_case()
        mapping["coordinates"][1]["candidate_index"] = [0, 0]
        with self.assertRaises(ObservableMapRefusal) as caught:
            self.small_case_from(ref, cand, mapping)
        self.assertEqual(caught.exception.reason, "duplicate-candidate-coordinate")

    def test_out_of_range_candidate_coordinate_is_refused(self):
        ref, cand, mapping, _, _, _, _, _ = self.small_case()
        mapping["coordinates"][1]["candidate_index"] = [2, 0]
        with self.assertRaises(ObservableMapRefusal) as caught:
            self.small_case_from(ref, cand, mapping)
        self.assertEqual(caught.exception.reason, "invalid-map")

    def test_omitted_candidate_cell_must_have_reconstruction(self):
        ref, cand, mapping, _, _, _, _, _ = self.small_case()
        mapping["reconstruct"] = mapping["reconstruct"][:-1]
        with self.assertRaises(ObservableMapRefusal) as caught:
            self.small_case_from(ref, cand, mapping)
        self.assertEqual(caught.exception.reason, "candidate-coverage")

    def test_missing_or_wrong_row_equality_fails_proof(self):
        (_, _, _, _, c_array, plan, _, candidate_assertions) = self.small_case()
        wrong_row = list(candidate_assertions)
        wrong_row[0] = c_array[0][1] == 9
        with self.assertRaises(ObservableMapRefusal) as caught:
            verify_reconstruction(plan, wrong_row)
        self.assertEqual(caught.exception.reason, "proof-counterexample")

        no_row_constraints = candidate_assertions[2:]
        with self.assertRaises(ObservableMapRefusal) as caught:
            verify_reconstruction(plan, no_row_constraints)
        self.assertEqual(caught.exception.reason, "proof-counterexample")

    def test_unknown_timeout_is_typed_refusal(self):
        (_, _, _, _, _, plan, _, candidate_assertions) = self.small_case()

        class UnknownSolver:
            def set(self, **kwargs):
                self.timeout_ms = kwargs.get("timeout")
            def add(self, *args):
                self.assertions = args
            def check(self):
                return z3.unknown
            def reason_unknown(self):
                return "timeout"

        with self.assertRaises(ObservableMapRefusal) as caught:
            verify_reconstruction(plan, candidate_assertions,
                                  solver_factory=UnknownSolver, timeout_ms=1)
        self.assertEqual(caught.exception.reason, "proof-unknown")
        self.assertIn("timeout", str(caught.exception))

    def test_proof_context_cannot_be_weakened_before_projection(self):
        (_, _, _, _, _, plan, ref_assertions, candidate_assertions) = self.small_case()
        verified = verify_reconstruction(plan, candidate_assertions)
        bridges = fresh_observation_bridges(verified, ref_assertions, candidate_assertions)
        weakened = candidate_assertions[2:]
        with self.assertRaises(ObservableMapRefusal) as caught:
            complete_candidate_bridges(verified, bridges, weakened)
        self.assertEqual(caught.exception.reason, "proof-context-mismatch")
        with self.assertRaises(ObservableMapRefusal) as caught:
            project_reference_relation(
                bridges, ref_assertions[:-1], reference_projection)
        self.assertEqual(caught.exception.reason, "proof-context-mismatch")

    def test_aliases_are_fresh_and_shared_by_reference_and_candidate_bridges(self):
        (_, _, _, _, _, plan, ref_assertions, cand_assertions) = self.small_case()
        verified = verify_reconstruction(plan, cand_assertions)
        bridges = fresh_observation_bridges(verified, ref_assertions, cand_assertions)
        alias_ids = [alias.get_id() for alias in bridges.aliases]
        self.assertEqual(len(set(alias_ids)), 2)
        self.assertEqual([a.get_id() for a, _ in bridges.reference_bridges], alias_ids)
        self.assertEqual([a.get_id() for a, _ in bridges.candidate_bridges], alias_ids)
        source_ids = {expr.get_id() for expr in (q for _, q in bridges.reference_bridges)}
        self.assertTrue(set(alias_ids).isdisjoint(source_ids))

    def test_bool_int_pair_is_refused_without_bridge_normalization(self):
        ref = {"name": "r", "shape": [1], "sort": "Bool"}
        cand = {"name": "c", "shape": [1], "sort": "Int"}
        mapping = {"reference_name": "r", "candidate_name": "c",
                   "coordinates": [{"reference_index": [0], "candidate_index": [0]}],
                   "reconstruct": []}
        with self.assertRaises(ObservableMapRefusal) as caught:
            build_coordinate_map(ref, cand, mapping,
                                 {(0,): z3.Bool("r0")}, {(0,): z3.Int("c0")})
        self.assertEqual(caught.exception.reason, "sort-mismatch")


    def test_forged_or_replaced_proof_and_bridge_receipts_are_refused(self):
        (_, _, _, _, _, plan, ref_assertions, cand_assertions) = self.small_case()
        verified = verify_reconstruction(plan, cand_assertions)
        bridges = fresh_observation_bridges(verified, ref_assertions, cand_assertions)
        forged_plan = replace(plan, pairs=plan.pairs[::-1])
        with self.assertRaises(ObservableMapRefusal):
            verify_reconstruction(forged_plan, cand_assertions)
        altered_proof = replace(verified, candidate_assertion_fingerprint="0" * 64)
        with self.assertRaises(ObservableMapRefusal):
            fresh_observation_bridges(altered_proof, ref_assertions, cand_assertions)
        altered_bridges = replace(bridges, candidate_bridges=bridges.candidate_bridges[::-1])
        with self.assertRaises(ObservableMapRefusal):
            complete_candidate_bridges(verified, altered_bridges, cand_assertions)
        with self.assertRaises(ObservableMapRefusal):
            project_reference_relation(
                altered_bridges, ref_assertions, reference_projection)

    def test_nondefault_z3_context_is_preserved(self):
        ctx = z3.Context()
        ref = {"name": "q", "shape": [1], "sort": "Int"}
        cand = {"name": "queens", "shape": [1, 2], "sort": "Int"}
        mapping = {"reference_name": "q", "candidate_name": "queens",
                   "coordinates": [{"reference_index": [0], "candidate_index": [0, 0]}],
                   "reconstruct": [{"candidate_index": [0, 1], "value": 1}]}
        q = z3.Array("ctx_q", z3.IntSort(ctx=ctx), z3.IntSort(ctx=ctx))
        pair_sort = z3.ArraySort(z3.IntSort(ctx=ctx), z3.IntSort(ctx=ctx))
        c = z3.Array("ctx_c", z3.IntSort(ctx=ctx), pair_sort)
        ref_terms = {(0,): z3.Select(q, z3.IntVal(0, ctx=ctx))}
        cand_terms = {(0, j): z3.Select(z3.Select(c, z3.IntVal(0, ctx=ctx)),
                                                z3.IntVal(j, ctx=ctx)) for j in range(2)}
        plan = build_coordinate_map(ref, cand, mapping, ref_terms, cand_terms)
        refs = [q[0] >= 1, q[0] <= 2]
        cands = [c[0][1] == 1, c[0][0] >= 1, c[0][0] <= 2]
        verified = verify_reconstruction(plan, cands,
                                         solver_factory=lambda: z3.Solver(ctx=ctx),
                                         timeout_ms=5000)
        bridges = fresh_observation_bridges(verified, refs, cands)
        projected = project_candidate_relation(
            verified, bridges, cands, candidate_projection)
        self.assertIs(projected.ctx, ctx)
        self.assertTrue(all(alias.ctx is ctx for alias in bridges.aliases))

    def small_case_from(self, reference, candidate, mapping):
        q = {(i,): z3.Int(f"rq{i}") for i in range(2)}
        c = {(i, j): z3.Int(f"cc{i}_{j}") for i in range(2) for j in range(2)}
        return build_coordinate_map(reference, candidate, mapping, q, c)


if __name__ == "__main__":
    unittest.main()
