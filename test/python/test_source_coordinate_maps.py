import copy
import unittest

from tools.semantic_checks.source_coordinate_maps import (
    CoordinateMetadataError,
    comparison_metadata_for_explicit_maps,
)


def record(name="a", shape=(3, 3), coordinates=((0, 1), (1, 2))):
    return {
        "name": name,
        "shape": list(shape),
        "sort": "Int",
        "elements": [
            {"index": list(coord), "symbol": f"a_{coord[0]}_{coord[1]}", "sort": "Int"}
            for coord in coordinates
        ],
    }


def mapping(name="a", coordinates=((0, 1), (1, 2))):
    return {
        "reference_name": name,
        "coordinates": [{"reference_index": list(coord), "candidate_index": list(coord)}
                        for coord in coordinates],
    }


class SourceCoordinateMetadataTests(unittest.TestCase):
    def test_sparse_map_is_explicit_and_input_is_unchanged(self):
        original = {"observables": [record()]}
        before = copy.deepcopy(original)
        output = comparison_metadata_for_explicit_maps(original, [mapping()], {"a": [[0, 1], [1, 2]]})
        self.assertEqual(original, before)
        self.assertTrue(output["observables"][0]["sparse"])
        self.assertEqual(output["observables"][0]["observed_indices"], [[0, 1], [1, 2]])

    def test_full_map_does_not_mark_array_sparse(self):
        coords = tuple((i, j) for i in range(2) for j in range(2))
        output = comparison_metadata_for_explicit_maps(
            {"observables": [record(shape=(2, 2), coordinates=coords)]},
            [mapping(coordinates=coords)], {"a": [list(c) for c in coords]})
        self.assertNotIn("sparse", output["observables"][0])
        self.assertNotIn("observed_indices", output["observables"][0])

    def test_refuses_incomplete_duplicate_or_unexported_mapping(self):
        cases = (
            (record(), mapping(coordinates=((0, 1),)), "cover exactly exported"),
            (record(), mapping(coordinates=((0, 1), (0, 1))), "repeats a reference cell"),
            (record(), mapping(coordinates=((0, 1), (2, 2))), "cover exactly exported"),
        )
        for observable, coordinate_map, message in cases:
            with self.subTest(message=message), self.assertRaisesRegex(CoordinateMetadataError, message):
                comparison_metadata_for_explicit_maps(
                    {"observables": [observable]}, [coordinate_map], {"a": [[0, 1], [1, 2]]})

    def test_rejects_wrong_reference_name_and_duplicate_map(self):
        with self.assertRaisesRegex(CoordinateMetadataError, "unknown reference"):
            comparison_metadata_for_explicit_maps({"observables": [record()]}, [mapping("b")], {"a": [[0, 1], [1, 2]]})
        with self.assertRaisesRegex(CoordinateMetadataError, "duplicate coordinate map"):
            comparison_metadata_for_explicit_maps(
                {"observables": [record()]}, [mapping(), mapping()], {"a": [[0, 1], [1, 2]]})

    def test_rejects_source_to_map_mismatch(self):
        with self.assertRaisesRegex(CoordinateMetadataError, "source and map coordinate coverage disagree"):
            comparison_metadata_for_explicit_maps(
                {"observables": [record()]}, [mapping()], {"a": [[0, 1], [2, 2]]})

    def test_rejects_missing_source_index_record(self):
        with self.assertRaisesRegex(CoordinateMetadataError, "source observed coordinates are missing"):
            comparison_metadata_for_explicit_maps(
                {"observables": [record()]}, [mapping()], {})


if __name__ == "__main__":
    unittest.main()
