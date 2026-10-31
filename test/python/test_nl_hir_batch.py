import json
from pathlib import Path
import tempfile
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools"))

from nl_hir_batch import (BatchPackageError, build_request_package, prepare_file,
                          seal_file, seal_outputs, validate_output)
from somtparser.hir import hir_api, hir_schema


SOURCE = "Choose a value."


def sat_model():
    return {
        "schema": "somt-hir-model-v1", "language": "hir",
        "decision": "satisfiability", "declarations": [], "functions": [],
        "constraints": [], "objectives": [], "objective_order": "single",
        "goal": None, "assumptions": [], "unresolved": [],
    }


def request_package():
    return build_request_package([{"id": "tiny/0", "source": SOURCE,
                                  "context": {"x": "public output name"}}])


def output(model=None):
    return {"id": "tiny/0", "model": sat_model() if model is None else model,
            "modeling_notes": "Source-faithful satisfiability model."}


class HIRBatchTests(unittest.TestCase):
    def test_supplied_spans_use_unicode_characters_and_survive_crlf(self):
        source = "选择🍎。\r\n\r\n第二条要求。\n"
        request = build_request_package([{"id": "tiny/0", "source": source}])["requests"][0]
        self.assertEqual([[0, 4], [8, 14]], request["source_line_spans"])
        self.assertEqual(len(source), request["source_length"])
        for span in request["source_line_spans"]:
            model = sat_model()
            model["constraints"] = [{"expr": {"literal": True, "sort": "Bool"},
                                     "span": span}]
            validate_output(request, output(model))
        request["source_line_spans"][0][1] = len("选择🍎。".encode("utf-8"))
        with self.assertRaisesRegex(BatchPackageError, "source_line_spans"):
            validate_output(request, output())

    def test_envelope_examples_from_failed_batches_are_rejected_before_build(self):
        malformed = output()
        malformed["modeling_notes"] = {"assumptions": []}
        contextual = output()
        contextual["model"]["context"] = {}
        with patch("nl_hir_batch.build_hir") as build:
            for candidate in [malformed, contextual]:
                with self.assertRaises(BatchPackageError):
                    validate_output(request_package()["requests"][0], candidate)
            build.assert_not_called()

    def test_archived_requests_without_generation_aids_still_validate(self):
        request = request_package()["requests"][0]
        for key in ["source_length", "source_line_spans", "response_envelope_schema"]:
            del request[key]
        validate_output(request, output())

    def test_request_embeds_full_live_schema_and_constructor_catalog(self):
        request = request_package()["requests"][0]
        self.assertEqual(hir_schema(), request["hir_schema"])
        self.assertEqual(hir_api(), request["operator_catalog"])
        self.assertTrue({"language", "assumptions", "objective_order"} <=
                        set(request["hir_schema"]["required"]))
        self.assertIn("operations", request["operator_catalog"])
        self.assertIn("cp_constructors", request["operator_catalog"])
        self.assertEqual({"x": "public output name"}, request["context"])

    def test_request_instruction_preserves_namespace_goal_and_array_semantics(self):
        instruction = request_package()["requests"][0]["instruction"]
        for requirement in [
            "one global name namespace",
            "declare each context observable exactly once",
            "keep goal null",
            "inverse encodings are allowed",
            "using channeling constraints where needed",
            "Never erase unresolved solely to pass validation",
            "intentionally not sealable pending review",
        ]:
            self.assertIn(requirement, instruction)

    def test_valid_zero_objective_model_seals_without_translation_or_solver(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            source_file = root / "source.json"
            source_file.write_text(json.dumps({"cases": [{"id": "tiny/0",
                "source": SOURCE, "context": {"x": "public output name"}}]}), encoding="utf-8")
            request_dir = root / "requests"
            request_manifest = prepare_file(source_file, request_dir)
            self.assertEqual(1, request_manifest["denominator"])
            self.assertTrue((request_dir / "hir-schema.json").is_file())
            self.assertTrue((request_dir / "operator-catalog.json").is_file())
            response_dir = root / "responses"
            response_dir.mkdir()
            (response_dir / "0.json").write_text(json.dumps(output()), encoding="utf-8")
            destination = root / "sealed"
            manifest = seal_file(request_dir / "requests.json", response_dir, destination)
            self.assertEqual(1, manifest["denominator"])
            self.assertEqual(0, manifest["api_calls"])
            self.assertIn("no translation/solver", manifest["validation"])
            saved = json.loads((destination / "0.json").read_text(encoding="utf-8"))
            self.assertEqual(output(), saved)

    def test_builder_validation_rejects_schema_enum_and_operator_errors(self):
        changes = [
            (lambda m: m.pop("assumptions"), "missing fields"),
            (lambda m: m.update(objective_order=[]), "objective_order"),
            (lambda m: m.update(decision="optimization", objectives=[{
                "sense": "min", "expr": {"literal": 1, "sort": "Int"},
                "span": [0, len(SOURCE)]}]), "unknown objective sense"),
            (lambda m: m.update(constraints=[{
                "expr": {"op": "select", "args": [
                    {"literal": 1, "sort": "Int"}, {"literal": 0, "sort": "Int"},
                    {"literal": 1, "sort": "Int"}]}, "span": [0, len(SOURCE)]
            }]), "unknown HIR operator or invalid arity: select"),
        ]
        for mutate, message in changes:
            with self.subTest(message=message), tempfile.TemporaryDirectory() as temp:
                model = sat_model()
                mutate(model)
                destination = Path(temp) / "sealed"
                with self.assertRaisesRegex(BatchPackageError, message):
                    seal_outputs(request_package(), [output(model)], destination)
                self.assertFalse(destination.exists())

    def test_batch_validation_finishes_before_any_seal_is_written(self):
        package = build_request_package([
            {"id": "first", "source": SOURCE},
            {"id": "second", "source": SOURCE},
        ])
        good = output()
        good["id"] = "first"
        bad = output(sat_model())
        bad["id"] = "second"
        bad["model"]["objective_order"] = []
        with tempfile.TemporaryDirectory() as temp:
            destination = Path(temp) / "sealed"
            with self.assertRaisesRegex(BatchPackageError, "objective_order"):
                seal_outputs(package, [good, bad], destination)
            self.assertFalse(destination.exists())

    def test_malformed_package_and_source_or_api_drift_are_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            destination = Path(temp) / "sealed"
            with self.assertRaisesRegex(BatchPackageError, "package must be an object"):
                seal_outputs([], [], destination)
            self.assertFalse(destination.exists())

            request = request_package()["requests"][0]
            request["source"] = "changed after the request was sealed"
            with self.assertRaisesRegex(BatchPackageError, "source hash mismatch"):
                validate_output(request, output())

            request = request_package()["requests"][0]
            request["hir_schema"]["required"].remove("language")
            with self.assertRaisesRegex(BatchPackageError, "schema differs from live API"):
                validate_output(request, output())

            request = request_package()["requests"][0]
            request["operator_catalog"]["operations"].pop("eq")
            with self.assertRaisesRegex(BatchPackageError, "catalog differs from live API"):
                validate_output(request, output())

    def test_context_is_attached_only_to_validation_copy(self):
        request = request_package()["requests"][0]
        candidate = output()
        seen = {}

        def capture(model, source):
            seen["model"] = model
            seen["source"] = source
            return object()

        with patch("nl_hir_batch.build_hir", side_effect=capture):
            returned = validate_output(request, candidate)
        self.assertEqual(request["context"], seen["model"]["context"])
        self.assertEqual(SOURCE, seen["source"])
        self.assertNotIn("context", candidate["model"])
        self.assertNotIn("context", returned)

    def test_malformed_request_entries_do_not_write_partial_seals(self):
        for entry in [None, [], {"id": []}, {"id": {}}]:
            with self.subTest(entry=entry), tempfile.TemporaryDirectory() as temp:
                package = request_package()
                package["requests"] = [entry]
                destination = Path(temp) / "sealed"
                with self.assertRaises(BatchPackageError):
                    seal_outputs(package, [output()], destination)
                self.assertFalse(destination.exists())

        with tempfile.TemporaryDirectory() as temp:
            package = request_package()
            package.update(requests=[], denominator=0)
            destination = Path(temp) / "sealed"
            with self.assertRaisesRegex(BatchPackageError, "denominator"):
                seal_outputs(package, [], destination)
            self.assertFalse(destination.exists())


if __name__ == "__main__":
    unittest.main()
