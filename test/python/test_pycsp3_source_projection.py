"""Reference compiler provenance and independent projected relation controls."""
from pathlib import Path
import copy
import hashlib
import importlib.util
import json
import os
import subprocess
import sys

import pytest

pytestmark = pytest.mark.skipif(importlib.util.find_spec("pycsp3") is None,
                                reason="optional PyCSP3 reference exporter is not installed")


ROOT = Path(__file__).resolve().parents[2]
TOOL = ROOT / "tools/pycsp3_source_projection.py"
SPEC = importlib.util.spec_from_file_location("pycsp3_source_projection", TOOL)
adapter = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(adapter)

MODEL = """from pycsp3 import *
y = VarArray(size=2, dom=range(3))
aux_gb_user = Var(dom=range(2))
satisfy(NoOverlap(origins=([0, 0], y), lengths=([1, 1], [1, 1])))
minimize(Sum(y) + aux_gb_user)
"""


def export(tmp_path, source=MODEL, *, extra_files=None):
    model = tmp_path / "model.py"
    model.write_text(source)
    data = tmp_path / "data.json"
    data.write_text("{}\n")
    for name, text in (extra_files or {}).items():
        (tmp_path / name).write_text(text)
    command = [sys.executable, "-B", str(TOOL), "export", "--model", str(model),
               "--data", str(data), "--cwd", str(tmp_path),
               "--xml", str(tmp_path / "reference.xml"),
               "--provenance", str(tmp_path / "provenance.json")]
    result = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            text=True, env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"))
    assert result.returncode == 0, result.stdout
    provenance = json.loads((tmp_path / "provenance.json").read_text())
    assert provenance["model"]["sha256"] == hashlib.sha256(source.encode()).hexdigest()
    assert model.read_text() == source
    assert provenance["xml"]["sha256"] == hashlib.sha256((tmp_path / "reference.xml").read_bytes()).hexdigest()
    return provenance


@pytest.fixture(scope="module")
def reference(tmp_path_factory):
    directory = tmp_path_factory.mktemp("source-projection")
    return directory, export(directory)


def legacy_metadata(provenance):
    return dict(observables=[dict(name=entity["name"], shape=entity["shape"], elements=[
        dict(index=e["index"], symbol=e["source_symbol"], sort="Int")
        for e in entity["elements"]]) for entity in provenance["entities"]],
        has_objective=True, objectives=[dict(direction="min", expr="sum(y)+aux_gb_user", offset="-7/3")],
        reference_sha256="exact-SMT-digest")


def test_compiler_registry_not_name_prefix(reference):
    _, provenance = reference
    assert set(provenance["public_source_symbols"]) == {"y[0]", "y[1]", "aux_gb_user"}
    assert len(provenance["compiler_private_symbols"]) == 2
    for variable in provenance["variables"]:
        if variable["role"] == "compiler-private":
            assert variable["auxiliary_registry_member"] is True
            assert variable["explicit_source_bindings"] == []
        else:
            assert variable["explicit_source_bindings"]


def test_projected_metadata_preserves_costs_and_original_bytes(reference):
    _, provenance = reference
    metadata = legacy_metadata(provenance)
    before = copy.deepcopy(metadata)
    projected = adapter.project_observables(metadata, provenance)
    assert metadata == before
    assert {x["name"] for x in projected["observables"]} == {"y", "aux_gb_user"}
    for field in ("objectives", "has_objective", "reference_sha256"):
        assert projected[field] == metadata[field]
    assert projected["source_projection"]["constraints_changed"] is False
    assert projected["source_projection"]["objectives_changed"] is False


def test_actual_aux_name_is_public_when_author_declares_it(tmp_path):
    p = export(tmp_path, "from pycsp3 import *\naux_gb = Var(dom=range(2))\nsatisfy(aux_gb == 1)\n")
    assert p["public_source_symbols"] == ["aux_gb"]
    assert p["compiler_private_symbols"] == []
    assert adapter.project_observables(legacy_metadata(p), p)["observables"][0]["name"] == "aux_gb"


def test_factory_provenance_also_covers_non_auxiliary_spelling(tmp_path):
    source = MODEL.replace("y = VarArray", "from pycsp3.classes.main.constraints import auxiliary\nauxiliary().prefix = 'hidden_normalized'\ny = VarArray")
    p = export(tmp_path, source)
    assert set(p["compiler_private_symbols"]) == {"hidden_normalized[0]", "hidden_normalized[1]"}
    projected = adapter.project_observables(legacy_metadata(p), p)
    assert {o["name"] for o in projected["observables"]} == {"y", "aux_gb_user"}


def test_explicit_source_reference_to_factory_variable_stays_public(tmp_path):
    p = export(tmp_path, """from pycsp3 import *
from pycsp3.classes.main.variables import Domain
x = Var()
x.dom = Domain(range(3))
satisfy(x == 1)
""")
    assert len(p["public_source_symbols"]) == 1
    assert p["compiler_private_symbols"] == []
    assert p["variables"][0]["auxiliary_registry_member"]
    assert "x" in p["variables"][0]["explicit_source_bindings"]


def test_full_problem_cwd_and_import_path_are_preserved(tmp_path):
    p = export(tmp_path, """from pycsp3 import *
from local_data import LIMIT
with open('value.txt') as source:
    expected = int(source.read())
x = Var(dom=range(LIMIT))
satisfy(x == expected)
""", extra_files={"local_data.py": "LIMIT = 3\n", "value.txt": "2\n"})
    assert p["public_source_symbols"] == ["x"]
    assert Path(p["cwd"]) == tmp_path


def test_explicit_full_renaming_is_applied_without_guessing(reference):
    _, p = reference
    metadata = legacy_metadata(p)
    mapping = {row["source_symbol"]: "target_" + str(i) for i, row in enumerate(p["variables"])}
    for observation in metadata["observables"]:
        for element in observation["elements"]:
            element["symbol"] = mapping[element["symbol"]]
    with pytest.raises(ValueError, match="no captured source variable"):
        adapter.project_observables(metadata, p)
    projected = adapter.project_observables(metadata, p, mapping)
    assert {e["symbol"] for o in projected["observables"] for e in o["elements"]} == {
        mapping[s] for s in p["public_source_symbols"]}


@pytest.mark.parametrize("mutation", ["unknown", "duplicate", "missing-public", "ambiguous-map"])
def test_bad_projection_contracts_are_rejected(reference, mutation):
    _, p = reference
    metadata = legacy_metadata(p)
    mapping = None
    if mutation == "unknown":
        metadata["observables"][0]["elements"][0]["symbol"] = "unaccounted"
    elif mutation == "duplicate":
        metadata["observables"].append(copy.deepcopy(metadata["observables"][0]))
    elif mutation == "missing-public":
        metadata["observables"] = [o for o in metadata["observables"] if o["name"] != "y"]
    else:
        mapping = {s: "one-symbol" for s in (v["source_symbol"] for v in p["variables"])}
    with pytest.raises(ValueError):
        adapter.project_observables(metadata, p, mapping)


def test_sparse_source_array_holes_are_not_invented(tmp_path):
    p = export(tmp_path, """from pycsp3 import *
x = VarArray(size=3, dom=lambda i: range(2) if i != 1 else None)
satisfy(x[0] != x[2])
""")
    assert p["public_source_symbols"] == ["x[0]", "x[2]"]
    projected = adapter.project_observables(legacy_metadata(p), p)
    assert projected["observables"][0]["shape"] == [3]
    assert [e["index"] for e in projected["observables"][0]["elements"]] == [[0], [2]]


def test_complete_projected_relation_and_signed_cost(reference):
    import somtparser as sp
    import z3
    from z3.z3util import get_vars

    directory, provenance = reference
    source = (directory / "reference.xml").read_text()
    translated = sp.translate(source=source, language="xcsp3", dialect=sp.OmtDialect.Z3)
    assert translated.ok, translated.diagnostic_items
    script = translated.to_smt2(dialect=sp.OmtDialect.Z3)
    optimize = z3.Optimize()
    optimize.from_string(script)
    assert len(optimize.objectives()) == 1
    y0, y1, user = (z3.Int(name) for name in ("y[0]", "y[1]", "aux_gb_user"))
    expected = z3.And(y0 >= 0, y0 <= 2, y1 >= 0, y1 <= 2, user >= 0, user <= 1, z3.Or(y0 >= 1, y1 >= 1))
    actual = z3.And(*optimize.assertions())
    public = {"y[0]", "y[1]", "aux_gb_user"}
    variables = get_vars(z3.And(actual, optimize.objectives()[0] == z3.Int("__cost_probe")))
    private = [v for v in variables if str(v.decl().name()) not in public | {"__cost_probe"}]
    assert set(provenance["compiler_private_symbols"]).issubset({str(v.decl().name()) for v in private})
    projected = z3.Exists(private, actual)
    # PyCSP3 keeps the two 2D origin vectors (0,0) and (y0,y1).
    # Two unit rectangles may meet at a boundary but must not overlap.
    for x, y, wanted in ((1, 1, z3.sat), (0, 0, z3.unsat)):
        witness = z3.Solver()
        witness.add(projected, y0 == x, y1 == y, user == 0)
        assert witness.check() == wanted
    solver = z3.Solver()
    solver.add(z3.Xor(projected, expected))
    assert solver.check() == z3.unsat
    cost = z3.Int("__cost_probe")
    actual_cost = z3.Exists(private, z3.And(actual, cost == optimize.objectives()[0]))
    expected_cost = z3.And(expected, cost == y0 + y1 + user)
    solver = z3.Solver()
    solver.add(z3.Xor(actual_cost, expected_cost))
    assert solver.check() == z3.unsat
    # A wrong source constraint or cost remains detectable after hiding helpers.
    for original, mutant in ((projected, z3.And(expected, y0 == 0)),
                             (actual_cost, z3.And(expected, cost == y0 + y1 + user + 1))):
        solver = z3.Solver()
        solver.add(z3.Xor(original, mutant))
        assert solver.check() == z3.sat
