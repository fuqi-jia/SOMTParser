import json
from pathlib import Path
import shutil

import pytest
from somtparser._nl_model import ModelError
from somtparser.nl_datasets import (
    IndusCPTask,
    induscp_expected_objective,
    induscp_required_variant,
    induscp_statements,
    induscp_tasks,
)


STATEMENT = {
    "problem": "toy problem",
    "code": "from pycsp3 import *\nx = data\n",
    "constraints": [],
}
VARIANT_CODE = (
    "from pycsp3 import *\nassert variant() in {\"english\", \"french\"}\nx = data\n"
)


def make_repo(tmp_path, statements, files):
    root = tmp_path / "ConstraintLLM"
    cost = root / "data" / "induscp" / "cost_data"
    shutil.rmtree(cost, ignore_errors=True)
    cost.mkdir(parents=True, exist_ok=True)
    (root / "data" / "induscp" / "statements.json").write_text(
        json.dumps(statements), encoding="utf-8"
    )
    for problem, members in files.items():
        directory = cost / problem
        directory.mkdir(exist_ok=True)
        for name, content in members.items():
            (directory / name).write_text(content, encoding="utf-8")
    return root


def test_task_discovery_orders_and_reads_expected_values(tmp_path):
    statements = [
        dict(STATEMENT, name="Beta", code=VARIANT_CODE),
        dict(STATEMENT, name="Alpha"),
    ]
    root = make_repo(
        tmp_path,
        statements,
        {
            "Beta": {"0.json": "{\"x\": 1}"},
            "Alpha": {
                "1.json": "{\"x\": 2}",
                "0.json": "{\"x\": 1}",
                "0.out": "7\n",
                "Alpha.py": "# upstream copy, not the executed reference\n",
                "README.md": "# Problem Alpha\n",
            },
        },
    )
    tasks = list(induscp_tasks(root))
    assert [(t.problem, t.instance) for t in tasks] == [
        ("Alpha", "0"),
        ("Alpha", "1"),
        ("Beta", "0"),
    ]
    assert tasks[0].expected == 7
    assert tasks[1].expected is None
    assert tasks[0].extra_args == ()
    assert tasks[2].extra_args == ("-variant=english",)
    assert tasks[0].model == STATEMENT["code"]
    assert tasks[0].data_path.name == "0.json"


def test_discovery_rejects_inconsistent_trees(tmp_path):
    root = make_repo(tmp_path, [dict(STATEMENT, name="Alpha")], {})
    with pytest.raises(ModelError, match="no cost_data directory"):
        list(induscp_tasks(root))
    root = make_repo(
        tmp_path, [dict(STATEMENT, name="Alpha")], {"Alpha": {"x.json": "{}"}}
    )
    with pytest.raises(ModelError, match="non-integer"):
        list(induscp_tasks(root))
    root = make_repo(
        tmp_path, [dict(STATEMENT, name="Alpha")], {"Alpha": {"0.json": "{}", "0.out": ""}}
    )
    with pytest.raises(ModelError, match="expected objective"):
        list(induscp_tasks(root))
    root = make_repo(
        tmp_path,
        [dict(STATEMENT, name="Alpha"), dict(STATEMENT, name="Alpha")],
        {"Alpha": {"0.json": "{}"}},
    )
    with pytest.raises(ModelError, match="duplicate"):
        list(induscp_tasks(root))
    root = make_repo(tmp_path, [], {"Ghost": {"0.json": "{}"}})
    with pytest.raises(ModelError, match="without a statement"):
        list(induscp_tasks(root))
    root = make_repo(tmp_path, [dict(STATEMENT, name="Alpha")], {"Alpha": {}})
    with pytest.raises(ModelError, match="no instances"):
        list(induscp_tasks(root))


def test_statements_require_name_and_unique_code(tmp_path):
    root = tmp_path / "ConstraintLLM"
    data = root / "data" / "induscp"
    data.mkdir(parents=True)
    (data / "statements.json").write_text(json.dumps({"name": "Alpha"}))
    with pytest.raises(ModelError, match="not a list"):
        induscp_statements(root)
    (data / "statements.json").write_text(json.dumps([{"name": "Alpha"}]))
    with pytest.raises(ModelError, match="lacks a name or reference code"):
        induscp_statements(root)


def test_required_variant_only_from_assertions():
    assert induscp_required_variant(VARIANT_CODE) == "english"
    assert (
        induscp_required_variant(
            "from pycsp3 import *\nassert variant() in ('aux', 'table')\n"
        )
        == "aux"
    )
    assert induscp_required_variant("from pycsp3 import *\nx = variant('bis')\n") is None
    assert induscp_required_variant("from pycsp3 import *\nx = data\n") is None
    with pytest.raises(ModelError, match="variant assertion"):
        induscp_required_variant("assert variant() in {x, y}\n")


def test_expected_objective_parsing():
    assert induscp_expected_objective(None) is None
    assert induscp_expected_objective("4") == 4
    assert induscp_expected_objective("  -12\n") == -12
    for bad in ("", "4.5", "sat", "4 5"):
        with pytest.raises(ModelError, match="expected objective"):
            induscp_expected_objective(bad)






























