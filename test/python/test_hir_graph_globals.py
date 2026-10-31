"""Small exhaustive oracle for exact HIR connected/dconnected globals."""
from _public_relation import public_relation
from itertools import product

import pytest
import z3

from somtparser._nl_model import ModelError
from somtparser import natural_language as sp
from somtparser.hir import hir_api, hir_schema
from somtparser.hir_cp import build_cp_hir


def var(name):
    return {"var": name}


def op(name, *args):
    return {"op": name, "args": list(args)}


def graph_constructor(kind, sources, targets, nodes, edges):
    return {"cp": kind, "from": list(sources), "to": list(targets),
            "nodes": [var(name) for name in nodes],
            "edges": [var(name) for name in edges]}


def lit(value):
    return {"literal": value, "sort": "Int"}


def model(expression, n, e):
    declarations = [
        {"name": f"n{i}", "sort": "Bool"} for i in range(n)
    ] + [
        {"name": f"e{i}", "sort": "Bool"} for i in range(e)
    ]
    return {
        "schema": "somt-hir-model-v1", "language": "hir",
        "decision": "satisfiability", "declarations": declarations,
        "functions": [], "constraints": [{"expr": expression, "span": [0, 1]}],
        "objectives": [], "objective_order": "single", "goal": None,
        "assumptions": [], "unresolved": [],
    }


def translated_relation(expression, n, e):
    translated = build_cp_hir(model(expression, n, e), "graph-global-test").translate()
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    return public_relation(translated)


def _reachable(nodes, edges, sources, targets, directed):
    selected_nodes = {i for i, yes in enumerate(nodes) if yes}
    if not selected_nodes:
        return False
    for selected, source, target in zip(edges, sources, targets):
        if selected and (source not in selected_nodes or target not in selected_nodes):
            return False
    for root in selected_nodes:
        reached = {root}
        changed = True
        while changed:
            changed = False
            for selected, source, target in zip(edges, sources, targets):
                if not selected:
                    continue
                neighbors = [(source, target)]
                if not directed:
                    neighbors.append((target, source))
                for start, finish in neighbors:
                    if start in reached and finish in selected_nodes and finish not in reached:
                        reached.add(finish)
                        changed = True
        if reached == selected_nodes:
            return True
    return False


def _oracle(sources, targets, node_vars, edge_vars, directed):
    n, e = len(node_vars), len(edge_vars)
    satisfying = []
    for bits in product((False, True), repeat=n + e):
        nodes, edges = bits[:n], bits[n:]
        if not _reachable(nodes, edges, sources, targets, directed):
            continue
        satisfying.append(z3.And(*[
            symbol if bit else z3.Not(symbol)
            for symbol, bit in zip(node_vars + edge_vars, bits)
        ]))
    return z3.Or(*satisfying)


def _check_equivalence(actual, expected):
    solver = z3.Solver()
    solver.set(timeout=10000)
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("kind,directed,sources,targets", [
    ("connected", False, (0, 1), (1, 2)),
    ("dconnected", True, (0, 2), (1, 1)),
    ("dconnected", True, (0, 1, 2), (1, 2, 0)),
])
def test_rank_witness_matches_exhaustive_small_graph_oracle(
    kind, directed, sources, targets
):
    n, e = 3, len(sources)
    node_names = [f"n{i}" for i in range(n)]
    edge_names = [f"e{i}" for i in range(e)]
    node_vars = [z3.Bool(name) for name in node_names]
    edge_vars = [z3.Bool(name) for name in edge_names]
    constructor = graph_constructor(kind, sources, targets, node_names, edge_names)
    _check_equivalence(
        translated_relation(constructor, n, e),
        _oracle(sources, targets, node_vars, edge_vars, directed),
    )
    negated = translated_relation(op("not", constructor), n, e)
    _check_equivalence(
        negated,
        z3.Not(_oracle(sources, targets, node_vars, edge_vars, directed)),
    )


def test_zero_and_one_node_graphs_and_edge_endpoint_closure():
    # Empty selected set is false, while a selected isolated singleton is true.
    empty = translated_relation(
        graph_constructor("connected", (), (), (), ()), 0, 0
    )
    assert z3.is_false(z3.simplify(empty))
    singleton = translated_relation(
        graph_constructor("dconnected", (), (), ("n0",), ()), 1, 0
    )
    n0 = z3.Bool("n0")
    _check_equivalence(singleton, n0)
    empty_negation = translated_relation(
        op("not", graph_constructor("dconnected", (), (), (), ())), 0, 0
    )
    assert z3.is_true(z3.simplify(empty_negation))


def test_flattened_native_hir_operator_uses_canonical_layout():
    expression = op("connected", lit(2), lit(1), lit(0), lit(1),
                    var("n0"), var("n1"), var("e0"))
    actual = translated_relation(expression, 2, 1)
    n0, n1, e0 = z3.Bools("n0 n1 e0")
    expected = _oracle((0,), (1,), [n0, n1], [e0], directed=False)
    _check_equivalence(actual, expected)


def test_cp_vector_lengths_endpoint_range_and_selector_sorts_are_checked():
    with pytest.raises(ModelError, match="length mismatch"):
        from somtparser.hir_cp import expand_cp_expression

        expand_cp_expression({
            "cp": "connected", "from": [0], "to": [],
            "nodes": [True], "edges": [True],
        })
    with pytest.raises(ModelError, match="outside zero-based"):
        from somtparser.hir_cp import expand_cp_expression

        expand_cp_expression({
            "cp": "connected", "from": [1], "to": [0],
            "nodes": [{"literal": True, "sort": "Bool"}],
            "edges": [{"literal": True, "sort": "Bool"}],
        })

    malformed = model(op("connected", lit(2), lit(1)), 2, 1)
    with pytest.raises(ModelError, match="argument count does not match"):
        build_cp_hir(malformed, "graph-arity-test")

    invalid = graph_constructor("connected", [0], [1], ["n0", "n1"], ["e0"])
    source = model(invalid, 2, 1)
    source["declarations"][0]["sort"] = "Int"
    with pytest.raises(ModelError, match="node selections require exact Bool sort"):
        build_cp_hir(source, "graph-type-test")


def test_graph_apis_are_discoverable_in_standard_nl_hir_request():
    candidate = model(
        graph_constructor("connected", [0], [1], ["n0", "n1"], ["e0"]),
        2,
        1,
    )
    seen = []
    proposal = sp.propose_nl(
        "Choose a connected selected subgraph.",
        language="hir",
        provider=lambda request: seen.append(request) or candidate,
    )
    assert proposal.valid, proposal.diagnostics
    assert len(seen) == 1
    request_api = seen[0]["schema"]["constructor_api"]
    # Provider responses omit the caller-owned context; serialized candidates
    # retain it. All remaining schema and constructor information must agree.
    serialized_schema = hir_schema()
    assert "context" in serialized_schema["properties"]
    serialized_schema["properties"].pop("context")
    assert "context" not in seen[0]["schema"]["properties"]
    assert seen[0]["schema"] == serialized_schema
    assert proposal.model["context"] == {}
    for operation in ("connected", "dconnected"):
        assert operation in request_api["operations"]
        assert operation in request_api["cp_constructors"]["constructors"]
        assert operation in hir_api()["cp_constructors"]["constructors"]
        assert operation in hir_schema()["constructor_api"]["operations"]
    compiled = sp.compile_candidate(proposal, accept_digest=proposal.digest)
    assert compiled.ok, compiled.diagnostics
