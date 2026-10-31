"""Explain a comparison tuple using recorded bridges, without changing verdicts.

This module does not solve, complete models, infer encodings, or parse a printed
model. Diagnostics describe the shared observation tuple, not two separately
satisfying source models: one side of a counterexample excludes that tuple.
"""
from copy import deepcopy
from dataclasses import asdict, is_dataclass


def scalar_model_values(model):
    """Capture only explicitly interpreted, closed scalar constants.

    In particular, never use model_completion: unconstrained coordinates must
    remain unknown. Arrays, function interpretations, and non-literal algebraic
    values are not converted to guessed scalar assignments.
    """
    import z3
    values = []
    for declaration in model.decls():
        if declaration.arity() != 0:
            continue
        value = model[declaration]
        if not (z3.is_true(value) or z3.is_false(value)
                or z3.is_int_value(value) or z3.is_rational_value(value)
                or z3.is_bv_value(value)):
            continue
        symbol = z3.Const(declaration.name(), declaration.range()).sexpr()
        values.append((symbol, declaration.range().sexpr(), value.sexpr()))
    return tuple(sorted(values))


def _index(value):
    if not isinstance(value, (list, tuple)) or any(type(i) is not int or i < 0 for i in value):
        raise ValueError("a recorded coordinate must be a nonnegative integer sequence")
    return tuple(value)


def _bindings(provenance):
    """Validate exact recorded aliases; missing old receipts stay unavailable."""
    bindings, missing, symbols = [], [], set()
    for receipt in provenance:
        if receipt.get("kind") not in ("identity", "explicit"):
            raise ValueError("only an existing identity or explicit coordinate receipt is supported")
        aliases = receipt.get("aliases")
        if aliases is None:
            missing.append({"reference_name": receipt["reference_name"],
                            "candidate_name": receipt["candidate_name"],
                            "reason": "historical receipt has no fresh-symbol bindings"})
            continue
        coordinates = {(_index(pair["reference_index"]), _index(pair["candidate_index"]))
                       for pair in receipt["coordinates"]}
        if len(coordinates) != len(receipt["coordinates"]) or len(aliases) != len(coordinates):
            raise ValueError("recorded aliases must cover the coordinate receipt exactly")
        seen = set()
        for alias in aliases:
            pair = (_index(alias["reference_index"]), _index(alias["candidate_index"]))
            symbol, sort = alias["symbol"], alias["sort"]
            if (pair not in coordinates or pair in seen or not isinstance(symbol, str)
                    or not symbol or symbol in symbols or sort != receipt["coordinate_sort"]):
                raise ValueError("ambiguous or inconsistent fresh-symbol binding")
            seen.add(pair)
            symbols.add(symbol)
            if receipt["kind"] == "identity" and (pair[0] != pair[1]
                    or receipt["reference_name"] != receipt["candidate_name"]):
                raise ValueError("non-identity alignment requires an explicit receipt")
            bindings.append((receipt, alias))
    return bindings, missing


def _side(name, index, sort, coordinate_sort, value):
    result = dict(name=name, index=list(index), sort=sort,
                  status="unknown", value=None)
    if value is None:
        return result
    if sort == coordinate_sort:
        result.update(status="assigned", value=value)
    elif sort == "Bool" and coordinate_sort == "Int":
        if value in ("0", "1"):
            result.update(status="assigned", value="true" if value == "1" else "false")
        else:
            result.update(status="outside-Boolean-embedding", value=None)
    else:
        raise ValueError("unsupported observation embedding in diagnostic receipt")
    return result


def describe_counterexample(comparison, map_provenance, *, cost_coordinates=()):
    """Return JSON-compatible metadata; input results and maps remain untouched.

    cost_coordinates must be caller-recorded cost bridge descriptions with a
    symbol and sort. Their reference/candidate directions and signed expressions
    are retained verbatim. No offset or optimization-direction normalization is
    performed here. Value-dependent encodings (such as inverse permutations)
    cannot be inferred from names or from this fixed coordinate map.
    """
    result = asdict(comparison) if is_dataclass(comparison) else deepcopy(comparison)
    bindings, missing = _bindings(map_provenance)
    costs = deepcopy(list(cost_coordinates))
    used = {alias["symbol"] for _, alias in bindings}
    for cost in costs:
        if (not isinstance(cost.get("symbol"), str) or not cost["symbol"]
                or cost["symbol"] in used or cost.get("sort") not in ("Int", "Real")):
            raise ValueError("cost metadata requires a distinct recorded numeric alias")
        used.add(cost["symbol"])
    output = dict(version=1, diagnostic_only=True, verdict_unchanged=True,
                  status=result["status"], equivalent=result["equivalent"],
                  tuple_scope="shared observation coordinates, not two satisfying source models",
                  mapping_policy="recorded bridges only; no inverse or offset inference",
                  unavailable_mappings=missing, directions=[])
    if result["status"] != "counterexample":
        return output
    for key, admitted, excluded in (("left_implies_right", "reference", "candidate"),
                                     ("right_implies_left", "candidate", "reference")):
        direction = result[key]
        if direction.get("counterexample_conjunct") is None:
            continue
        assignments = {}
        for symbol, sort, value in direction.get("counterexample_values", ()):
            if symbol in assignments or not all(isinstance(x, str) for x in (symbol, sort, value)):
                raise ValueError("ambiguous scalar witness assignment")
            assignments[symbol] = (sort, value)
        rows = []
        for receipt, alias in bindings:
            assignment = assignments.get(alias["symbol"])
            if assignment is not None and assignment[0] != alias["sort"]:
                raise ValueError("model assignment and bridge sorts disagree")
            value = assignment[1] if assignment else None
            rows.append(dict(symbol=alias["symbol"], sort=alias["sort"],
                             status="assigned" if assignment else "unknown", value=value,
                             map_kind=receipt["kind"],
                             reference=_side(receipt["reference_name"], alias["reference_index"],
                                             receipt["reference_sort"], alias["sort"], value),
                             candidate=_side(receipt["candidate_name"], alias["candidate_index"],
                                             receipt["candidate_sort"], alias["sort"], value)))
        objective_rows = []
        for cost in costs:
            row = deepcopy(cost)
            assignment = assignments.get(cost["symbol"])
            if assignment is not None and assignment[0] != cost["sort"]:
                raise ValueError("model assignment and cost sorts disagree")
            row.update(status="assigned" if assignment else "unknown",
                       value=assignment[1] if assignment else None)
            objective_rows.append(row)
        output["directions"].append(dict(
            direction=key, admitted_by=admitted, excluded_by=excluded,
            failed_obligation=direction["counterexample_conjunct"],
            raw_model=direction.get("counterexample_model"),
            scalar_assignment_capture_available="counterexample_values" in direction,
            observations=rows, objectives=objective_rows))
    return output


def write_sidecar(comparison_path, alignment_path, output_path, *, costs_path=None):
    """Create a new sidecar bound to exact input bytes; never replace a record."""
    import hashlib
    import json
    from pathlib import Path
    paths = [Path(comparison_path), Path(alignment_path)]
    if costs_path is not None:
        paths.append(Path(costs_path))
    output = Path(output_path)
    if any(output.resolve() == path.resolve() for path in paths):
        raise ValueError("diagnostic output must be separate from its evidence")
    raw = [path.read_bytes() for path in paths]
    comparison, alignment = [json.loads(data) for data in raw[:2]]
    maps = alignment["maps"] if isinstance(alignment, dict) else alignment
    costs = json.loads(raw[2]) if len(raw) == 3 else []
    diagnostic = describe_counterexample(comparison, maps, cost_coordinates=costs)
    diagnostic["input_evidence"] = [
        dict(path=str(path), sha256=hashlib.sha256(data).hexdigest(), bytes=len(data))
        for path, data in zip(paths, raw)]
    with output.open("x", encoding="utf-8") as stream:
        json.dump(diagnostic, stream, indent=2)
        stream.write("\n")
    return diagnostic


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("comparison")
    parser.add_argument("alignment")
    parser.add_argument("output")
    parser.add_argument("--costs")
    args = parser.parse_args()
    write_sidecar(args.comparison, args.alignment, args.output, costs_path=args.costs)
