"""Align finite Bool/Int outputs without rewriting either model's relation.

Names and shapes must agree unless a caller supplies an explicit coordinate
map. Sparse reference cells must be listed explicitly; omitted candidate cells
must be explicitly hidden for existential projection. This adapter requires
``reconstruct=[]``; proved reconstructions belong to the lower-level coordinate
map API. This adapter does not infer coordinate mappings. Pass the returned
bridges, the original assertions, and any separate cost bridges to
``checker_adapter``.
"""
from dataclasses import dataclass
from itertools import product

from .coordinate_map import (
    ObservableMapRefusal,
    build_coordinate_map,
    fresh_observation_bridges,
    verify_reconstruction,
)
from .projection import free_constants


@dataclass(frozen=True)
class FiniteObservableAlignment:
    reference_bridges: tuple
    candidate_bridges: tuple
    embeddings: dict
    map_provenance: tuple


def _name(value, where):
    if not isinstance(value, str) or not value:
        raise ObservableMapRefusal("invalid-metadata", f"{where} must be a nonempty string")
    return value


def _shape(value, where):
    if not isinstance(value, (list, tuple)):
        raise ObservableMapRefusal("invalid-metadata", f"{where} shape must be a finite sequence")
    if any(type(size) is not int or size <= 0 for size in value):
        raise ObservableMapRefusal("invalid-metadata", f"{where} dimensions must be positive integers")
    return tuple(value)


def _indices(shape):
    return tuple(product(*(range(size) for size in shape)))


def _reference_records(metadata):
    if not isinstance(metadata, dict) or not isinstance(metadata.get("observables"), list):
        raise ObservableMapRefusal("invalid-metadata", "reference observables must be an explicit list")
    records = {}
    symbol_sorts = {}
    for observable in metadata["observables"]:
        if not isinstance(observable, dict):
            raise ObservableMapRefusal("invalid-metadata", "each reference observable must be an object")
        name = _name(observable.get("name"), "reference observable name")
        if name in records:
            raise ObservableMapRefusal("duplicate-observable", f"reference observable {name!r} is repeated")
        shape = _shape(observable.get("shape"), f"reference {name}")
        elements = observable.get("elements")
        if not isinstance(elements, list):
            raise ObservableMapRefusal("invalid-metadata", f"reference {name} elements must be a list")
        cells = {}
        sort = None
        for element in elements:
            if not isinstance(element, dict):
                raise ObservableMapRefusal("invalid-metadata", f"reference {name} element must be an object")
            index = element.get("index")
            if (not isinstance(index, (list, tuple))
                    or any(type(i) is not int for i in index)):
                raise ObservableMapRefusal("invalid-metadata", f"reference {name} index must be an integer sequence")
            index = tuple(index)
            if len(index) != len(shape) or any(i < 0 or i >= n for i, n in zip(index, shape)):
                raise ObservableMapRefusal("invalid-metadata", f"reference {name} index {index} is outside shape {shape}")
            if index in cells:
                raise ObservableMapRefusal("duplicate-reference-coordinate", f"reference {name} repeats index {index}")
            element_sort = element.get("sort")
            if element_sort not in ("Bool", "Int"):
                raise ObservableMapRefusal("unsupported-sort", "finite observables support Bool and Int only")
            if sort is not None and element_sort != sort:
                raise ObservableMapRefusal("sort-mismatch", f"reference {name} has mixed element sorts")
            sort = element_sort
            symbol = _name(element.get("symbol"), f"reference {name} symbol")
            if symbol in symbol_sorts and symbol_sorts[symbol] != sort:
                raise ObservableMapRefusal("sort-mismatch", f"reference symbol {symbol!r} has conflicting sorts")
            # Repeated symbols at different coordinates express an existing
            # reference alias; both coordinates still get separate bridges.
            symbol_sorts[symbol] = sort
            cells[index] = symbol
        sparse = observable.get("sparse", False)
        if type(sparse) is not bool:
            raise ObservableMapRefusal("invalid-metadata", f"reference {name} sparse flag must be Boolean")
        if sparse:
            if not cells:
                raise ObservableMapRefusal("reference-coverage", f"sparse reference {name} must contain at least one observed element")
        elif set(cells) != set(_indices(shape)):
            raise ObservableMapRefusal("reference-coverage", f"reference {name} elements must cover every coordinate exactly unless sparse=true")
        if "sort" in observable and observable["sort"] != sort:
            raise ObservableMapRefusal("sort-mismatch", f"reference {name} sort disagrees with its elements")
        records[name] = {"name": name, "shape": shape, "sort": sort,
                         "cells": cells, "sparse": sparse}
    return records


def _candidate_declarations(payload):
    model = payload.get("model") if isinstance(payload, dict) else None
    declarations = model.get("declarations") if isinstance(model, dict) else None
    if not isinstance(declarations, list):
        raise ObservableMapRefusal("invalid-metadata", "candidate model.declarations must be an explicit list")
    records = {}
    for declaration in declarations:
        if not isinstance(declaration, dict):
            raise ObservableMapRefusal("invalid-metadata", "candidate declaration must be an object")
        name = _name(declaration.get("name"), "candidate declaration name")
        if name in records:
            raise ObservableMapRefusal("duplicate-declaration", f"candidate declaration {name!r} is repeated")
        # Only selected finite outputs need this adapter's shape restrictions.
        # Hidden HIR declarations may have empty domains or other encodings.
        shape = declaration.get("shape", [])
        records[name] = {"name": name, "shape": shape, "sort": declaration.get("sort")}
    return records


def _context(reference_assertions, candidate_assertions, objectives):
    import z3
    expressions = reference_assertions + candidate_assertions + objectives
    if any(not z3.is_expr(expr) for expr in expressions):
        raise ObservableMapRefusal("invalid-proof-context", "assertions and objectives must be Z3 expressions")
    ctx = expressions[0].ctx if expressions else z3.main_ctx()
    if any(expr.ctx is not ctx for expr in expressions):
        raise ObservableMapRefusal("proof-context-mismatch", "all assertions and objectives must share one Z3 context")
    if any(not z3.is_bool(expr) for expr in reference_assertions + candidate_assertions):
        raise ObservableMapRefusal("invalid-proof-context", "assertions must be Boolean formulas")
    return ctx


def _constants_by_name(expressions):
    constants = {}
    for term in free_constants(expressions):
        constants.setdefault(str(term.decl().name()), []).append(term)
    return constants


def _constant(name, sort, constants, where):
    import z3
    actual = constants.get(name, ())
    if any(term.sort() != sort for term in actual):
        raise ObservableMapRefusal("sort-mismatch", f"{where} {name!r} disagrees with the actual SMT constant sort")
    # A declared output absent from the formulas is unconstrained. Creating
    # its free constant preserves that fact instead of inventing a constraint.
    return actual[0] if actual else z3.Const(name, sort)


def _leaf_sort(name, ctx):
    import z3
    if name == "Bool":
        return z3.BoolSort(ctx=ctx)
    if name == "Int":
        return z3.IntSort(ctx=ctx)
    raise ObservableMapRefusal("unsupported-sort", "finite observables support Bool and Int only")


def _candidate_terms(record, constants, ctx):
    import z3
    sort = _leaf_sort(record["sort"], ctx)
    for _ in record["shape"]:
        sort = z3.ArraySort(z3.IntSort(ctx=ctx), sort)
    root = _constant(record["name"], sort, constants, "candidate declaration")
    terms = {}
    for index in _indices(record["shape"]):
        term = root
        for coordinate in index:
            term = z3.Select(term, z3.IntVal(coordinate, ctx=ctx))
        terms[index] = term
    return terms


def _integer_embedding(terms, ctx):
    import z3
    return {index: z3.If(term, z3.IntVal(1, ctx=ctx), z3.IntVal(0, ctx=ctx))
            for index, term in terms.items()}


def align_finite_observables(reference_metadata, candidate_payload, *,
                             reference_assertions, candidate_assertions,
                             reference_objectives=(), candidate_objectives=(),
                             coordinate_maps=()):
    """Return shared fresh observation bridges and an auditable map receipt.

    Maps use ``coordinate_map.build_coordinate_map``'s format with
    ``reconstruct=[]`` required. Sparse reference
    metadata lists observed coordinates through its element records; every
    observed reference and mapped candidate cell must occur exactly once. Any
    omitted candidate cell must be explicitly hidden. Unmapped
    reference names use same-name, same-shape identity. Additional candidate
    declarations stay hidden by the existing relational projection; their
    assertions are never removed.

    Mixed Bool/Int observations share an Int coordinate by embedding only
    Bool as ``If(b, 1, 0)``. Int values outside 0/1 remain visible. Both sides' objectives
    participate in constant discovery and freshness protection only; this
    function neither maps objectives nor returns a replacement cost term.
    """
    references = _reference_records(reference_metadata)
    declarations = _candidate_declarations(candidate_payload)
    ref_assertions = list(reference_assertions)
    cand_assertions = list(candidate_assertions)
    ref_objectives = list(reference_objectives)
    cand_objectives = list(candidate_objectives)
    ctx = _context(ref_assertions, cand_assertions, ref_objectives + cand_objectives)
    ref_constants = _constants_by_name(ref_assertions + ref_objectives)
    cand_constants = _constants_by_name(cand_assertions + cand_objectives)

    if not isinstance(coordinate_maps, (list, tuple)):
        raise ObservableMapRefusal("invalid-map", "coordinate_maps must be a sequence of explicit maps")
    explicit = {}
    for mapping in coordinate_maps:
        if not isinstance(mapping, dict):
            raise ObservableMapRefusal("invalid-map", "each coordinate map must be an object")
        ref_name = _name(mapping.get("reference_name"), "map reference name")
        cand_name = _name(mapping.get("candidate_name"), "map candidate name")
        if ref_name not in references:
            raise ObservableMapRefusal("unknown-reference", f"map refers to unknown reference {ref_name!r}")
        if cand_name not in declarations:
            raise ObservableMapRefusal("undeclared-candidate", f"map refers to undeclared candidate {cand_name!r}")
        if ref_name in explicit:
            raise ObservableMapRefusal("duplicate-map", f"reference {ref_name!r} has more than one map")
        if not isinstance(mapping.get("reconstruct"), list) or mapping["reconstruct"]:
            raise ObservableMapRefusal("reconstruction-not-supported", "finite observable alignment requires reconstruct=[]")
        explicit[ref_name] = mapping

    plans = []
    provenance = []
    embeddings = {}
    used_candidates = set()
    all_terms = []
    for ref_name, reference in references.items():
        mapping = explicit.get(ref_name)
        if mapping is None and reference["sparse"]:
            raise ObservableMapRefusal("invalid-map", "sparse observables require an explicit coordinate map")
        cand_name = mapping["candidate_name"] if mapping is not None else ref_name
        if cand_name not in declarations:
            raise ObservableMapRefusal("undeclared-candidate", f"candidate output {cand_name!r} is not declared")
        if cand_name in used_candidates:
            raise ObservableMapRefusal("duplicate-candidate-observable", f"candidate output {cand_name!r} is mapped more than once")
        used_candidates.add(cand_name)
        candidate = dict(declarations[cand_name])
        candidate["shape"] = _shape(candidate["shape"], f"candidate {cand_name}")
        is_explicit = mapping is not None
        if mapping is None:
            if reference["shape"] != candidate["shape"]:
                raise ObservableMapRefusal("shape-mismatch", f"output {ref_name!r} requires an explicit map for differing shapes")
            mapping = {
                "reference_name": ref_name,
                "candidate_name": cand_name,
                "coordinates": [{"reference_index": list(index), "candidate_index": list(index)}
                                for index in _indices(reference["shape"])],
                "reconstruct": [],
            }
        ref_sort = _leaf_sort(reference["sort"], ctx)
        ref_terms = {index: _constant(symbol, ref_sort, ref_constants, "reference symbol")
                     for index, symbol in reference["cells"].items()}
        cand_terms = _candidate_terms(candidate, cand_constants, ctx)
        all_terms.extend(ref_terms.values())
        all_terms.extend(cand_terms.values())
        common_sort = reference["sort"]
        if reference["sort"] != candidate["sort"]:
            common_sort = "Int"
            if reference["sort"] == "Bool":
                ref_terms = _integer_embedding(ref_terms, ctx)
            if candidate["sort"] == "Bool":
                cand_terms = _integer_embedding(cand_terms, ctx)
            key = f"{reference['sort']}-to-{candidate['sort']}"
            embeddings[key] = embeddings.get(key, 0) + len(ref_terms)
        normalized_ref = {"name": ref_name, "shape": reference["shape"], "sort": common_sort,
                          "sparse": reference["sparse"]}
        if reference["sparse"]:
            normalized_ref["observed_indices"] = [list(index) for index in reference["cells"]]
        normalized_cand = {"name": cand_name, "shape": candidate["shape"], "sort": common_sort}
        plan = build_coordinate_map(normalized_ref, normalized_cand, mapping, ref_terms, cand_terms)
        plans.append(plan)
        provenance.append({
            "kind": "explicit" if is_explicit else "identity",
            "reference_name": ref_name, "candidate_name": cand_name,
            "reference_shape": list(reference["shape"]), "candidate_shape": list(candidate["shape"]),
            "reference_sort": reference["sort"], "candidate_sort": candidate["sort"],
            "coordinate_sort": common_sort,
            "coordinates": [{"reference_index": list(pair.reference_index),
                             "candidate_index": list(pair.candidate_index)} for pair in plan.pairs],
            "reconstruct": [],
            "hidden_candidate_indices": [list(index) for index in plan.hidden_candidate_indices],
        })
        if reference["sparse"]:
            provenance[-1]["sparse"] = True

    # The helper scans these expressions only to avoid alias collisions. The
    # tautologies protect terms belonging to other maps and objective-only
    # constants; they are NOT returned or added to either model's relation.
    protection = ref_assertions + [term == term for term in all_terms + ref_objectives + cand_objectives]
    reference_bridges = []
    candidate_bridges = []
    for plan, receipt in zip(plans, provenance):
        verified = verify_reconstruction(plan, cand_assertions)
        bridges = fresh_observation_bridges(
            verified, protection, cand_assertions, prefix="finite_observable")
        reference_bridges.extend(bridges.reference_bridges)
        candidate_bridges.extend(bridges.candidate_bridges)
        protection.extend(alias == alias for alias in bridges.aliases)
        # Record the exact fresh symbols at creation. Diagnostic readers must
        # never guess this binding from generated-name suffixes or term order.
        receipt["aliases"] = [
            {"symbol": alias.sexpr(), "sort": alias.sort().sexpr(),
             "reference_index": list(pair.reference_index),
             "candidate_index": list(pair.candidate_index)}
            for alias, pair in zip(bridges.aliases, plan.pairs)]
    return FiniteObservableAlignment(tuple(reference_bridges), tuple(candidate_bridges),
                                     embeddings, tuple(provenance))
