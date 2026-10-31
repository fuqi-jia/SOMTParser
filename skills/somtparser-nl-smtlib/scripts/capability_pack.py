"""On-demand skill resources and live HIR capability views.

This module retrieves documentation and constructs prompt packets. It neither
chooses capabilities from a gold model nor changes native compiler support.
"""
from copy import deepcopy
import argparse
import hashlib
import json
from pathlib import Path
import sys


ROUTES = ("hir", "smtlib2", "hybrid")
RESOURCE_ROOT = Path(__file__).resolve().parents[1] / "references"
DOCUMENTS = {
    "semantics.core": ("semantics.md", "Source clauses, domains, units and interpretation boundaries"),
    "domain.linear": ("linear-omt.md", "Linear arithmetic and exact optimization modeling"),
    "domain.cp": ("cp.md", "Finite constraint, table, scheduling and connectivity patterns"),
    "domain.fol": ("fol.md", "Open-world first-order logic and proof obligations"),
    "macros": ("macro-library.md", "HIR preprocessing macros and exact expansions"),
    "dialect.z3": ("omt-dialects.md", "Z3 optimization syntax and current route limitations"),
    "dialect.optimathsat": ("omt-dialects.md", "OptiMathSAT syntax and current route limitations"),
    "dialect.smtlib-pure": ("omt-dialects.md", "Pure SMT-LIB excludes optimization, without degrading it"),
    "template": ("fixed-template.md", "Stable command ordering and result-independent queries"),
    "repair": ("repair.md", "Compiler feedback repair without gold answers"),
    "protocol.candidates": ("provider-candidates.md", "Provider JSON envelopes and exact source anchors"),
    "protocol.output": ("output-contract.md", "Machine-readable translated output contract"),
    "routes": ("routes.md", "HIR, direct SMT-LIB and shared-interface hybrid routes"),
    "logic": ("intent-and-logic.md", "Intent, validity polarity and SMT logic selection"),
}
DESCRIPTIONS = {
    "core": "Complete candidate envelope; source links; variables, literals, equality and ite",
    "bool": "Boolean connectives, equality and distinctness",
    "arithmetic": "Exact integer/real arithmetic, comparisons and explicit division conventions",
    "arrays": "Total arrays, finite shapes, access, update and immutable data lookup",
    "folds": "Finite half-open sum/forall/exists folds",
    "uf": "Uninterpreted sorts and declared or defined function applications",
    "quantifiers": "First-order forall/exists/exists_unique with explicit binders",
    "bitvectors": "Fixed-width modular arithmetic and signed/unsigned operators",
    "floating-point": "IEEE floating point with explicit format and rounding mode",
    "strings": "String operations with integer indices",
    "regex": "Regular-language constructors and string membership",
    "sets": "Finite-set constructors and backend limitations",
    "tuples": "Product values, selectors, updates and projection",
    "datatypes": "Datatype declarations, construction, selectors and testers",
    "omt": "Exact objectives, soft preferences and exposed priority semantics",
}
MARKERS = {
    "core": {"var", "literal", "op"}, "arrays": {"at", "const_array", "data"},
    "folds": {"fold"}, "uf": {"apply"}, "quantifiers": {"quantifier"},
    "floating-point": {"rm"}, "tuples": {"tuple", "tuple_unit"},
    "datatypes": {"dt_constructor", "dt_selector", "dt_tester"},
}
CONSTRUCTORS = {
    "core": {"variable", "literal", "operator"},
    "arrays": {"array_access", "constant_array", "data_lookup"},
    "folds": {"finite_fold"}, "uf": {"application", "function"},
    "quantifiers": {"quantifier"}, "floating-point": {"rounding_mode", "indexed_operator"},
    "tuples": {"tuple", "tuple_unit", "indexed_operator"},
    "datatypes": {"datatype_constructor", "datatype_selector", "datatype_tester", "datatype_declaration"},
    "bitvectors": {"indexed_operator"}, "regex": {"indexed_operator"},
    "arithmetic": {"indexed_operator"},
}
SEMANTICS = {
    "core": {"identifiers", "term_namespace", "scope"},
    "arithmetic": {"arithmetic", "absolute_value", "division", "count"},
    "arrays": {"arrays", "shape", "data"}, "folds": {"folds"},
    "quantifiers": {"quantifiers"}, "bitvectors": {"bitvectors"},
    "floating-point": {"floating_point"}, "strings": {"strings"},
    "regex": {"regular_expressions"}, "sets": {"sets"}, "tuples": {"tuples"},
}
SORT_KEYS = {
    "arrays": {"Array"}, "uf": {"Uninterpreted"}, "bitvectors": {"BitVec"},
    "floating-point": {"FloatingPoint"}, "sets": {"Set"}, "tuples": {"Tuple"},
    "datatypes": {"Datatype", "Parameter"},
}
# Short syntax reminders are not a second JSON model schema. Native semantic
# explanations and actual HIR constructor shapes below come from the live API.
SMT_SYNTAX = {
    "core": "(declare-const x Int), (assert (= x 1)), (ite p a b). Return the formal JSON envelope, not HIR objects.",
    "bool": "Bool terms: true, false, (not p), (and p q), (or p q), (=> p q), (= p q), (distinct x y).",
    "arithmetic": "Int/Real terms: (+ x y), (- x y), (* x y), (/ x y) for Real, (div x y)/(mod x y) for Int; preserve the source's division convention.",
    "arrays": "(Array IndexSort ValueSort), (select a i), (store a i v), ((as const (Array Int Int)) 0). Bounds are separate source constraints.",
    "folds": "No SMT-LIB 'fold' keyword: instantiate exactly the finite source range, or use an equivalent bounded quantified encoding.",
    "uf": "(declare-sort Person 0), (declare-fun f (Person) Int), (define-fun f ((x Int)) Int body), (f a).",
    "quantifiers": "(forall ((x Sort)) body), (exists ((x Sort)) body). SMT-LIB has no exists_unique primitive.",
    "bitvectors": "(_ BitVec 32), #x00000001, (bvadd x y), (bvult x y), (bvslt x y), ((_ extract 7 0) x).",
    "floating-point": "(_ FloatingPoint 8 24), RNE, (fp.add RNE x y), (fp.eq x y). IEEE equality differs from (= x y).",
    "strings": 'String, "text", (str.len s), (str.contains s "a"), (str.++ a b).',
    "regex": '(str.in_re s (re.* (str.to_re "a"))); RegLan terms are not strings.',
    "sets": "Finite-set syntax and solver extensions are backend-specific; consult the native semantic limitations, not Z3's array-set API by analogy.",
    "tuples": "Product encodings require a declared datatype or supported native product syntax; HIR tuple constructors are not SMT-LIB functions.",
    "datatypes": "(declare-datatype T ((ctor (field Int)))) declares a constructor/selector; names and sort arities must agree.",
    "omt": "(minimize e), (maximize e), (assert-soft p :weight 2 :id preference). Priority support depends on the exposed route and dialect.",
}


def canonical(value):
    return json.dumps(value, sort_keys=True, ensure_ascii=False, separators=(",", ":"), allow_nan=False)


def digest(value):
    return hashlib.sha256(canonical(value).encode("utf-8")).hexdigest()


def _candidate_example(route):
    """Small mandatory wire-contract example, independent of task/domain lookup."""
    source = "The integer u equals 2."
    span = {"quote": source}
    hir = dict(schema="somt-hir-model-v1", language="hir", decision="satisfiability",
        declarations=[{"name": "u", "sort": "Int"}], functions=[],
        constraints=[{"expr": {"op": "eq", "args": [{"var": "u"}, {"literal": 2, "sort": "Int"}]},
                      "span": span}],
        objectives=[], objective_order="single", goal=None, assumptions=[], unresolved=[])
    if route == "hir":
        candidate = hir
    elif route == "hybrid":
        hir["constraints"] = []
        candidate = {"schema": "somt-nl-hybrid-v1", "hir": hir,
                     "smt_constraints": [{"span": span, "term": "(= u 2)"}]}
    else:
        candidate = dict(schema="somt-nl-formal-v1", language="smtlib2", decision="satisfiability",
            program="(declare-const u Int)\n(assert (= u 2))\n(check-sat)", assumptions=[], unresolved=[],
            links=[{"span": span, "fragment": "(assert (= u 2))"}])
    return {"source": source, "candidate": candidate,
            "purpose": "Wire-format illustration only. Translate the actual source/context; do not copy this example's facts."}


def _hir_schema(native_request):
    schema = native_request.get("schema", {}) if native_request else {}
    if schema.get("properties", {}).get("schema", {}).get("const") == "somt-hir-model-v1":
        return schema
    nested = schema.get("properties", {}).get("hir")
    if isinstance(nested, dict):
        # Hybrid references resolve at its document root; do not relocate them
        # in the generated request. This temporary view is just for inspection.
        view = deepcopy(nested)
        if "$defs" not in view and "$defs" in schema:
            view["$defs"] = deepcopy(schema["$defs"])
        return view
    return None


def _catalog_schema(native_request):
    schema = _hir_schema(native_request)
    if schema is None or "constructor_api" not in schema:
        from somtparser.hir import hir_schema
        live = hir_schema()
        if schema is None:
            schema = live
        else:
            schema = deepcopy(schema)
            schema["constructor_api"] = live["constructor_api"]
    return schema


def _cp_names(api):
    return set(api.get("cp_constructors", {}).get("constructors", {}))


def capability_index(route, native_request=None):
    """List retrievable API and documentation IDs, without source selection.

    Passing a request uses its live catalog where present. Otherwise the local
    native API is inspected lazily, with no LLM, network or solver invocation.
    """
    if route not in ROUTES:
        raise ValueError("unknown route: " + str(route))
    api = _catalog_schema(native_request)["constructor_api"]
    entries = [{"id": key, "kind": "api", "description": value}
               for key, value in DESCRIPTIONS.items()]
    entries += [{"id": "cp." + name, "kind": "api",
                 "description": "Native CP constructor " + name + ("; direct SMT requires its encoding" if route == "smtlib2" else "")}
                for name in sorted(_cp_names(api))]
    entries += [{"id": key, "kind": "document", "description": value[1]}
                for key, value in DOCUMENTS.items()]
    return entries


def _operations(api, selected):
    names = set(api.get("operations", {}))
    wanted = {"eq", "ne", "ite"}
    if "bool" in selected:
        wanted |= {"not", "implies", "xor", "and", "or", "distinct"}
    if "arithmetic" in selected:
        wanted |= {"le", "lt", "ge", "gt", "add", "sub", "mul", "abs", "count"}
        wanted |= {name for name in names if name.startswith(("div", "mod"))}
    if "arrays" in selected:
        wanted |= {"select", "store"}
    for capability, prefixes in (("bitvectors", ("bv",)), ("floating-point", ("fp.",)),
                                 ("strings", ("str.",)), ("regex", ("re.",)), ("sets", ("set.",))):
        if capability in selected:
            wanted |= {name for name in names if name.startswith(prefixes)}
    if "bitvectors" in selected:
        wanted.add("concat")
    if "strings" in selected and "regex" not in selected:
        wanted -= {"str.to_re", "str.in_re"}
    if "regex" in selected:
        wanted |= {"str.to_re", "str.in_re"}
    wanted |= {item[3:] for item in selected if item.startswith("cp.")}
    return names & wanted


def _indexed(api, selected):
    wanted = set()
    if "bitvectors" in selected:
        wanted |= {"extract", "zero_extend", "sign_extend", "rotate_left", "rotate_right", "repeat", "int2bv"}
    if "arithmetic" in selected:
        wanted.add("divisible")
    if "floating-point" in selected:
        wanted |= {"fp.to_sbv", "fp.to_ubv", "to_fp", "to_fp_unsigned", "ieee_bv_to_fp"}
    if "regex" in selected:
        wanted.add("re.loop")
    if "tuples" in selected:
        wanted |= {name for name in api.get("indexed_operations", {}) if name.startswith("tuple.")}
    return wanted & set(api.get("indexed_operations", {}))


def _narrow_enum_schema(schema, field, names):
    result = deepcopy(schema)
    result["properties"][field]["enum"] = [name for name in result["properties"][field]["enum"] if name in names]
    if "allOf" in result:
        keep = []
        for check in result["allOf"]:
            condition = check.get("if", {}).get("properties", {}).get(field, {})
            if "enum" in condition:
                condition["enum"] = [value for value in condition["enum"] if value in names]
                if not condition["enum"]:
                    continue
            keep.append(check)
        result["allOf"] = keep
    return result


def _expression_view(expression, api, selected):
    allowed_markers = set().union(*(MARKERS.get(key, set()) for key in selected))
    cp_names = {key[3:] for key in selected if key.startswith("cp.")}
    operators = _operations(api, selected)
    aliases = {key for key, target in api.get("operator_aliases", {}).items() if target in operators}
    indexed = _indexed(api, selected)
    variants = []
    for check in expression.get("allOf", []):
        required = check.get("if", {}).get("required", [])
        if not required:
            continue
        marker, branch = required[0], deepcopy(check["then"])
        if marker == "op":
            ordinary, globals_ = branch["oneOf"]
            variants.append(_narrow_enum_schema(ordinary, "op", operators | aliases))
            for item in globals_.get("oneOf", []):
                if item.get("properties", {}).get("op", {}).get("const") in cp_names:
                    variants.append(item)
        elif marker == "op_indexed" and indexed:
            branch["properties"]["op_indexed"] = _narrow_enum_schema(branch["properties"]["op_indexed"], "op", indexed)
            checks = []
            for item in branch.get("allOf", []):
                values = item["if"]["properties"]["op_indexed"]["properties"]["op"]["enum"]
                item["if"]["properties"]["op_indexed"]["properties"]["op"]["enum"] = [value for value in values if value in indexed]
                if item["if"]["properties"]["op_indexed"]["properties"]["op"]["enum"]:
                    checks.append(item)
            branch["allOf"] = checks
            variants.append(branch)
        elif marker == "cp" and cp_names:
            cp_string = branch["oneOf"][0]
            # Use the live exact constructor branch itself. This avoids the
            # full union of every CP constructor's fields and descriptions.
            for item in cp_string.get("allOf", []):
                if item["if"]["properties"]["cp"]["const"] in cp_names:
                    variants.append(item["then"])
            if "abs" in cp_names:
                variants.append(branch["oneOf"][1])
        elif marker in allowed_markers:
            variants.append(branch)
    if not variants:
        raise ValueError("live HIR expression schema has no recognized constructor branches")
    return {"anyOf": variants}


def _sort_view(sort_schema, selected):
    scalar = {"Bool", "Int", "Real"}
    if "strings" in selected or "regex" in selected:
        scalar.add("String")
    if "regex" in selected:
        scalar.add("RegLan")
    keys = set().union(*(SORT_KEYS.get(key, set()) for key in selected))
    variants = []
    for branch in sort_schema.get("anyOf", []):
        if "enum" in branch:
            item = deepcopy(branch)
            item["enum"] = [value for value in item["enum"] if value in scalar]
            if item["enum"]:
                variants.append(item)
        elif set(branch.get("properties", {})) & keys:
            variants.append(deepcopy(branch))
    return {"anyOf": variants}


def _used_definitions(schema):
    definitions = schema.get("$defs", {})
    used = set()

    def walk(value):
        if isinstance(value, list):
            for item in value:
                walk(item)
        elif isinstance(value, dict):
            reference = value.get("$ref", "")
            if isinstance(reference, str) and reference.startswith("#/$defs/"):
                name = reference.split("/")[2].replace("~1", "/").replace("~0", "~")
                if name not in used:
                    used.add(name)
                    walk(definitions[name])
            for key, child in value.items():
                if key != "$defs":
                    walk(child)

    walk(schema)
    return {key: value for key, value in definitions.items() if key in used}


def _schema_view(route, native_schema, api, selected):
    result = deepcopy(native_schema)
    if route == "smtlib2":
        return result
    hir = result["properties"]["hir"] if route == "hybrid" else result
    hir.pop("constructor_api", None)
    definitions = result["$defs"]
    definitions["expression"] = _expression_view(definitions["expression"], api, selected)
    definitions["sort"] = _sort_view(definitions["sort"], selected)
    result["$defs"] = _used_definitions(result)
    return result


def _api_fragment(api, selected):
    names = set().union(*(CONSTRUCTORS.get(key, set()) for key in selected))
    semantics = set().union(*(SEMANTICS.get(key, set()) for key in selected))
    operators, indexed = _operations(api, selected), _indexed(api, selected)
    fragment = {
        "constructors": {key: deepcopy(value) for key, value in api.get("constructors", {}).items() if key in names},
        "operations": {key: deepcopy(value) for key, value in api.get("operations", {}).items() if key in operators},
        "operator_aliases": {key: value for key, value in api.get("operator_aliases", {}).items() if value in operators},
        "indexed_operations": {key: deepcopy(value) for key, value in api.get("indexed_operations", {}).items() if key in indexed},
        "semantics": {key: value for key, value in api.get("semantics", {}).items() if key in semantics},
    }
    cp_names = {key[3:] for key in selected if key.startswith("cp.")}
    if cp_names:
        cp = api["cp_constructors"]
        cp_semantics = {"budgets"}
        if cp_names & {"no_overlap", "cumulative"}:
            cp_semantics.add("time")
        if cp_names & {"among", "count_true", "at_most_one", "global_cardinality"}:
            cp_semantics.add("finite_globals")
        if cp_names & {"circuit", "regular"}:
            cp_semantics.add("witnesses")
        cp_semantics |= cp_names
        fragment["cp_constructors"] = {
            "vector": cp["vector"],
            "constructors": {key: deepcopy(value) for key, value in cp["constructors"].items() if key in cp_names},
            "semantics": {key: value for key, value in cp.get("semantics", {}).items() if key in cp_semantics},
        }
        fragment["semantics"].update({key: value for key, value in api.get("semantics", {}).items() if key in cp_names})
    if "omt" in selected:
        fragment["soft_constraints"] = deepcopy(api.get("soft_constraints", {}))
    return fragment


def materialize_capabilities(route, ids, native_request):
    """Return a hashed packet with the selected API view and document resources.

    ``core`` is the only implicit capability. For a later lookup pass the union
    of previous and newly requested IDs; no input list or request is modified.
    A view omission means "not loaded", never "unsupported by the compiler".
    """
    if route not in ROUTES:
        raise ValueError("unknown route: " + str(route))
    if not isinstance(ids, (list, tuple)) or any(not isinstance(value, str) for value in ids):
        raise TypeError("capability IDs must be a list of strings")
    if not isinstance(native_request, dict) or not isinstance(native_request.get("schema"), dict):
        raise TypeError("native_request must contain its live schema")
    if native_request.get("language", route) != route:
        raise ValueError("request language does not match route")
    catalog_schema = _catalog_schema(native_request)
    api = catalog_schema["constructor_api"]
    index = capability_index(route, native_request)
    known = {item["id"] for item in index}
    unknown = sorted(set(ids) - known)
    if unknown:
        raise ValueError("unknown capability IDs: " + ", ".join(unknown))
    selected = set(ids) | {"core"}
    request = deepcopy(native_request)
    original_instructions = {key: digest(request.pop(key)) for key in ("instruction", "hir_instruction") if key in request}
    request.pop("macro_extension", None)
    request["request_profile"] = "capability-view"
    request["schema"] = _schema_view(route, native_request["schema"], api, selected)
    request["candidate_contract_example"] = _candidate_example(route)
    request["instruction"] = (
        "Return one complete candidate in this route's JSON envelope, including every required root field. "
        "Use the unchanged source and caller context. Preserve every constraint, domain, unit and objective; "
        "do not add bounds or infer missing facts. Variables use {var:name} in HIR, never op:var. "
        'Source spans use exact {"quote":"unchanged source substring"} anchors, not guessed character offsets. '
        "Genuine unresolved alternatives prevent compilation. "
        "Unknown decision values or multiple feasible solutions are not unresolved interpretation. "
        "This schema is the loaded capability view, not the complete native language. If construction requires "
        "another capability, request its documented ID; do not weaken the source to fit this view. "
        "Native compilation remains authoritative. Translation does not execute a solver or prove NL correctness."
    )
    if route != "smtlib2":
        request["instruction"] += (' HIR Real literals and Real declaration lower/upper bounds use exact '
                                   'decimal/rational strings, including "0" and "1"; Int values use JSON integers. '
                                   'Expression nodes are objects, never infix strings. {"var":"u"} has no sort field; '
                                   '{"literal":2,"sort":"Int"} requires its sort. Empty required fields still appear.')
        request["loaded_constructor_api"] = _api_fragment(api, selected)
    else:
        request["instruction"] += (' Each links[].fragment must be an exact substring of your final SMT program, '
                                   'such as "(assert (= u 2))", never a natural-language sentence. '
                                   'The source quotation belongs only in links[].span.quote.')
        request["loaded_smt_syntax"] = {key: SMT_SYNTAX[key] for key in sorted(selected) if key in SMT_SYNTAX}
        if any(key.startswith("cp.") for key in selected):
            request["cp_semantic_reference"] = _api_fragment(api, selected).get("cp_constructors", {})
            request["cp_reference_boundary"] = "CP JSON constructors are HIR APIs, not SMT-LIB primitives. Encode their source-required relation using declared SMT terms."
    resources = []
    for identifier in sorted(selected & DOCUMENTS.keys()):
        filename, _ = DOCUMENTS[identifier]
        path = RESOURCE_ROOT / filename
        content = path.read_text(encoding="utf-8")
        resources.append({"id": identifier, "path": "references/" + filename,
                          "sha256": hashlib.sha256(content.encode("utf-8")).hexdigest(), "text": content})
    request["loaded_resources"] = resources
    request["capability_view"] = {"loaded": sorted(selected), "native_support_unchanged": True,
                                  "selection_must_not_use_reference_answers": True}
    packet = {
        "schema": "somt-capability-packet-v1", "route": route, "loaded": sorted(selected), "request": request,
        "native_schema_sha256": digest(native_request["schema"]), "catalog_sha256": digest(index),
        "original_instruction_sha256": original_instructions,
        "boundaries": [
            "Loaded-view schema describes advertised constructors; native compiler still accepts its complete language.",
            "Core retains all candidate envelope properties and required fields; optional theory operators and sorts are retrieved separately.",
            "Documents are retrieved by stable whole-file IDs; dialect IDs currently share a comparison document.",
            "Macro documentation describes preprocessing notation; this schema describes the expanded native HIR.",
            "The capability groups reflect the current live API. Newly introduced native constructor families require catalog grouping before they are advertised.",
        ],
    }
    packet["packet_sha256"] = digest(packet)
    return packet


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    for name in ("index", "read"):
        command = commands.add_parser(name)
        command.add_argument("--route", choices=ROUTES, required=True)
        command.add_argument("--request", type=Path, required=True,
                             help="captured native request JSON; source/context are retained")
        if name == "read":
            command.add_argument("--ids", nargs="+", required=True)
    args = parser.parse_args(argv)
    from smt_bridge import read_json
    try:
        request = read_json(args.request)
        result = (capability_index(args.route, request) if args.command == "index"
                  else materialize_capabilities(args.route, args.ids, request))
        print(json.dumps(result, ensure_ascii=False, indent=2, allow_nan=False))
        return 0
    except (OSError, ValueError, TypeError, KeyError) as error:
        print(json.dumps({"status": "capability-error", "error": str(error)}, ensure_ascii=False), file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
