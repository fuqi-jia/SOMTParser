"""Source-anchor protocol and optional shape diagnostics, without solver calls.

Only named source-link positions are rewritten. This is intentionally not a
recursive model normalizer: literal data can contain ``span`` or ``quote``.
"""
from copy import deepcopy
import heapq
import re


ROUTES = ("hir", "smtlib2", "hybrid")
HIR_LINK_ARRAYS = ("constraints", "soft_constraints", "objectives", "functions")
ANCHOR_SCHEMA = {
    "type": "object",
    "required": ["quote"],
    "properties": {
        "quote": {"type": "string", "minLength": 1},
        "occurrence": {"type": "integer", "minimum": 0},
    },
    "additionalProperties": False,
    "description": (
        "Exact, nonempty source quotation. If it occurs more than once, choose "
        "the zero-based occurrence explicitly. Indices count Unicode code points."
    ),
}


def json_pointer(parts):
    return "".join("/" + str(part).replace("~", "~0").replace("/", "~1")
                   for part in parts)


class SourceAnchorError(ValueError):
    """An exact quotation cannot be resolved without changing or guessing it."""

    def __init__(self, pointer, message):
        self.pointer = pointer
        super().__init__(pointer + ": " + message)


def _entries(model, route):
    """Yield mutable source-expression objects with their JSON paths."""
    if not isinstance(model, dict):
        return
    if route == "hybrid":
        for entry, path in _entries(model.get("hir"), "hir"):
            yield entry, ("hir", *path)
        fields = ("smt_constraints",)
    elif route == "smtlib2":
        fields = ("links",)
    else:
        fields = HIR_LINK_ARRAYS
        goal = model.get("goal")
        if isinstance(goal, dict):
            yield goal, ("goal",)
    for field in fields:
        values = model.get(field)
        if isinstance(values, list):
            for index, entry in enumerate(values):
                if isinstance(entry, dict):
                    yield entry, (field, index)


def resolve_source_spans(model, source, route):
    """Return ``(deep_copy, ledger)`` with exact quote anchors made numeric.

    Numeric spans and malformed non-object spans remain untouched for native
    validation. A dictionary at an allowed ``span`` position must be exactly
    ``{"quote": text, "occurrence": optional_zero_based_integer}``.
    Matching is literal, includes overlapping occurrences, and does not apply
    Unicode normalization. No declaration, expression, or literal data is edited.
    """
    if route not in ROUTES:
        raise ValueError("unknown route: " + str(route))
    if not isinstance(source, str):
        raise TypeError("source must be text")
    result, ledger = deepcopy(model), []
    for entry, path in _entries(result, route):
        anchor = entry.get("span")
        if not isinstance(anchor, dict):
            continue
        pointer = json_pointer((*path, "span"))
        if "quote" not in anchor or set(anchor) - {"quote", "occurrence"}:
            raise SourceAnchorError(pointer, "expected quote and optional occurrence only")
        quote = anchor["quote"]
        if not isinstance(quote, str) or not quote:
            raise SourceAnchorError(pointer, "quote must be nonempty source text")
        occurrence = anchor.get("occurrence")
        if "occurrence" in anchor and (type(occurrence) is not int or occurrence < 0):
            raise SourceAnchorError(pointer, "occurrence must be a nonnegative integer")
        # Find only enough matches to choose the requested occurrence or detect
        # ambiguity. Do not allocate an offset for every character of a source.
        start, selected, matches = 0, None, 0
        target = 1 if occurrence is None else occurrence
        while matches <= target:
            index = source.find(quote, start)
            if index < 0:
                break
            if occurrence is not None and matches == occurrence:
                selected = index
            elif occurrence is None and matches == 0:
                selected = index
            matches += 1
            start = index + 1
        if not matches:
            raise SourceAnchorError(pointer, "quote does not occur exactly in source")
        if occurrence is None and matches > 1:
            raise SourceAnchorError(pointer, "quote repeats; specify its zero-based occurrence")
        if selected is None:
            raise SourceAnchorError(pointer, "occurrence is out of range")
        span = [selected, selected + len(quote)]
        entry["span"] = span
        ledger.append({"path": pointer, "rule": "exact-source-quote",
                       "before": deepcopy(anchor), "after": span.copy()})
    return result, ledger


def _local_ref(schema, reference):
    if not isinstance(reference, str) or not reference.startswith("#/"):
        raise ValueError("source-span schema references must be local JSON pointers")
    value = schema
    for part in reference[2:].split("/"):
        value = value[part.replace("~1", "/").replace("~0", "~")]
    return value


def _source_entry_schema(node, root, seen=()):
    """Alter one source-expression schema, never descend into its expr/data."""
    if not isinstance(node, dict):
        return deepcopy(node)
    result = deepcopy(node)
    reference = result.get("$ref")
    if reference is not None:
        if reference in seen:
            raise ValueError("recursive source-expression schema")
        target = _local_ref(root, reference)
        # Source-entry refs use document-root fragments. Keep the document root
        # and its $defs in place; inline only this entry's view, not its siblings.
        if not isinstance(target, dict) or "$id" in target:
            raise ValueError("scoped source-expression schema is not supported")
        resolved = _source_entry_schema(target, root, (*seen, reference))
        siblings = {key: value for key, value in result.items() if key != "$ref"}
        if siblings:
            return {"allOf": [resolved, _source_entry_schema(siblings, root, seen)]}
        return resolved
    properties = result.get("properties")
    if isinstance(properties, dict) and "span" in properties:
        original = properties["span"]
        # Do not alter the old numeric contract, including any $ref it carries.
        alternatives = original.get("anyOf") if isinstance(original, dict) else None
        if not (isinstance(alternatives, list) and alternatives and alternatives[-1] == ANCHOR_SCHEMA):
            properties["span"] = {"anyOf": [original, deepcopy(ANCHOR_SCHEMA)]}
    for keyword in ("allOf", "anyOf", "oneOf"):
        if isinstance(result.get(keyword), list):
            result[keyword] = [_source_entry_schema(child, root, seen)
                               for child in result[keyword]]
    for keyword in ("if", "then", "else", "not"):
        if keyword in result:
            result[keyword] = _source_entry_schema(result[keyword], root, seen)
    return result


def schema_with_source_anchors(schema, route):
    """Deep-copy a live request schema and extend permitted span properties.

    The caller passes the entire document, including the hybrid root $defs.
    Root definitions and all unrelated schemas remain unchanged. This helper
    does not permit declaration spans or new HIR expression constructors.
    """
    if route not in ROUTES:
        raise ValueError("unknown route: " + str(route))
    if not isinstance(schema, dict):
        raise TypeError("schema must be an object")
    result = deepcopy(schema)

    def extend(container, fields, goal=False):
        properties = container.get("properties", {})
        for field in fields:
            field_schema = properties.get(field, {})
            if isinstance(field_schema, dict) and "items" in field_schema:
                field_schema["items"] = _source_entry_schema(field_schema["items"], schema)
        if goal and "goal" in properties:
            properties["goal"] = _source_entry_schema(properties["goal"], schema)

    if route == "hir":
        extend(result, HIR_LINK_ARRAYS, goal=True)
    elif route == "smtlib2":
        extend(result, ("links",))
    else:
        hir = result.get("properties", {}).get("hir", {})
        extend(hir, HIR_LINK_ARRAYS, goal=True)
        extend(result, ("smt_constraints",))
    return result


def _diagnostic(error):
    path = list(error.absolute_path)
    validator = error.validator
    message = error.message
    if validator == "required":
        for field in error.validator_value:
            if field not in error.instance and message == repr(field) + " is a required property":
                path.append(field)
                message = "required field is missing"
                break
    elif validator in ("oneOf", "anyOf"):
        message = "value does not match the permitted schema alternatives"
        if isinstance(error.instance, dict) and error.instance.get("op") == "var":
            path.append("op")
            message = "'var' is not an operator; a variable reference has the form {\"var\": \"declared_name\"}"
    elif validator == "type":
        message = "expected type " + str(error.validator_value)
    elif validator in ("enum", "const"):
        message = "value is not in the permitted " + validator + " contract"
    # jsonschema sometimes quotes a complete expression in messages. A failed
    # repair should receive the location and contract, not another full model.
    message = message if len(message) <= 320 else message[:317] + "..."
    return {"code": "SCHEMA_" + str(validator).upper(), "severity": "error",
            "pointer": json_pointer(path), "message": message,
            "schema_pointer": json_pointer(error.absolute_schema_path)}


def schema_diagnostics(model, schema, limit=16):
    """Return at most ``limit`` stable shape errors, without changing the model.

    jsonschema is an optional developer dependency. Its absence is an explicit
    warning, never a claim that the candidate passed. Semantic/type validation
    remains the native builder's responsibility. Union alternatives are reported
    once at their owning expression to avoid dozens of irrelevant branch errors.
    """
    if type(limit) is not int or limit < 1:
        raise ValueError("diagnostic limit must be a positive integer")
    try:
        import jsonschema
    except ImportError:
        return [{"code": "SCHEMA_VALIDATOR_UNAVAILABLE", "severity": "warning",
                 "pointer": "", "schema_pointer": "",
                 "message": "install jsonschema for optional shape diagnostics; native validation is still required"}]
    validator_class = jsonschema.validators.validator_for(schema)
    validator_class.check_schema(schema)
    validator = validator_class(schema)
    seen = set()
    count = 0

    def diagnostics():
        nonlocal count
        for error in validator.iter_errors(model):
            if error.validator == "additionalProperties" and error.validator_value is False and isinstance(error.instance, dict):
                patterns = list(error.schema.get("patternProperties", {}))
                extra = [key for key in error.instance if key not in error.schema.get("properties", {})
                         and not any(re.search(pattern, key) for pattern in patterns)]
                entries = []
                for field in sorted(extra):
                    entry = _diagnostic(error)
                    entry.update(pointer=json_pointer([*error.absolute_path, field]),
                                 message="field is not permitted by this schema")
                    entries.append(entry)
            else:
                entries = [_diagnostic(error)]
            for entry in entries:
                identity = (entry["pointer"], entry["code"], entry["message"])
                if identity not in seen:
                    seen.add(identity)
                    count += 1
                    yield entry

    entries = heapq.nsmallest(limit, diagnostics(),
                             key=lambda item: (item["pointer"], item["code"], item["message"]))
    if count > limit:
        entries[-1]["additional_diagnostics_omitted"] = count - limit
    return entries
