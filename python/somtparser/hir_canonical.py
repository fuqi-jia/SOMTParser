"""Audited, exact syntactic normalization for typed HIR candidate JSON.

Only spellings with an explicit sort/operator meaning are normalized. Missing
bounds, indices, variables, parentheses or constraints are never inferred.
Every change is returned in a ledger; callers must select the resulting digest.
"""
from copy import deepcopy
import re
from .hir_provider_forms import adapt_provider_forms


def canonicalize_hir(model):
    result, changes = adapt_provider_forms(model)

    def change(obj, key, value, path, rule):
        changes.append(
            dict(
                path=path + "/" + key,
                rule=rule,
                before=deepcopy(obj[key]),
                after=deepcopy(value),
            )
        )
        obj[key] = value

    # An empty provider container carries no named data entries. Normalize
    # only this top-level empty list; nonempty lists have no unambiguous
    # name-to-table interpretation, and nested table arrays remain data.
    if (result.get("schema") == "somt-hir-model-v1"
            and result.get("language") == "hir"
            and isinstance(result.get("data"), list) and not result["data"]):
        change(result, "data", {}, "", "empty-data-array-to-object")

    def integer(obj, key, path):
        value = obj.get(key)
        if (
            isinstance(value, str)
            and len(value) <= 512
            and re.fullmatch(r"[+-]?[0-9]+", value)
        ):
            change(obj, key, int(value), path, "exact-Int-decimal-spelling")

    def numeric_sort(obj, key, path):
        value = obj.get(key)
        if (
            isinstance(value, dict)
            and set(value) == {"sort"}
            and isinstance(value["sort"], str)
            and value["sort"] in {"Int", "Real"}
        ):
            change(obj, key, value["sort"], path, "singleton-numeric-sort-wrapper")

    def canonical_sort(value, path):
        """Normalize exact sort wrappers throughout nested datatype/sort syntax."""
        if (
            isinstance(value, dict)
            and set(value) == {"sort"}
            and isinstance(value["sort"], str)
            and value["sort"] in {"Int", "Real"}
        ):
            normalized = value["sort"]
            changes.append(
                dict(path=path, rule="singleton-numeric-sort-wrapper",
                     before=deepcopy(value), after=normalized)
            )
            return normalized
        if isinstance(value, str) and value.startswith("Uninterpreted:"):
            identifier = value[len("Uninterpreted:"):]
            if (
                identifier.isidentifier()
                and len(identifier) <= 128
                and identifier.lower()
                not in {"true", "false", "tdiv", "ite", "and", "or", "not"}
            ):
                normalized = {"Uninterpreted": identifier}
                changes.append(
                    dict(path=path, rule="explicit-uninterpreted-sort-alias",
                         before=deepcopy(value), after=deepcopy(normalized))
                )
                return normalized
            return value
        if not isinstance(value, dict):
            return value
        if (set(value) == {"Array"} and isinstance(value["Array"], list)
                and len(value["Array"]) == 2):
            value["Array"] = [
                canonical_sort(item, f"{path}/Array/{i}")
                for i, item in enumerate(value["Array"])
            ]
        elif set(value) == {"Set"}:
            value["Set"] = canonical_sort(value["Set"], f"{path}/Set")
        elif set(value) == {"Tuple"} and isinstance(value["Tuple"], list):
            value["Tuple"] = [
                canonical_sort(item, f"{path}/Tuple/{i}")
                for i, item in enumerate(value["Tuple"])
            ]
        elif set(value) == {"Datatype"}:
            spec = value["Datatype"]
            if isinstance(spec, dict) and isinstance(spec.get("args"), list):
                spec["args"] = [
                    canonical_sort(item, f"{path}/Datatype/args/{i}")
                    for i, item in enumerate(spec["args"])
                ]
        return value

    def typed_sort(obj, key, path):
        if key in obj:
            obj[key] = canonical_sort(obj[key], f"{path}/{key}")

    datatypes = result.get("datatypes", [])
    if isinstance(datatypes, list):
        for i, datatype in enumerate(datatypes):
            if not isinstance(datatype, dict):
                continue
            constructors = datatype.get("constructors", [])
            if isinstance(constructors, list):
                for j, constructor in enumerate(constructors):
                    if not isinstance(constructor, dict):
                        continue
                    fields = constructor.get("fields", [])
                    if isinstance(fields, list):
                        for k, field in enumerate(fields):
                            if isinstance(field, dict):
                                typed_sort(field, "sort", f"/datatypes/{i}/constructors/{j}/fields/{k}")

    declarations = result.get("declarations", [])
    if not isinstance(declarations, list):
        declarations = []
    for i, declaration in enumerate(declarations):
        if isinstance(declaration, dict):
            numeric_sort(declaration, "sort", f"/declarations/{i}")
            typed_sort(declaration, "sort", f"/declarations/{i}")
            if declaration.get("sort") == "Int":
                for key in ["lower", "upper"]:
                    if key in declaration:
                        integer(declaration, key, f"/declarations/{i}")

    functions = result.get("functions", [])
    if not isinstance(functions, list):
        functions = []
    for i, function in enumerate(functions):
        if not isinstance(function, dict):
            continue
        if isinstance(function.get("arguments"), list):
            for j, argument in enumerate(function["arguments"]):
                if isinstance(argument, dict) and set(argument) == {"sort"}:
                    # Argument entries are themselves sort values in this schema.
                    value = argument["sort"]
                    if isinstance(value, str) and value in {"Int", "Real"}:
                        function["arguments"][j] = value
                        changes.append(
                            dict(
                                path=f"/functions/{i}/arguments/{j}",
                                rule="singleton-numeric-sort-wrapper",
                                before=deepcopy(argument),
                                after=value,
                            )
                        )
                function["arguments"][j] = canonical_sort(
                    function["arguments"][j],
                    f"/functions/{i}/arguments/{j}",
                )
        numeric_sort(function, "result", f"/functions/{i}")
        typed_sort(function, "result", f"/functions/{i}")
        binders = function.get("binders", [])
        if isinstance(binders, list):
            for j, binder in enumerate(binders):
                if isinstance(binder, dict):
                    numeric_sort(binder, "sort", f"/functions/{i}/binders/{j}")
                    typed_sort(binder, "sort", f"/functions/{i}/binders/{j}")

    def expression(e, path):
        if not isinstance(e, dict):
            return
        if "literal" in e and "sort" in e:
            numeric_sort(e, "sort", path)
        if set(e) in ({"dt_constructor", "sort", "args"},
                      {"dt_selector", "sort", "value"}):
            typed_sort(e, "sort", path)
        if set(e) == {"literal", "sort"}:
            typed_sort(e, "sort", path)
        if set(e) == {"literal", "sort"} and e["sort"] == "Int":
            integer(e, "literal", path)
        if (set(e) == {"literal", "sort"} and e["sort"] == "Bool"
                and isinstance(e["literal"], str) and e["literal"] in ("true", "false")):
            change(e, "literal", e["literal"] == "true", path, "exact-Bool-literal-spelling")
        if isinstance(e.get("binders"), list):
            for i, binder in enumerate(e["binders"]):
                if isinstance(binder, dict) and set(binder) == {"name", "sort"}:
                    numeric_sort(binder, "sort", f"{path}/binders/{i}")
                    typed_sort(binder, "sort", f"{path}/binders/{i}")
        if set(e) == {"op", "binders", "body"} and e["op"] in ["forall", "exists", "exists_unique"]:
            previous = deepcopy(e)
            e["quantifier"] = e.pop("op")
            changes.append(
                dict(
                    path=path,
                    rule="explicit-quantifier-tag",
                    before=previous,
                    after=deepcopy(e),
                )
            )
        if set(e) == {"op", "args"} and isinstance(e["args"], list):
            aliases = {"sum": "add", "allDifferent": "all_different"}
            if e["op"] in aliases:
                change(e, "op", aliases[e["op"]], path, "operator-spelling")
            if e["op"] in ["min", "max", "minimum", "maximum"]:
                previous = deepcopy(e)
                kind = "minimum" if e["op"] in ["min", "minimum"] else "maximum"
                items = e["args"]
                e.clear()
                e.update(cp=kind, items=items)
                changes.append(
                    dict(
                        path=path,
                        rule="aggregate-constructor-tag",
                        before=previous,
                        after=deepcopy(e),
                    )
                )
        for key in [
            "args",
            "indices",
            "items",
            "weights",
            "left",
            "right",
            "starts",
            "successors",
            "counts",
        ]:
            if isinstance(e.get(key), list):
                for i, v in enumerate(e[key]):
                    expression(v, f"{path}/{key}/{i}")
            elif isinstance(e.get(key), dict):
                vector = e[key]
                if (set(vector) == {"array", "length", "prefix"}
                        and isinstance(vector["prefix"], list)):
                    for i, value in enumerate(vector["prefix"]):
                        # These positions are explicitly array indices. A JSON
                        # integer names an exact Int constant; bool, float and
                        # strings are left to the ordinary shape/type checker.
                        if type(value) is int:
                            normalized = {"literal": value, "sort": "Int"}
                            changes.append(dict(
                                path=f"{path}/{key}/prefix/{i}",
                                rule="explicit-CP-prefix-integer",
                                before=value, after=deepcopy(normalized),
                            ))
                            vector["prefix"][i] = value = normalized
                        expression(value, f"{path}/{key}/prefix/{i}")
        for key in ["body", "default", "value", "index", "capacity"]:
            if key in e:
                expression(e[key], path + "/" + key)
        if isinstance(e.get("op_indexed"), dict):
            arguments = e["op_indexed"].get("args")
            if isinstance(arguments, list):
                for i, argument in enumerate(arguments):
                    expression(argument, f"{path}/op_indexed/args/{i}")
        if (
            e.get("op") == "add"
            and isinstance(e.get("args"), list)
            and all(
                isinstance(v, dict)
                and set(v) == {"literal", "sort"}
                and v["sort"] == "Int"
                and type(v["literal"]) is int
                for v in e["args"]
            )
        ):
            previous = deepcopy(e)
            value = sum(v["literal"] for v in e["args"])
            e.clear()
            e.update(literal=value, sort="Int")
            changes.append(
                dict(
                    path=path,
                    rule="exact-constant-sum",
                    before=previous,
                    after=deepcopy(e),
                )
            )

    for i, function in enumerate(functions):
        if isinstance(function, dict) and "body" in function:
            expression(function["body"], f"/functions/{i}/body")

    for section in ["constraints", "soft_constraints", "objectives"]:
        entries = result.get(section, [])
        if not isinstance(entries, list):
            entries = []
        for i, entry in enumerate(entries):
            if (section == "objectives" and isinstance(entry, dict)
                    and set(entry) == {"sense", "expr", "span"}
                    and isinstance(entry["sense"], str)
                    and entry["sense"] in {"min", "max"}):
                # These spellings express the same optimization direction.
                # Record the change before candidate selection; archived
                # candidates remain immutable when loaded or compiled.
                direction = {"min": "minimize", "max": "maximize"}[entry["sense"]]
                change(entry, "sense", direction, f"/{section}/{i}",
                       "explicit-objective-sense-alias")
            if isinstance(entry, dict) and "expr" in entry:
                expression(entry["expr"], f"/{section}/{i}/expr")
    if isinstance(result.get("goal"), dict) and "expr" in result["goal"]:
        expression(result["goal"]["expr"], "/goal/expr")
    # Some HIR models encode goal directly as an expression.
    elif isinstance(result.get("goal"), dict):
        expression(result["goal"], "/goal")
    return result, changes
