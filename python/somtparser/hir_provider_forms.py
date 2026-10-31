"""Audited adapter for explicit HIR constructor variants from providers.

This is separate from candidate construction and acceptance. Named constructors,
whitelisted operators, and exact JSON Int/Bool literals in expression slots are
normalized; names, bindings, and missing expression meaning are never guessed.
"""
from copy import deepcopy
from functools import lru_cache
import hashlib

from .hir import INDEXED_OPERATIONS, OPERATOR_ALIASES, OPERATIONS


# These spellings have the same operand order and relation as the named HIR
# operator. Division/remainder and unary '-' deliberately have no alias here:
# their conventions must be selected explicitly by the provider.
_SYMBOLIC_OPERATORS = {
    "=": "eq", "!=": "ne", "<=": "le", "<": "lt",
    ">=": "ge", ">": "gt", "+": "add", "-": "sub",
    "*": "mul", "=>": "implies",
}


def _arity_ok(operator, arguments):
    minimum, maximum = OPERATIONS[operator]
    return minimum <= len(arguments) <= maximum


@lru_cache(maxsize=1)
def _reserved_operator_names():
    # Function declarations cannot reinterpret any operator spelling already
    # owned by HIR or by the following canonicalizer/CP adapter.
    from .hir_cp import cp_api

    return frozenset(
        set(OPERATIONS)
        | set(OPERATOR_ALIASES)
        | set(INDEXED_OPERATIONS)
        | set(cp_api()["constructors"])
        | {"sum", "min", "max", "minimum", "maximum", "allDifferent"}
    )


def _declared_function_arities(model):
    """Index only unambiguous, explicitly shaped function signatures."""
    functions = model.get("functions")
    if not isinstance(functions, list):
        return {}

    function_name_counts = {}
    for function in functions:
        if isinstance(function, dict) and isinstance(function.get("name"), str):
            name = function["name"]
            function_name_counts[name] = function_name_counts.get(name, 0) + 1

    occupied_names = set()
    declarations = model.get("declarations")
    if isinstance(declarations, list):
        occupied_names.update(
            declaration["name"] for declaration in declarations
            if isinstance(declaration, dict) and isinstance(declaration.get("name"), str)
        )
    datatypes = model.get("datatypes")
    if isinstance(datatypes, list):
        for datatype in datatypes:
            if not isinstance(datatype, dict) or not isinstance(datatype.get("constructors"), list):
                continue
            for constructor in datatype["constructors"]:
                if not isinstance(constructor, dict):
                    continue
                if isinstance(constructor.get("name"), str):
                    occupied_names.add(constructor["name"])
                fields = constructor.get("fields")
                if isinstance(fields, list):
                    occupied_names.update(
                        field["name"] for field in fields
                        if isinstance(field, dict) and isinstance(field.get("name"), str)
                    )

    reserved = _reserved_operator_names()
    arities = {}
    declaration_keys = {"name", "arguments", "result"}
    definition_keys = declaration_keys | {"binders", "body", "span"}
    for function in functions:
        if not isinstance(function, dict):
            continue
        name = function.get("name")
        arguments = function.get("arguments")
        if (
            isinstance(name, str)
            and function_name_counts.get(name) == 1
            and name not in occupied_names
            and name not in reserved
            and set(function) in (declaration_keys, definition_keys)
            and isinstance(arguments, list)
        ):
            arities[name] = len(arguments)
    return arities


def _finite_span_within_caller_policy(lower, upper):
    from .construction_limits import current_construction_limits
    limit = current_construction_limits().max_finite_elements
    return 0 <= upper - lower and (limit is None or upper - lower <= limit)


def adapt_provider_forms(model):
    """Return ``(adapted_model, ledger)`` for recognized one-key op forms.

    Explicit expression slots in exact function definitions, hard/soft constraints,
    objectives, and a validity goal are visited. Unknown or malformed
    expression objects are left intact. Source spans and all non-expression
    fields are copied without interpretation.
    """
    result = deepcopy(model)
    if not isinstance(result, dict):
        return result, []
    ledger = []
    function_arities = _declared_function_arities(result)

    def pointer(path, component):
        escaped = str(component).replace("~", "~0").replace("/", "~1")
        return path + "/" + escaped

    # HIR's public API requires both legal identifier spellings and one shared
    # top-level term namespace. A scalar Entity individual can be alpha-renamed
    # when its spelling is invalid or when exactly one explicit function has
    # the same name. Rewriting exact {"var": name} leaves preserves the symbol
    # denotation while leaving function applications untouched. Only exact
    # scalar Entity declarations are eligible; arrays, shapes, bounds, opaque
    # data, ambiguous function names, and malformed declarations stay intact.
    # Targets are collision-checked against all model strings.
    def valid_hir_identifier(name):
        return isinstance(name, str) and name.isidentifier() and len(name) <= 128

    def renameable_source_name(name):
        if not isinstance(name, str) or valid_hir_identifier(name) or not name.strip():
            return False
        try:
            name.encode("utf-8")
        except UnicodeEncodeError:
            return False
        return True

    def collect_strings(value, found):
        if isinstance(value, str):
            found.add(value)
        elif isinstance(value, dict):
            for key, item in value.items():
                collect_strings(key, found)
                collect_strings(item, found)
        elif isinstance(value, list):
            for item in value:
                collect_strings(item, found)

    occupied_identifiers = set()
    collect_strings(result, occupied_identifiers)
    identifier_renames = {}
    declarations = result.get("declarations")
    def explicit_individual_declaration(declaration):
        return (
            isinstance(declaration, dict)
            and set(declaration) == {"name", "sort"}
            and isinstance(declaration.get("name"), str)
            and declaration.get("sort") == {"Uninterpreted": "Entity"}
        )

    if isinstance(declarations, list):
        scalar_declaration_counts = {}
        for declaration in declarations:
            if isinstance(declaration, dict) and isinstance(declaration.get("name"), str):
                name = declaration["name"]
                scalar_declaration_counts[name] = scalar_declaration_counts.get(name, 0) + 1

        # Only count function records with the exact public declaration or
        # definition key shape and a list-valued signature. Duplicate/malformed
        # function records are ambiguous and cannot justify alpha-renaming.
        # Count every named record first. A malformed extra record with the
        # same name still makes the collision ambiguous; shape checks happen
        # only after uniqueness is established.
        function_name_counts = {}
        function_records_by_name = {}
        functions = result.get("functions")
        if isinstance(functions, list):
            for function in functions:
                if isinstance(function, dict) and isinstance(function.get("name"), str):
                    name = function["name"]
                    function_name_counts[name] = function_name_counts.get(name, 0) + 1
                    function_records_by_name[name] = function

        function_declaration_keys = {"name", "arguments", "result"}
        function_definition_keys = function_declaration_keys | {"binders", "body", "span"}
        def unique_explicit_function(name):
            function = function_records_by_name.get(name)
            return (
                function_name_counts.get(name) == 1
                and isinstance(function, dict)
                and set(function) in (function_declaration_keys, function_definition_keys)
                and isinstance(function.get("arguments"), list)
            )

        datatype_names = set()
        datatypes = result.get("datatypes")
        if isinstance(datatypes, list):
            for datatype in datatypes:
                if not isinstance(datatype, dict) or not isinstance(datatype.get("constructors"), list):
                    continue
                for constructor in datatype["constructors"]:
                    if not isinstance(constructor, dict):
                        continue
                    if isinstance(constructor.get("name"), str):
                        datatype_names.add(constructor["name"])
                    fields = constructor.get("fields")
                    if isinstance(fields, list):
                        datatype_names.update(
                            field["name"] for field in fields
                            if isinstance(field, dict) and isinstance(field.get("name"), str)
                        )

        reserved_names = _reserved_operator_names()
        invalid_names = {
            declaration["name"] for declaration in declarations
            if explicit_individual_declaration(declaration)
            and renameable_source_name(declaration["name"])
        }
        namespace_collision_names = {
            declaration["name"] for declaration in declarations
            if explicit_individual_declaration(declaration)
            and valid_hir_identifier(declaration["name"])
            and scalar_declaration_counts.get(declaration["name"]) == 1
            and unique_explicit_function(declaration["name"])
            and declaration["name"] not in datatype_names
            and declaration["name"] not in reserved_names
        }
        names_to_rename = sorted(invalid_names | namespace_collision_names)
        rename_rules = {
            name: "explicit-individual-identifier-alpha-renaming"
            for name in invalid_names
        }
        for name in namespace_collision_names:
            rename_rules.setdefault(name, "entity-function-namespace-alpha-renaming")
        for original in names_to_rename:
            digest = hashlib.sha256(original.encode("utf-8")).hexdigest()
            candidate = "_somt_source_" + digest
            suffix = 0
            while candidate in occupied_identifiers:
                suffix += 1
                candidate = "_somt_source_" + digest + "_" + str(suffix)
            identifier_renames[original] = candidate
            occupied_identifiers.add(candidate)
        for index, declaration in enumerate(declarations):
            if (explicit_individual_declaration(declaration)
                    and declaration["name"] in identifier_renames):
                before = declaration["name"]
                declaration["name"] = identifier_renames[before]
                ledger.append(dict(
                    path=pointer(pointer("", "declarations"), index) + "/name",
                    rule=rename_rules[before],
                    before=before, after=declaration["name"],
                ))
        # Recompute after alpha-renaming: a formerly colliding explicit
        # function is now unambiguous for the existing {op, args} adapter.
        function_arities = _declared_function_arities(result)

    def valid_binders(binders, *, allow_empty=False):
        return (isinstance(binders, list) and (allow_empty or bool(binders))
                and all(isinstance(binder, dict) and set(binder) == {"name", "sort"}
                        and isinstance(binder["name"], str) for binder in binders))

    def explicit_expression(value):
        return isinstance(value, dict) or type(value) in (int, bool)

    def scoped_expression(binders, body, path):
        # A same-spelled lexical binder shadows a declared individual. Do not
        # rewrite those body references as references to the top-level symbol.
        shadowed = {}
        if isinstance(binders, list):
            for binder in binders:
                if (isinstance(binder, dict) and isinstance(binder.get("name"), str)
                        and binder["name"] in identifier_renames):
                    name = binder["name"]
                    shadowed[name] = identifier_renames.pop(name)
        try:
            return expression(body, path)
        finally:
            identifier_renames.update(shadowed)

    def expression(value, path):
        if type(value) in (int, bool):
            # JSON integers and Booleans have exact, distinct sorts. Only this
            # expression visitor performs the conversion: numeric metadata,
            # explicit typed literal payloads and opaque data remain untouched.
            rewritten = {"literal": value, "sort": "Bool" if type(value) is bool else "Int"}
            ledger.append(dict(path=path, rule="exact-JSON-scalar-expression",
                               before=value, after=deepcopy(rewritten)))
            return rewritten
        if not isinstance(value, dict):
            return value
        if set(value) == {"literal"} and type(value["literal"]) in (int, bool):
            # A JSON scalar has the same exact sort as its unwrapped form.
            # Decimal strings and floating-point values remain ambiguous.
            rewritten = {"literal": value["literal"],
                         "sort": "Bool" if type(value["literal"]) is bool else "Int"}
            ledger.append(dict(path=path, rule="exact-JSON-literal-sort",
                               before=deepcopy(value), after=deepcopy(rewritten)))
            return rewritten

        if (set(value) == {"var", "indices"} and isinstance(value["var"], str)
                and isinstance(value["indices"], list) and value["indices"]):
            # Explicit indices distinguish this provider spelling from a
            # variable leaf. Retain their order and every expression; HIR
            # still checks declaration, scope, rank, and exact index sorts.
            rewritten = {"at": value["var"], "indices": deepcopy(value["indices"])}
            ledger.append(dict(path=path, rule="explicit-indexed-variable-access",
                               before=deepcopy(value), after=deepcopy(rewritten)))
            return expression(rewritten, path)

        if (set(value) == {"var"} and isinstance(value["var"], str)
                and value["var"] in identifier_renames):
            rewritten = {"var": identifier_renames[value["var"]]}
            ledger.append(dict(
                path=pointer(path, "var"),
                rule=rename_rules[value["var"]],
                before=value["var"], after=rewritten["var"],
            ))
            return rewritten

        operator, arguments = None, None
        if set(value) == {"op", "args"}:
            operator, arguments = value["op"], value["args"]
        elif len(value) == 1:
            operator, arguments = next(iter(value.items()))
        # A square is multiplication by the same term and is exact for both
        # Int and Real operands. Keep this deliberately narrower than a
        # general power operator: only the canonical two-argument form with
        # an exact Int exponent literal 2 is rewritten. Do not infer exponent
        # sorts from Python booleans, coerce numeric strings, or choose
        # semantics for zero/negative/nonliteral exponents.
        if (
            set(value) == {"op", "args"}
            and value["op"] == "pow"
            and "pow" not in function_arities
            and isinstance(arguments, list)
            and len(arguments) == 2
            and isinstance(arguments[1], dict)
            and set(arguments[1]) == {"literal", "sort"}
            and type(arguments[1]["literal"]) is int
            and arguments[1]["sort"] == "Int"
            and arguments[1]["literal"] == 2
            and explicit_expression(arguments[0])
        ):
            base = deepcopy(arguments[0])
            rewritten = {"op": "mul", "args": [base, deepcopy(base)]}
            ledger.append(dict(path=path, rule="exact-square-to-multiplication",
                               before=deepcopy(value), after=deepcopy(rewritten)))
            return expression(rewritten, path)

        if (isinstance(operator, str) and operator in _SYMBOLIC_OPERATORS
                and isinstance(arguments, list)
                and _arity_ok(_SYMBOLIC_OPERATORS[operator], arguments)):
            rewritten = {"op": _SYMBOLIC_OPERATORS[operator],
                         "args": deepcopy(arguments)}
            ledger.append(dict(path=path, rule="symbolic-operator-spelling",
                               before=deepcopy(value), after=deepcopy(rewritten)))
            return expression(rewritten, path)

        # Some providers pass the finite all-different vector as one argument.
        # Unwrap exactly that vector, retaining order and repeated positions.
        # Do not flatten arbitrary lists or reinterpret typed arrays/tuples.
        if (isinstance(operator, str) and operator in {"all_different", "allDifferent"}
                and isinstance(arguments, list) and len(arguments) == 1
                and isinstance(arguments[0], list)
                and _arity_ok("all_different", arguments[0])
                and all(explicit_expression(item) for item in arguments[0])):
            rewritten = {"op": "all_different", "args": deepcopy(arguments[0])}
            ledger.append(dict(path=path, rule="all-different-explicit-vector",
                               before=deepcopy(value), after=deepcopy(rewritten)))
            return expression(rewritten, path)

        # Normalize quantifier tags before walking their bodies. The numeric
        # canonicalizer runs after this adapter; deferring the tag rewrite to
        # that later pass would leave singleton operators in the body unvisited.
        # Matching redundant tags are explicit aliases, conflicting tags are not.
        if (set(value) in ({"op", "binders", "body"},
                           {"op", "quantifier", "binders", "body"})
                and isinstance(value["op"], str)
                and value["op"] in {"forall", "exists", "exists_unique"}
                and value.get("quantifier", value["op"]) == value["op"]
                and valid_binders(value["binders"])
                and explicit_expression(value["body"])):
            rewritten = {"quantifier": value["op"],
                         "binders": deepcopy(value["binders"]), "body": deepcopy(value["body"])}
            ledger.append(dict(path=path, rule="tagged-quantifier-constructor",
                               before=deepcopy(value), after=deepcopy(rewritten)))
            return expression(rewritten, path)

        for quantifier in ("forall", "exists", "exists_unique"):
            if (set(value) == {quantifier, "body"}
                    and valid_binders(value[quantifier]) and explicit_expression(value["body"])):
                rewritten = {"quantifier": quantifier,
                             "binders": deepcopy(value[quantifier]), "body": deepcopy(value["body"])}
                ledger.append(dict(path=path, rule="named-quantifier-constructor",
                                   before=deepcopy(value), after=deepcopy(rewritten)))
                return expression(rewritten, path)

        # Provider schemas name the array-access constructor as well as showing
        # its fields. Accept only those exact redundant wrappers; never turn an
        # arbitrary function/operator name into a declaration or change indices.
        if set(value) == {"array_access"}:
            spec = value["array_access"]
            if (isinstance(spec, dict) and set(spec) == {"at", "indices"}
                    and isinstance(spec["at"], str)
                    and isinstance(spec["indices"], list) and spec["indices"]):
                rewritten = deepcopy(spec)
                ledger.append(dict(path=path, rule="named-array-access-constructor",
                                   before=deepcopy(value), after=deepcopy(rewritten)))
                return expression(rewritten, path)
            return value

        if (set(value) == {"op", "at", "indices"}
                and value["op"] == "array_access"
                and isinstance(value["at"], str)
                and isinstance(value["indices"], list) and value["indices"]):
            rewritten = {"at": value["at"], "indices": deepcopy(value["indices"])}
            ledger.append(dict(path=path, rule="tagged-array-access-constructor",
                               before=deepcopy(value), after=deepcopy(rewritten)))
            return expression(rewritten, path)

        if "cp" in value:
            from .hir_cp import cp_api

            kind = value["cp"]
            catalog = cp_api()["constructors"]
            # Some providers repeat the constructor tag as a one-key wrapper.
            # Unwrap only a complete, explicitly named constructor. Unknown
            # fields or missing polarity/counts remain errors, never guesses.
            if set(value) == {"cp"} and isinstance(kind, dict):
                inner_kind = kind.get("cp")
                if (isinstance(inner_kind, str) and inner_kind in catalog
                        and set(kind) == set(catalog[inner_kind])):
                    rewritten = deepcopy(kind)
                    ledger.append(dict(path=path, rule="named-cp-constructor",
                                       before=deepcopy(value), after=deepcopy(rewritten)))
                    return expression(rewritten, path)
                return value
            if (not isinstance(kind, str) or kind not in catalog
                    or set(value) != set(catalog[kind])):
                return value
            vector_fields = {
                "sum": ("items",), "minimum": ("items",),
                "maximum": ("items",), "all_different": ("items",),
                "among": ("items",), "global_cardinality": ("items",),
                "element": ("items",), "table": ("items",),
                "lex": ("left", "right"), "no_overlap": ("starts",),
                "cumulative": ("starts",), "circuit": ("successors",),
                "subcircuit": ("successors",),
                "regular": ("items",),
                "weighted_count": ("items", "weights"),
            }
            for field in vector_fields.get(kind, ()):
                vector = value[field]
                field_path = pointer(path, field)
                if isinstance(vector, list):
                    value[field] = [expression(arg, pointer(field_path, i))
                                    for i, arg in enumerate(vector)]
                elif (isinstance(vector, dict)
                      and set(vector) == {"array", "length", "prefix"}
                      and isinstance(vector["prefix"], list)):
                    vector["prefix"] = [
                        expression(arg, pointer(pointer(field_path, "prefix"), i))
                        for i, arg in enumerate(vector["prefix"])
                    ]
            for field in {"abs": ("value",), "element": ("index", "default"),
                          "cumulative": ("capacity",)}.get(kind, ()):
                value[field] = expression(value[field], pointer(path, field))
            if kind == "global_cardinality" and isinstance(value["counts"], list):
                value["counts"] = [
                    expression(arg, pointer(pointer(path, "counts"), i))
                    for i, arg in enumerate(value["counts"])
                ]
            if kind == "diffn":
                for field in ("positions", "sizes"):
                    if isinstance(value[field], list):
                        for i, row in enumerate(value[field]):
                            if isinstance(row, list):
                                value[field][i] = [expression(arg, pointer(pointer(pointer(path, field), i), j))
                                                  if isinstance(arg, dict) else arg
                                                  for j, arg in enumerate(row)]
            # Integer data (values, durations, tuples, automata) is never
            # interpreted as expressions or repaired by this adapter.
            return value

        if set(value) == {"data_lookup"}:
            spec = value["data_lookup"]
            if (isinstance(spec, dict) and set(spec) == {"data", "indices", "default"}
                    and isinstance(spec["data"], str)
                    and isinstance(spec["indices"], list)
                    and explicit_expression(spec["default"])):
                rewritten = deepcopy(spec)
                ledger.append(dict(path=path, rule="named-data-lookup-constructor",
                                   before=deepcopy(value), after=deepcopy(rewritten)))
                # The existing HIR lookup enforces that the table is present;
                # adapting this wrapper never manufactures missing data.
                return expression(rewritten, path)
            return value

        # Some provider outputs wrap the already documented finite-fold
        # object in one redundant singleton key. Keep this deliberately
        # narrower than general singleton-operator conversion: only the exact
        # fold fields and bounds accepted by HIR are eligible.
        if set(value) == {"finite_fold"}:
            spec = value["finite_fold"]
            if (
                isinstance(spec, dict)
                and set(spec) == {"fold", "var", "range", "body"}
                and isinstance(spec["fold"], str)
                and spec["fold"] in {"sum", "forall", "exists"}
                and isinstance(spec["var"], str)
                and spec["var"].isidentifier()
                and len(spec["var"]) <= 128
                and spec["var"].lower()
                not in {"true", "false", "tdiv", "ite", "and", "or", "not"}
                and isinstance(spec["range"], list)
                and len(spec["range"]) == 2
                and all(type(bound) is int for bound in spec["range"])
                and _finite_span_within_caller_policy(*spec["range"])
                and explicit_expression(spec["body"])
            ):
                rewritten = deepcopy(spec)
                ledger.append(
                    {
                        "path": path,
                        "rule": "finite-fold-singleton-constructor",
                        "before": deepcopy(value),
                        "after": deepcopy(rewritten),
                    }
                )
                return expression(rewritten, path)
            return value

        # Datatype terms carry sorts/signatures verbatim; only recurse into
        # their expression children and preserve the explicit declaration data.
        if set(value) == {"dt_constructor", "sort", "args"}:
            if isinstance(value["args"], list):
                value["args"] = [
                    expression(arg, pointer(pointer(path, "args"), i))
                    for i, arg in enumerate(value["args"])
                ]
            return value
        if set(value) == {"dt_selector", "sort", "value"}:
            value["value"] = expression(value["value"], pointer(path, "value"))
            return value
        if set(value) == {"dt_tester", "value"}:
            value["value"] = expression(value["value"], pointer(path, "value"))
            return value

        # These constructors contain expression values but keep their sort,
        # field order and structural metadata unchanged.
        if set(value) == {"const_array"}:
            spec = value["const_array"]
            if isinstance(spec, dict) and set(spec) == {"index_sort", "value"}:
                spec["value"] = expression(spec["value"], pointer(pointer(path, "const_array"), "value"))
            return value
        if set(value) == {"tuple"}:
            fields = value["tuple"]
            if isinstance(fields, list) and fields:
                value["tuple"] = [expression(field, pointer(pointer(path, "tuple"), i))
                                  for i, field in enumerate(fields)]
            return value

        # Dedicated singleton constructors must be dispatched before the
        # provider-only one-key operator form below.
        if set(value) == {"op_indexed"}:
            spec = value["op_indexed"]
            if (
                isinstance(spec, dict)
                and set(spec) == {"op", "indices", "args"}
                and isinstance(spec["op"], str)
                and spec["op"] in INDEXED_OPERATIONS
                and isinstance(spec["indices"], list)
                and isinstance(spec["args"], list)
                and (INDEXED_OPERATIONS[spec["op"]][0] is None
                     or len(spec["indices"]) == INDEXED_OPERATIONS[spec["op"]][0])
                and len(spec["args"]) == INDEXED_OPERATIONS[spec["op"]][1]
                and all(type(index) is int and index >= 0 for index in spec["indices"])
            ):
                spec["args"] = [
                    expression(
                        arg,
                        pointer(pointer(pointer(path, "op_indexed"), "args"), i),
                    )
                    for i, arg in enumerate(spec["args"])
                ]
            return value

        # The only provider-specific rewrite: {"op_name": [args...]} to the
        # documented {"op": "op_name", "args": [...]} form.
        if len(value) == 1:
            operator, arguments = next(iter(value.items()))
            # A unary operator has exactly one explicit expression operand.
            # This covers provider objects such as {"not": {"apply": ...}}
            # without interpreting dictionary values as an ordered argument list.
            if (operator in OPERATIONS and OPERATIONS[operator] == (1, 1)
                    and explicit_expression(arguments)):
                rewritten = {"op": operator, "args": [deepcopy(arguments)]}
                ledger.append(dict(path=path, rule="unary-operator-object",
                                   before=deepcopy(value), after=deepcopy(rewritten)))
                return expression(rewritten, path)
            if (
                operator in OPERATIONS
                and isinstance(arguments, list)
                and _arity_ok(operator, arguments)
            ):
                rewritten = {"op": operator, "args": deepcopy(arguments)}
                ledger.append(
                    {
                        "path": path,
                        "rule": "singleton-operator-object",
                        "before": deepcopy(value),
                        "after": deepcopy(rewritten),
                    }
                )
                rewritten["args"] = [
                    expression(arg, pointer(pointer(path, "args"), i))
                    for i, arg in enumerate(rewritten["args"])
                ]
                return rewritten
            # Unknown names and malformed singleton forms remain untouched,
            # including any descendants they contain.
            return value

        if set(value) == {"op", "args"}:
            operator, arguments = value["op"], value["args"]
            if (
                isinstance(operator, str)
                and operator in function_arities
                and isinstance(arguments, list)
                and len(arguments) == function_arities[operator]
            ):
                rewritten = {"apply": operator, "args": deepcopy(arguments)}
                ledger.append(
                    dict(path=path, rule="declared-function-op-tag",
                         before=deepcopy(value), after=deepcopy(rewritten))
                )
                return expression(rewritten, path)
            # These aliases are resolved by the following canonicalizer.
            # Visit their operands now, retaining the operator spelling and
            # its separate existing ledger entry in that later pass.
            canonical_alias = {"sum": "add", "allDifferent": "all_different"}
            if (
                isinstance(operator, str) and isinstance(arguments, list)
                and ((operator in OPERATIONS and _arity_ok(operator, arguments))
                     or (operator in canonical_alias
                         and _arity_ok(canonical_alias[operator], arguments))
                     or (operator in {"min", "max", "minimum", "maximum"}
                         and 1 <= len(arguments) <= 1000)
                     or (operator == "abs" and len(arguments) == 1))
            ):
                value["args"] = [
                    expression(arg, pointer(pointer(path, "args"), i))
                    for i, arg in enumerate(arguments)
                ]
            return value

        if set(value) == {"at", "indices"} and isinstance(value["indices"], list):
            value["indices"] = [
                expression(arg, pointer(pointer(path, "indices"), i))
                for i, arg in enumerate(value["indices"])
            ]
            return value

        if set(value) == {"data", "indices", "default"} and isinstance(value["indices"], list):
            value["indices"] = [
                expression(arg, pointer(pointer(path, "indices"), i))
                for i, arg in enumerate(value["indices"])
            ]
            value["default"] = expression(value["default"], pointer(path, "default"))
            return value

        if set(value) == {"apply", "args"} and isinstance(value["args"], list):
            value["args"] = [
                expression(arg, pointer(pointer(path, "args"), i))
                for i, arg in enumerate(value["args"])
            ]
            return value

        if set(value) == {"quantifier", "binders", "body"}:
            binders = value["binders"]
            if (
                isinstance(value["quantifier"], str)
                and value["quantifier"] in {"forall", "exists", "exists_unique"}
                and isinstance(binders, list)
                and binders
                and all(
                    isinstance(binder, dict)
                    and set(binder) == {"name", "sort"}
                    and isinstance(binder["name"], str)
                    for binder in binders
                )
            ):
                value["body"] = scoped_expression(
                    binders, value["body"], pointer(path, "body")
                )
            return value

        if set(value) == {"fold", "var", "range", "body"}:
            span = value["range"]
            if (
                isinstance(value["fold"], str)
                and value["fold"] in {"sum", "forall", "exists"}
                and isinstance(value["var"], str)
                and isinstance(span, list)
                and len(span) == 2
                and all(type(bound) is int for bound in span)
                and _finite_span_within_caller_policy(*span)
            ):
                value["body"] = scoped_expression(
                    [{"name": value["var"]}], value["body"], pointer(path, "body")
                )
            return value

        # Variables, literals, rounding modes, unknown constructors, and
        # unsupported features are left byte-for-byte
        # equal in the deep copy.
        return value

    def annotated_statement(entry, expected_keys, path):
        # The expression and source span are already explicit. Rehouse only
        # a complete catalogued constructor; never fill a missing operand,
        # span, objective sense or type conversion. New proposals record this
        # in their normalization ledger; serialized candidates are unchanged.
        if not isinstance(entry, dict) or "expr" in entry:
            return entry
        metadata = expected_keys - {"expr"}
        if not metadata <= entry.keys():
            return entry
        body = {key: value for key, value in entry.items() if key not in metadata}
        operator = body.get("op")
        recognized = (set(body) == {"op", "args"}
                      and isinstance(operator, str) and operator in OPERATIONS
                      and isinstance(body["args"], list)
                      and _arity_ok(operator, body["args"]))
        if isinstance(body.get("cp"), str):
            from .hir_cp import cp_api
            signature = cp_api()["constructors"].get(body["cp"])
            recognized = signature is not None and set(body) == set(signature)
        if set(body) == {"quantifier", "binders", "body"}:
            recognized = (body["quantifier"] in ("forall", "exists", "exists_unique")
                          and valid_binders(body["binders"])
                          and explicit_expression(body["body"]))
        span = entry["span"]
        if (not recognized or not isinstance(span, list) or len(span) != 2
                or any(type(value) is not int for value in span)
                or not 0 <= span[0] < span[1]
                or ("sense" in metadata and entry["sense"] not in ("minimize", "maximize"))):
            return entry
        wrapped = {key: deepcopy(entry[key]) for key in metadata}
        wrapped["expr"] = deepcopy(body)
        ledger.append(dict(path=path, rule="annotated-expression-statement",
                           before=deepcopy(entry), after=deepcopy(wrapped)))
        return wrapped

    def slot(entries, section, expected_keys):
        if not isinstance(entries, list):
            return
        for index, entry in enumerate(entries):
            path = pointer(pointer("", section), index)
            entries[index] = entry = annotated_statement(entry, expected_keys, path)
            if isinstance(entry, dict) and set(entry) == expected_keys:
                entry["expr"] = expression(entry["expr"], path + "/expr")

    # Function bodies are explicit expression slots too. Require the complete
    # declared-definition shape before traversing them; malformed definitions
    # and extra fields stay opaque.
    definitions = result.get("functions")
    if isinstance(definitions, list):
        for index, function in enumerate(definitions):
            if (
                isinstance(function, dict)
                and set(function) == {"name", "arguments", "result", "binders", "body", "span"}
                and isinstance(function["name"], str)
                and function["name"] in function_arities
                and valid_binders(function["binders"], allow_empty=True)
                and explicit_expression(function["body"])
            ):
                function["body"] = scoped_expression(
                    function["binders"], function["body"],
                    pointer(pointer("", "functions"), index) + "/body"
                )

    constraints = result.get("constraints")
    if isinstance(constraints, list):
        for index, entry in enumerate(constraints):
            # Providers sometimes attach a human-readable label to a hard
            # constraint. HIR constraints have no label field, so remove only
            # this exact string annotation and retain it in the normalization
            # ledger. Other extra fields, and labels of any other type, remain
            # untouched for the closed schema validator to reject.
            if (isinstance(entry, dict)
                    and set(entry) == {"expr", "span", "name"}
                    and isinstance(entry["name"], str)):
                before = deepcopy(entry)
                del entry["name"]
                ledger.append(dict(
                    path=pointer("", "constraints") + f"/{index}",
                    rule="provider-constraint-name-annotation",
                    before=before,
                    after=deepcopy(entry),
                ))
    slot(constraints, "constraints", {"expr", "span"})
    slot(result.get("soft_constraints"), "soft_constraints", {"expr", "span", "weight", "group"})
    slot(result.get("objectives"), "objectives", {"expr", "span", "sense"})
    goal = annotated_statement(result.get("goal"), {"expr", "span"}, "/goal")
    if "goal" in result:
        result["goal"] = goal
    if isinstance(goal, dict) and set(goal) == {"expr", "span"}:
        goal["expr"] = expression(goal["expr"], "/goal/expr")

    return result, ledger
