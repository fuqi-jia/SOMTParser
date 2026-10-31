"""Typed CP constructor macros that expand directly into the native HIR API.

Expansion preserves logical polarity: automaton and circuit witnesses are
locally existentially quantified, never asserted as global auxiliary facts.
No generated code is executed and no SMT text is parsed during construction.
"""
from copy import deepcopy
import json
from .hir import build_hir
from ._nl_model import ModelError, keys, number

MAX_EXPANDED_NODES = 100000


def _check_expansion_size(value):
    stack = [value]
    nodes = 0
    while stack:
        nodes += 1
        if nodes > MAX_EXPANDED_NODES:
            raise ModelError("expanded CP model exceeds 100000 JSON nodes")
        current = stack.pop()
        if isinstance(current, dict):
            stack.extend(current.values())
        elif isinstance(current, list):
            stack.extend(current)


def cp_api():
    return {
        "version": "somt-hir-cp-v1",
        "integration": "Use these expressions inside somt-hir-model-v1; the standard HIR builder validates constructor inputs and directly builds supported native expressions. CpProvider supplies this catalog without expanding the returned JSON. Explicit JSON expansion remains available through expand_cp_model.",
        "named_operator_form": "CP globals may also use {op: constructor, ...fields}; all documented fields, including explicit strict/nonstrict flags, are required. The builder normalizes this exact form to {cp: constructor, ...fields}.",
        "vector": "An expression list, or {array: declared_name, length: n, prefix: [fixed index expressions]}. For a shaped array, prefix fixes every axis before the final axis and length is at most the final-axis size; it does not flatten dimensions. Indices are zero-based.",
        "constructors": {
            "sum": {"cp": "sum", "items": "vector"},
            "minimum": {"cp": "minimum", "items": "nonempty Int vector"},
            "maximum": {"cp": "maximum", "items": "nonempty Int vector"},
            "abs": {"cp": "abs", "value": "Int expression"},
            "all_different": {"cp": "all_different", "items": "Int vector"},
            "all_different_except_0": {
                "cp": "all_different_except_0",
                "items": "Int vector; any number of zero entries is ignored",
            },
            "connected": {
                "cp": "connected",
                "from": "fixed zero-based source-node indices, one per edge",
                "to": "fixed zero-based target-node indices, one per edge",
                "nodes": "Bool vector selecting graph nodes",
                "edges": "Bool vector selecting graph edges",
            },
            "dconnected": {
                "cp": "dconnected",
                "from": "fixed zero-based source-node indices, one per edge",
                "to": "fixed zero-based target-node indices, one per edge",
                "nodes": "Bool vector selecting graph nodes",
                "edges": "Bool vector selecting graph edges",
            },
            "among": {
                "cp": "among",
                "items": "Int vector",
                "values": "explicit finite list of exact Int values; duplicates denote one set member",
            },
            "count_true": {
                "cp": "count_true",
                "items": "Bool vector; returns the number of true entries as Int, counting every position",
            },
            "weighted_count": {
                "cp": "weighted_count",
                "items": "Bool vector; every position contributes independently",
                "weights": "same-length vector of exact expressions with the declared sort",
                "sort": "required Int or Real; no implicit numeric coercion",
            },
            "at_most_one": {
                "cp": "at_most_one",
                "items": "Bool vector; true iff at most one position is true",
            },
            "global_cardinality": {
                "cp": "global_cardinality",
                "items": "Int vector",
                "values": "distinct exact Int values",
                "counts": "same-length list of Int expressions",
                "closed": "required Boolean; when true every item must be in values",
            },
            "element": {
                "cp": "element",
                "items": "vector",
                "index": "Int expression",
                "default": "explicit out-of-range value",
            },
            "table": {
                "cp": "table",
                "items": "Int vector",
                "tuples": "list of equal-width integer tuples",
                "positive": "required Boolean: true allows listed tuples, false forbids them; derive polarity from source",
            },
            "lex": {
                "cp": "lex",
                "left": "Int vector",
                "right": "same-length Int vector",
                "strict": False,
            },
            "no_overlap": {
                "cp": "no_overlap",
                "starts": "Int vector",
                "durations": "equal-length nonnegative integer list",
            },
            "diffn": {
                "cp": "diffn",
                "dimensions": "positive integer dimension count",
                "positions": "list of Int vectors, one vector per box, each of length dimensions",
                "sizes": "same-shaped list of Int vectors or integer lists",
                "nonstrict": False,
            },
            "cumulative": {
                "cp": "cumulative",
                "starts": "Int vector",
                "durations": "equal-length nonnegative Int vector or integer list",
                "demands": "equal-length nonnegative Int vector or integer list",
                "capacity": "Int expression",
            },
            "circuit": {
                "cp": "circuit",
                "successors": "nonempty Int vector, zero-based; single Hamiltonian cycle, self-loop allowed only for size one",
            },
            "subcircuit": {
                "cp": "subcircuit",
                "successors": "Int vector, zero-based; self-successors are inactive, all other vertices form one cycle",
                "allow_empty": "required Boolean: whether all vertices may be inactive, including an empty vector",
            },
            "regular": {
                "cp": "regular",
                "items": "Int vector",
                "start": "integer state",
                "finals": "integer states",
                "transitions": "integer triples [from,symbol,to]",
            },
        },
        "semantics": {
            "time": "integer starts and half-open intervals; zero-duration tasks consume no resources; no_overlap requires fixed nonnegative durations",
            "cumulative": "Int durations and demands may be expressions; the relation requires nonnegative durations, demands and capacity. Native HIR retains this global until shared event-time lowering, without an arbitrary scheduling horizon. Native cumulative vectors accept up to 100000 tasks within the HIR construction budget, with nested constructors retained for native compilation",
            "diffn": "Box pairs must separate in at least one axis, with touching allowed. nonstrict=true ignores boxes with any zero size; false retains them. Matches MiniZinc's algebraic decomposition without implicit size bounds; declare nonnegative size bounds when required by the problem. Native HIR retains the global until shared lowering. At most 1000 boxes and dimensions, 10000 coordinates",
            "witnesses": "circuit ranks and nondeterministic automaton paths are locally existential, including inside negation or implication; deterministic automata need no witness",
            "subcircuit": "Every successor lies in [0,n). Inactive vertices point to themselves; active vertices form exactly one nontrivial directed cycle, with no disjoint subtours. allow_empty explicitly determines the all-inactive case. The anchor and ranks are locally existential, so negation negates the entire relation, not a chosen witness",
            "regular": "Exact Int labels, including nondeterministic transitions. Direct HIR compiles each item once. Deterministic transitions use a total finite table and a fresh rejecting sink without quantified witnesses; nondeterministic transitions use shared columns with local existential state and entry arrays. Explicit JSON expansion remains available",
            "weighted_count": "sum of ite(items[i], weights[i], typed zero). Negative and exact rational weights are allowed; repeated positions count repeatedly. Empty vectors return zero of the explicitly declared Int or Real sort. Each weight is checked under its own true flag branch, retaining guarded partial arithmetic; flags must be Bool and every weight must exactly match sort",
            "finite_globals": "among returns an Int expression counting Int items belonging to values; values form a set so duplicates do not double-count. count_true returns an Int count of true Bool positions, preserving repeated vector positions. at_most_one is the linear-size Boolean cardinality relation over Bool positions. global_cardinality counts each item once per distinct listed value, and closed=true excludes unlisted values",
            "budgets": "vectors <=1000, except native cumulative <=100000 tasks within the HIR construction budget; explicit expanded JSON <=100000 nodes and native construction retains its HIR expression budget; native among/global_cardinality compile item expressions once and share them across membership/count relations without materializing the JSON cross-product; model source spans and unresolved choices are retained",
        },
    }


def normalize_cp_operator_form(expr):
    """Normalize a named CP-global call to the canonical cp constructor form.

    A few model producers spell globals as {op: "circuit", successors: ...}
    instead of {cp: "circuit", successors: ...}. Accept only a complete,
    unambiguous constructor argument set; malformed calls remain errors.
    """
    kind = expr.get("op")
    if not isinstance(kind, str) or "args" in expr:
        return None
    spec = cp_api()["constructors"].get(kind)
    if not isinstance(spec, dict):
        return None
    allowed = set(spec) - {"cp"}
    # The public constructors currently require every field at construction
    # time, including explicit strict/nonstrict flags; keep aliases exact.
    optional = set()
    supplied = set(expr) - {"op"}
    required = allowed - optional
    if not required <= supplied or not supplied <= allowed:
        return None
    return {"cp": kind, **{field: expr[field] for field in spec if field != "cp"}}


def _lit(n):
    return {"literal": n, "sort": "Int"}


def _bool(v):
    return {"literal": v, "sort": "Bool"}


def _op(op, *args):
    # Exact constant folding also avoids the backend's ambiguous all-zero
    # arithmetic application. No floating-point computation is involved.
    if op == "add" and all(
        isinstance(a, dict)
        and set(a) == {"literal", "sort"}
        and a["sort"] == "Int"
        and type(a["literal"]) is int
        for a in args
    ):
        return _lit(sum(a["literal"] for a in args))
    return {"op": op, "args": list(args)}


def _int_sort_guard(expr):
    """A logically true predicate for Int terms that rejects other sorts."""
    return _op(
        "eq",
        _op("mod_euclid", expr, _lit(1)),
        _lit(0),
    )


class _Expand:
    def __init__(self, model, reserved=(), finite_shapes=None):
        # A fresh binder must avoid every user-supplied spelling, including
        # local variables and names nested in other constructor expressions.
        self.used = {name for name in reserved if isinstance(name, str)}
        stack = [model]
        while stack:
            v = stack.pop()
            if isinstance(v, str):
                self.used.add(v)
            elif isinstance(v, dict):
                stack.extend(v.values())
            elif isinstance(v, list):
                stack.extend(v)
        self.serial = 0
        self.nodes = 0
        self.estimated_expanded_nodes = 0
        self.finite_shapes = {}
        if isinstance(model, dict):
            for declaration in model.get("declarations", []):
                if not isinstance(declaration, dict):
                    continue
                name = declaration.get("name")
                shape = declaration.get("shape")
                if (isinstance(name, str) and isinstance(shape, list)
                        and all(type(axis) is int and axis >= 0 for axis in shape)):
                    self.finite_shapes[name] = (tuple(shape), declaration.get("sort"))
        if finite_shapes:
            self.finite_shapes.update(finite_shapes)

    def tree_nodes(self, value):
        stack = [value]
        nodes = 0
        while stack:
            current = stack.pop()
            nodes += 1
            if nodes > MAX_EXPANDED_NODES:
                raise ModelError("CP expression exceeds 100000 JSON nodes")
            if isinstance(current, dict):
                stack.extend(current.values())
            elif isinstance(current, list):
                stack.extend(current)
        return nodes

    def reserve_expansion(self, estimate):
        self.estimated_expanded_nodes += estimate
        if self.estimated_expanded_nodes > MAX_EXPANDED_NODES:
            raise ModelError(
                "CP constructor expansion estimate exceeds 100000 JSON nodes"
            )

    def fresh(self):
        while True:
            self.serial += 1
            name = f"somt_cp_witness_{self.serial}"
            if name not in self.used:
                self.used.add(name)
                return name

    def vector(self, v, *, expand_items=True, max_length=1000):
        visit = self.expr if expand_items else lambda item: item
        if isinstance(v, list):
            if len(v) > max_length:
                raise ModelError(f"CP vector exceeds {max_length} elements")
            return [visit(x) for x in v]
        keys(v, ["array", "length"], ["prefix"])
        if (
            not isinstance(v["array"], str)
            or type(v["length"]) is not int
            or not 0 <= v["length"] <= max_length
        ):
            raise ModelError("invalid CP array vector")
        prefix = v.get("prefix", [])
        if not isinstance(prefix, list):
            raise ModelError("CP prefix must be an index list")
        shape_info = self.finite_shapes.get(v["array"])
        if shape_info is not None:
            shape = tuple(shape_info[0])
            expected_prefix = max(0, len(shape) - 1)
            last_axis_size = shape[-1] if shape else 0
            if (not shape or len(prefix) != expected_prefix
                    or v["length"] > last_axis_size):
                recommendation = (
                    " For all-different over every cell, use native HIR all_different "
                    "on the whole shaped array or list scalar cells explicitly."
                    if len(shape) > 1 else ""
                )
                raise ModelError(
                    "CP vector descriptor for " + repr(v["array"]) + " with shape "
                    + repr(list(shape)) + " requires exactly " + str(expected_prefix)
                    + " fixed prefix indices and length at most " + str(last_axis_size)
                    + " (the final-axis size); CP vectors do not flatten array axes."
                    + recommendation
                )
        return [
            {"at": v["array"], "indices": [visit(i) for i in prefix] + [_lit(i)]}
            for i in range(v["length"])
        ]

    def integers(self, v, length=None, nonnegative=False):
        if (
            not isinstance(v, list)
            or len(v) > 10000
            or any(type(x) is not int or (nonnegative and x < 0) for x in v)
        ):
            raise ModelError("CP constructor requires exact integer data")
        if length is not None and len(v) != length:
            raise ModelError("CP vector length mismatch")
        return v

    def cardinality_inputs(self, e):
        kind = e.get("cp")
        if kind not in {"among", "global_cardinality"}:
            raise ModelError("expected a finite-cardinality CP constructor")
        fields = ["cp", "items", "values"]
        keys(e, fields if kind == "among" else fields + ["counts", "closed"])
        items = self.vector(e["items"])
        values = self.integers(e["values"])
        if len(values) > 1000:
            raise ModelError("CP " + kind + " value set exceeds 1000 values")
        if kind == "among":
            return items, list(dict.fromkeys(values)), [], False
        if len(set(values)) != len(values):
            raise ModelError("CP global-cardinality values must be distinct")
        counts = e["counts"]
        if not isinstance(counts, list) or len(counts) != len(values):
            raise ModelError("CP global-cardinality values/counts length mismatch")
        if type(e["closed"]) is not bool:
            raise ModelError("CP global-cardinality closed must be Boolean")
        return items, values, [self.expr(count) for count in counts], e["closed"]

    def cumulative_inputs(self, e, *, expand_items=True, max_length=1000):
        keys(e, ["cp", "starts", "durations", "demands", "capacity"])
        starts = self.vector(e["starts"], expand_items=expand_items, max_length=max_length)
        vectors = []
        # Fixed data repeated across tasks should become one typed operand per
        # exact integer in the native path. Expansion retains independent JSON.
        constants = {}
        def integer_expr(value):
            if expand_items:
                return _lit(value)
            if value not in constants:
                constants[value] = _lit(value)
            return constants[value]
        for field in ("durations", "demands"):
            raw = e[field]
            if isinstance(raw, list):
                if any(type(x) is int and x < 0 for x in raw):
                    raise ModelError("cumulative requires nonnegative integer data")
                raw = [integer_expr(x) if type(x) is int else x for x in raw]
            values = self.vector(raw, expand_items=expand_items, max_length=max_length)
            if len(values) != len(starts):
                raise ModelError("CP vector length mismatch")
            vectors.append(values)
        capacity = self.expr(e["capacity"]) if expand_items else e["capacity"]
        return starts, vectors[0], vectors[1], capacity

    def regular_inputs(self, e):
        keys(e, ["cp", "items", "start", "finals", "transitions"])
        xs = self.vector(e["items"])
        self.integers([e["start"]])
        finals = self.integers(e["finals"])
        if not isinstance(e["transitions"], list) or len(e["transitions"]) > 10000:
            raise ModelError("invalid regular transitions")
        triples = [self.integers(t, 3) for t in e["transitions"]]
        for labels in ([e["start"]], finals, *triples):
            for label in labels:
                number(label, "Int", "regular label")
        return xs, e["start"], finals, triples

    def diffn_inputs(self, e):
        keys(e, ["cp", "dimensions", "positions", "sizes", "nonstrict"])
        dimensions = e["dimensions"]
        if type(dimensions) is not int or not 1 <= dimensions <= 1000:
            raise ModelError("diffn dimensions must be an integer in 1..1000")
        if type(e["nonstrict"]) is not bool:
            raise ModelError("diffn nonstrict must be Boolean")
        positions, sizes = e["positions"], e["sizes"]
        if (not isinstance(positions, list) or not isinstance(sizes, list)
                or len(positions) != len(sizes) or len(positions) > 1000
                or len(positions) * dimensions > 10000):
            raise ModelError("diffn requires equally shaped box matrices within the coordinate budget")
        matrices = []
        for matrix in (positions, sizes):
            rows = []
            for row in matrix:
                if isinstance(row, list):
                    row = [_lit(value) if type(value) is int else value for value in row]
                values = self.vector(row)
                if len(values) != dimensions:
                    raise ModelError("diffn box vector length differs from dimensions")
                rows.append(values)
            matrices.append(rows)
        return dimensions, matrices[0], matrices[1], e["nonstrict"]

    def expr(self, e):
        if not isinstance(e, dict) or "cp" not in e:
            return self._expr(e)
        guards = cp_validation_guards(
            e, reserved=self.used, finite_shapes=self.finite_shapes,
        )
        # Expand guards in this exact lexical position. Moving them outside a
        # quantifier would lose its bindings or change the source relation.
        guards = [self.expr(guard) for guard in guards]
        result = self._expr(e)
        return _op("ite", _op("and", *guards), result, result) if guards else result

    def _expr(self, e):
        self.nodes += 1
        if self.nodes > 100000:
            raise ModelError("CP expansion budget exceeded")
        if not isinstance(e, dict):
            raise ModelError("CP expression must be an object")
        if "cp" not in e:
            # Visit expression-valued fields only; literal data and binders are
            # not expressions, and may contain arbitrary user identifiers.
            e = deepcopy(e)
            for k in ["args", "indices"]:
                if k in e:
                    if not isinstance(e[k], list):
                        raise ModelError("expression arguments must be a list")
                    e[k] = [self.expr(x) for x in e[k]]
            if "op_indexed" in e and isinstance(e["op_indexed"], dict):
                spec = e["op_indexed"]
                if isinstance(spec.get("args"), list):
                    spec["args"] = [self.expr(x) for x in spec["args"]]
            if "default" in e:
                e["default"] = self.expr(e["default"])
            if "body" in e:
                # Shape metadata belongs to declarations, not spellings. A
                # quantifier or fold can bind the same name in its body.
                shadowed = set()
                if "quantifier" in e and isinstance(e.get("binders"), list):
                    shadowed.update(binder["name"] for binder in e["binders"]
                                    if isinstance(binder, dict)
                                    and isinstance(binder.get("name"), str))
                if "fold" in e and isinstance(e.get("var"), str):
                    shadowed.add(e["var"])
                outer_shapes = self.finite_shapes
                self.finite_shapes = {name: shape for name, shape in outer_shapes.items()
                                      if name not in shadowed}
                try:
                    e["body"] = self.expr(e["body"])
                finally:
                    self.finite_shapes = outer_shapes
            return e
        kind = e["cp"]
        if kind in ["connected", "dconnected"]:
            keys(e, ["cp", "from", "to", "nodes", "edges"])
            node_edges = self.integers(e["from"], nonnegative=True)
            target_edges = self.integers(e["to"], length=len(node_edges),
                                         nonnegative=True)
            nodes = self.vector(e["nodes"])
            edges = self.vector(e["edges"])
            if len(edges) != len(node_edges):
                raise ModelError("graph edge-selection vector length mismatch")
            for endpoint in node_edges + target_edges:
                if endpoint >= len(nodes):
                    raise ModelError("graph endpoint outside zero-based node range [0,N)")
            n, edge_count = len(nodes), len(edges)
            args = [_lit(n), _lit(edge_count)]
            args.extend(_lit(x) for x in node_edges)
            args.extend(_lit(x) for x in target_edges)
            args.extend(nodes)
            args.extend(edges)
            return _op(kind, *args)
        if kind in ["sum", "minimum", "maximum", "all_different",
                    "all_different_except_0"]:
            keys(e, ["cp", "items"])
            xs = self.vector(e["items"])
            if kind in ["sum", "all_different", "all_different_except_0"]:
                operator = {
                    "sum": "add",
                    "all_different": "all_different",
                    "all_different_except_0": "all_different_except_0",
                }[kind]
                return _op(operator, *xs)
            if not xs:
                raise ModelError("minimum/maximum of an empty vector is undefined")
            # Balanced expansion avoids the exponential duplication of a
            # left-associated min/max when serialized as a JSON expression.
            while len(xs) > 1:
                xs = [
                    _op(
                        "ite",
                        _op("le" if kind == "minimum" else "ge", xs[i], xs[i + 1]),
                        xs[i],
                        xs[i + 1],
                    )
                    if i + 1 < len(xs)
                    else xs[i]
                    for i in range(0, len(xs), 2)
                ]
            return xs[0]
        if kind == "weighted_count":
            keys(e, ["cp", "items", "weights", "sort"])
            if e["sort"] not in ("Int", "Real"):
                raise ModelError("weighted_count sort must be Int or Real")
            flags = self.vector(e["items"])
            weights = self.vector(e["weights"])
            if len(flags) != len(weights):
                raise ModelError("weighted_count items/weights length mismatch")
            zero = {"literal": 0 if e["sort"] == "Int" else "0", "sort": e["sort"]}
            self.reserve_expansion(
                4 + sum(10 + self.tree_nodes(flag) + self.tree_nodes(weight)
                        for flag, weight in zip(flags, weights))
            )
            if not flags:
                return zero
            # Expand JSON only: compiling a weight here would discard its
            # branch-local nonzero facts. Ordinary ITE validation checks Bool
            # flags and identical branch sorts against the explicit zero.
            return _op("add", *[_op("ite", flag, weight, zero)
                                 for flag, weight in zip(flags, weights)])
        if kind in ["count_true", "at_most_one"]:
            keys(e, ["cp", "items"])
            xs = self.vector(e["items"])
            # Each operand appears once in the generated count. Keep the
            # expansion estimate linear in the vector size and retain the
            # shared 100000-node ceiling used by the other CP constructors.
            self.reserve_expansion(
                (4 if kind == "count_true" else 12)
                + sum(self.tree_nodes(item) for item in xs)
            )
            if not xs:
                return _lit(0) if kind == "count_true" else _bool(True)
            count = _op("count", *xs)
            return count if kind == "count_true" else _op("le", count, _lit(1))
        if kind == "abs":
            keys(e, ["cp", "value"])
            x = self.expr(e["value"])
            return _op("ite", _op("ge", x, _lit(0)), x, _op("sub", _lit(0), x))
        if kind == "among":
            keys(e, ["cp", "items", "values"])
            xs = self.vector(e["items"])
            values = self.integers(e["values"])
            if len(values) > 1000:
                raise ModelError("CP among set exceeds 1000 values")
            # The semantic object is a finite set; repeated JSON entries do
            # not give an item multiple votes.
            values = list(dict.fromkeys(values))
            value_count = len(values)
            self.reserve_expansion(
                8
                + sum(
                    48 + (value_count + 1) * self.tree_nodes(item) + 9 * value_count
                    for item in xs
                )
            )
            terms = []
            for x in xs:
                membership = _op(
                    "or", *[_op("eq", x, _lit(value)) for value in values]
                )
                membership = _op("and", _int_sort_guard(x), membership)
                terms.append(_op("ite", membership, _lit(1), _lit(0)))
            return _op("add", *terms)
        if kind == "global_cardinality":
            keys(e, ["cp", "items", "values", "counts", "closed"])
            xs = self.vector(e["items"])
            values = self.integers(e["values"])
            if len(values) > 1000:
                raise ModelError("CP global-cardinality value set exceeds 1000 values")
            if len(set(values)) != len(values):
                raise ModelError("CP global-cardinality values must be distinct")
            counts = e["counts"]
            if not isinstance(counts, list) or len(counts) != len(values):
                raise ModelError("CP global-cardinality values/counts length mismatch")
            if type(e["closed"]) is not bool:
                raise ModelError("CP global-cardinality closed must be Boolean")
            counts = [self.expr(count) for count in counts]
            value_count = len(values)
            self.reserve_expansion(
                8
                + sum(
                    64
                    + self.tree_nodes(item)
                    * (1 + value_count * (2 if e["closed"] else 1))
                    + (32 if e["closed"] else 24) * value_count
                    for item in xs
                )
                + sum(32 + 2 * self.tree_nodes(count) for count in counts)
            )
            checks = []
            for value, count in zip(values, counts):
                actual = _op(
                    "add",
                    *[
                        _op(
                            "ite",
                            _op("eq", item, _lit(value)),
                            _lit(1),
                            _lit(0),
                        )
                        for item in xs
                    ],
                )
                checks.extend(
                    [_int_sort_guard(count), _op("eq", actual, count)]
                )
            checks.extend(_int_sort_guard(item) for item in xs)
            if e["closed"]:
                for item in xs:
                    membership = _op(
                        "or", *[_op("eq", item, _lit(value)) for value in values]
                    )
                    checks.append(membership)
            return _op("and", *checks)
        if kind == "element":
            keys(e, ["cp", "items", "index", "default"])
            xs, index, result = (
                self.vector(e["items"]),
                self.expr(e["index"]),
                self.expr(e["default"]),
            )
            for i in reversed(range(len(xs))):
                result = _op("ite", _op("eq", index, _lit(i)), xs[i], result)
            return result
        if kind == "table":
            if isinstance(e, dict) and "positive" not in e:
                raise ModelError(
                    "CP table requires the Boolean field 'positive'; true means the "
                    "listed tuples are allowed and false means they are forbidden; "
                    "derive polarity from the source"
                )
            keys(e, ["cp", "items", "tuples", "positive"])
            xs = self.vector(e["items"])
            if (
                type(e["positive"]) is not bool
                or not isinstance(e["tuples"], list)
                or len(e["tuples"]) > 10000
            ):
                raise ModelError("invalid CP table")
            rows = [self.integers(row, len(xs)) for row in e["tuples"]]
            formula = _op(
                "or",
                *[
                    _op("and", *[_op("eq", x, _lit(v)) for x, v in zip(xs, row)])
                    for row in rows
                ],
            )
            return formula if e["positive"] else _op("not", formula)
        if kind == "lex":
            keys(e, ["cp", "left", "right", "strict"])
            left, right = self.vector(e["left"]), self.vector(e["right"])
            if len(left) != len(right) or type(e["strict"]) is not bool:
                raise ModelError("invalid CP lex vectors")
            result = _bool(not e["strict"])
            for x, y in reversed(list(zip(left, right))):
                result = _op("or", _op("lt", x, y), _op("and", _op("eq", x, y), result))
            return result
        if kind == "cumulative":
            starts, durations, demands, capacity = self.cumulative_inputs(e)
            self.reserve_expansion(len(starts) ** 2 * 24)
            checks = [_op("ge", capacity, _lit(0))]
            checks.extend(_op("ge", x, _lit(0)) for x in durations + demands)
            for event in starts:
                terms = [
                    _op("ite", _op("and", _op("le", start, event),
                                   _op("lt", event, _op("add", start, duration))),
                        demand, _lit(0))
                    for start, duration, demand in zip(starts, durations, demands)
                ]
                checks.append(_op("le", _op("add", *terms), capacity))
            return _op("and", *checks)
        if kind == "diffn":
            dimensions, positions, sizes, nonstrict = self.diffn_inputs(e)
            self.reserve_expansion(len(positions) ** 2 * dimensions * 40)
            checks = [_int_sort_guard(value)
                      for matrix in (positions, sizes) for row in matrix for value in row]
            for i in range(len(positions)):
                for j in range(i):
                    axes = []
                    for d in range(dimensions):
                        axes.extend([
                            _op("le", _op("add", positions[i][d], sizes[i][d]), positions[j][d]),
                            _op("le", _op("add", positions[j][d], sizes[j][d]), positions[i][d]),
                        ])
                        if nonstrict:
                            axes.extend([_op("eq", sizes[i][d], _lit(0)),
                                         _op("eq", sizes[j][d], _lit(0))])
                    checks.append(_op("or", *axes))
            return _op("and", *checks)
        if kind == "no_overlap":
            keys(e, ["cp", "starts", "durations"])
            starts = self.vector(e["starts"])
            durations = self.integers(e["durations"], len(starts), True)
            return _op(
                "and",
                *[
                    _op("or",
                        _op("le", _op("add", starts[i], _lit(durations[i])), starts[j]),
                        _op("le", _op("add", starts[j], _lit(durations[j])), starts[i]))
                    for i in range(len(starts))
                    for j in range(i)
                    if durations[i] and durations[j]
                ],
            )
        if kind == "subcircuit":
            keys(e, ["cp", "successors", "allow_empty"])
            if type(e["allow_empty"]) is not bool:
                raise ModelError("subcircuit allow_empty must be Boolean")
            xs = self.vector(e["successors"])
            if not xs:
                return _bool(e["allow_empty"])
            n = len(xs)
            root, ranks = self.fresh(), self.fresh()
            anchor = {"var": root}

            def rank(index):
                return {"at": ranks, "indices": [index]}

            active = [_op("ne", x, _lit(i)) for i, x in enumerate(xs)]
            # A permutation has disjoint cycles. Strictly increasing ranks
            # break every active cycle except the one closing at the anchor.
            # Choose the anchor locally instead of forcing source vertex zero
            # into the tour. No witness escapes a negated constructor call.
            cycle = [
                _op("or", *[_op("and", a, _op("eq", anchor, _lit(i)))
                            for i, a in enumerate(active)]),
                _op("eq", rank(anchor), _lit(0)),
            ]
            clauses = [_op("all_different", *xs)]
            for i, x in enumerate(xs):
                clauses.extend([_int_sort_guard(x), _op("ge", x, _lit(0)),
                                _op("lt", x, _lit(n))])
                cycle.extend([
                    _op("ge", rank(_lit(i)), _lit(0)),
                    _op("lt", rank(_lit(i)), _lit(n)),
                    _op("implies", _op("and", active[i], _op("ne", x, anchor)),
                        _op("eq", rank(x), _op("add", rank(_lit(i)), _lit(1)))),
                ])
            witnessed = {"quantifier": "exists", "binders": [
                {"name": root, "sort": "Int"},
                {"name": ranks, "sort": {"Array": ["Int", "Int"]}},
            ], "body": _op("and", *cycle)}
            if e["allow_empty"]:
                witnessed = _op("or", _op("and", *[
                    _op("eq", x, _lit(i)) for i, x in enumerate(xs)]), witnessed)
            return _op("and", *clauses, witnessed)
        if kind in ["circuit", "regular"]:
            keys(
                e,
                ["cp", "successors"]
                if kind == "circuit"
                else ["cp", "items", "start", "finals", "transitions"],
            )
            xs = self.vector(e["successors"] if kind == "circuit" else e["items"])
            witness = self.fresh()

            def at(i):
                return {
                    "at": witness,
                    "indices": [i if isinstance(i, dict) else _lit(i)],
                }

            if kind == "circuit":
                keys(e, ["cp", "successors"])
                if not xs:
                    raise ModelError("circuit requires at least one vertex")
                n = len(xs)
                clauses = [_op("all_different", *xs), _op("eq", at(0), _lit(0))]
                for i, x in enumerate(xs):
                    clauses.extend(
                        [
                            _op("ge", x, _lit(0)),
                            _op("lt", x, _lit(n)),
                            _op("ge", at(i), _lit(0)),
                            _op("lt", at(i), _lit(n)),
                            _op(
                                "implies",
                                _op("ne", x, _lit(0)),
                                _op("eq", at(x), _op("add", at(i), _lit(1))),
                            ),
                        ]
                    )
            else:
                keys(e, ["cp", "items", "start", "finals", "transitions"])
                self.integers([e["start"]])
                finals = self.integers(e["finals"])
                if (
                    not isinstance(e["transitions"], list)
                    or len(e["transitions"]) > 10000
                ):
                    raise ModelError("invalid regular transitions")
                triples = [self.integers(t, 3) for t in e["transitions"]]
                clauses = [
                    _op("eq", at(0), _lit(e["start"])),
                    _op("or", *[_op("eq", at(len(xs)), _lit(f)) for f in finals]),
                ]
                if not triples:
                    # No transition relation otherwise mentions the word's
                    # items. Preserve their deep typing in pure JSON routes;
                    # direct native construction uses validation-only roots.
                    clauses.extend(_int_sort_guard(item) for item in xs)
                for i, x in enumerate(xs):
                    clauses.append(
                        _op(
                            "or",
                            *[
                                _op(
                                    "and",
                                    _op("eq", at(i), _lit(a)),
                                    _op("eq", x, _lit(b)),
                                    _op("eq", at(i + 1), _lit(c)),
                                )
                                for a, b, c in triples
                            ],
                        )
                    )
            return {
                "quantifier": "exists",
                "binders": [{"name": witness, "sort": {"Array": ["Int", "Int"]}}],
                "body": _op("and", *clauses),
            }
        raise ModelError("unknown CP constructor: " + str(kind))


def cp_validation_guards(expr, reserved=(), finite_shapes=None, *, erased_only=False):
    """Retain typed inputs that a pure CP expansion could otherwise erase.

    These expressions are tautologies for well-typed inputs, and callers use
    them only as the guard of an identity ITE. They are not source constraints.
    Public vector expansion remains structural: its empty result is still [].
    """
    kind = expr.get("cp")
    vector_fields = {
        "sum": ("items",), "minimum": ("items",), "maximum": ("items",),
        "all_different": ("items",), "all_different_except_0": ("items",),
        "among": ("items",), "count_true": ("items",), "at_most_one": ("items",),
        "global_cardinality": ("items",), "element": ("items",),
        "table": ("items",), "lex": ("left", "right"),
        "cumulative": ("starts", "durations", "demands"),
        "no_overlap": ("starts",), "circuit": ("successors",),
        "subcircuit": ("successors",),
        "regular": ("items",), "connected": ("nodes", "edges"),
        "dconnected": ("nodes", "edges"),
    }
    if not isinstance(kind, str):
        return []  # The normal constructor parser reports malformed CP calls.
    expander = None

    def structural_expander():
        nonlocal expander
        if expander is None:
            expander = _Expand(expr, reserved=reserved, finite_shapes=finite_shapes)
        return expander

    vectors = [expr[field] for field in vector_fields.get(kind, ()) if field in expr]
    if kind == "diffn":
        for field in ("positions", "sizes"):
            if isinstance(expr.get(field), list):
                vectors.extend(expr[field])
    guards = []
    for vector in vectors:
        if not isinstance(vector, dict) or vector.get("length") != 0:
            continue
        # This still checks closed fields, length and any declared finite rank.
        structural_expander().vector(vector, expand_items=False)
        probe = {"at": vector["array"],
                 "indices": [*vector.get("prefix", []), _lit(0)]}
        # SMT arrays are total, including declarations with an empty finite
        # observation shape. Selecting zero is a type probe, not a domain fact.
        guards.append(_op("eq", probe, probe))
    if kind == "element" and not erased_only:
        keys(expr, ["cp", "items", "index", "default"])
        guards.append(_int_sort_guard(expr["index"]))
    elif kind == "no_overlap" and not erased_only:
        keys(expr, ["cp", "starts", "durations"])
        parser = structural_expander()
        starts = parser.vector(expr["starts"], expand_items=False)
        parser.integers(expr["durations"], len(starts), True)
        guards.extend(_int_sort_guard(start) for start in starts)
    return guards


def expand_cp_model(model):
    """Return an independent base-HIR JSON model; preserve source annotations."""
    result = deepcopy(model)
    expander = _Expand(result)
    for section in ["constraints", "soft_constraints", "objectives"]:
        for entry in result.get(section, []):
            entry["expr"] = expander.expr(entry["expr"])
    if result.get("goal") is not None:
        result["goal"]["expr"] = expander.expr(result["goal"]["expr"])
    _check_expansion_size(result)
    return result


def expand_cp_expression(expr, reserved=(), finite_shapes=None):
    """Expand CP macros in one expression while avoiding existing names."""
    expanded = _Expand(expr, reserved=reserved, finite_shapes=finite_shapes).expr(deepcopy(expr))
    _check_expansion_size(expanded)
    return expanded


def expand_cp_vector(vector, reserved=(), finite_shapes=None):
    """Expand a vector descriptor to its explicit expression list."""
    expander = _Expand(vector, reserved=reserved, finite_shapes=finite_shapes)
    expanded = expander.vector(deepcopy(vector))
    _check_expansion_size(expanded)
    return expanded


def element_inputs(expr, reserved=(), finite_shapes=None):
    """Keep element operands unexpanded for one scoped native construction."""
    keys(expr, ["cp", "items", "index", "default"])
    parser = _Expand(expr, reserved=reserved, finite_shapes=finite_shapes)
    items = parser.vector(expr["items"], expand_items=False)
    _check_expansion_size(items)
    return items, expr["index"], expr["default"]


def no_overlap_inputs(expr, reserved=(), finite_shapes=None):
    """Retain every supplied start, including zero-duration tasks."""
    keys(expr, ["cp", "starts", "durations"])
    parser = _Expand(expr, reserved=reserved, finite_shapes=finite_shapes)
    starts = parser.vector(expr["starts"], expand_items=False)
    durations = parser.integers(expr["durations"], len(starts), True)
    _check_expansion_size(starts)
    return starts, durations


def extrema_inputs(expr, reserved=(), finite_shapes=None):
    """Validate a nonempty vector while retaining its native-build operands."""
    keys(expr, ["cp", "items"])
    expander = _Expand(expr, reserved=reserved, finite_shapes=finite_shapes)
    # Nested constructors must also reach HirBuilder without JSON duplication.
    items = expander.vector(expr["items"], expand_items=False)
    if not items:
        raise ModelError("minimum/maximum of an empty vector is undefined")
    _check_expansion_size(items)
    return items


def cumulative_inputs(expr, reserved=(), finite_shapes=None):
    """Retain tasks for native scheduling within the HIR construction budget."""
    # Bound supplied JSON, not a manufactured JSON copy of native operands.
    # Descriptor selects and nested CP calls are checked once by HirBuilder;
    # its native expression budget also applies to the constructed terms.
    _check_expansion_size(expr)
    return _Expand(expr, reserved=reserved, finite_shapes=finite_shapes).cumulative_inputs(
        expr, expand_items=False, max_length=MAX_EXPANDED_NODES,
    )


def diffn_inputs(expr, reserved=(), finite_shapes=None):
    """Validate box matrices without constructing a quadratic JSON formula."""
    result = _Expand(expr, reserved=reserved, finite_shapes=finite_shapes).diffn_inputs(expr)
    _check_expansion_size(list(result))
    return result


def regular_inputs(expr, reserved=(), finite_shapes=None):
    """Validate an automaton without replicating each input per transition."""
    result = _Expand(expr, reserved=reserved, finite_shapes=finite_shapes).regular_inputs(expr)
    _check_expansion_size(list(result))
    return result


def cardinality_inputs(expr, reserved=(), finite_shapes=None):
    """Validate finite counting inputs without duplicating their expression trees."""
    result = _Expand(expr, reserved=reserved, finite_shapes=finite_shapes).cardinality_inputs(expr)
    _check_expansion_size(list(result))
    return result


def build_cp_hir(model, source):
    """Invoke the HIR builder, retaining supported native global relations."""
    return build_hir(model, source)


class CpProvider:
    """Supply the CP catalog while retaining compact native HIR constructors."""

    def __init__(self, provider):
        self.provider = provider
        self.last_cp_model = None

    def __call__(self, request):
        if request.get("language") != "hir":
            raise ModelError("CP constructor provider requires language=hir")
        request = deepcopy(request)
        request["context"]["cp_constructor_api"] = json.dumps(
            cp_api(), separators=(",", ":")
        )
        request[
            "instruction"
        ] += " The additional cp_constructor_api expressions are permitted and will be validated by the standard HIR builder. Prefer these compact constructors for global constraints, extrema, and indexed selection; do not expand them into repeated JSON subexpressions."
        self.last_cp_model = deepcopy(self.provider(request))
        # Native constructor paths compile shared operands once. Eager JSON
        # expansion here defeats that sharing before the builder can see it.
        # Retain a separate snapshot because callers may normalize the result.
        return deepcopy(self.last_cp_model)
