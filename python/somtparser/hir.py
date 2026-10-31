"""Typed, non-executable JSON construction API for the native C++ HIR.

The API constructs HIR nodes directly. It never evaluates Python or parses SMT.
Open sorts remain open; finite folds require explicit half-open integer ranges.
"""
from . import _somtparser as native
from ._nl_model import (ModelError, keys, name, number,
                        IDENTIFIER_RULES, TERM_NAMESPACE_RULES)
from ._hir_modeling import MODELING_GUIDANCE, modeling_patterns
from itertools import product
from math import prod
import hashlib
import json
import re

SCHEMA = "somt-hir-model-v1"
ROUNDING_MODES = frozenset(["RNE", "RNA", "RTP", "RTN", "RTZ"])
# Accept conventional mathematical spellings often emitted by models and
# external HIR producers. These normalize to canonical names before checking.
OPERATOR_ALIASES = {
    "=": "eq", "!=": "ne", "≠": "ne",
    "<": "lt", "<=": "le", "≤": "le",
    ">": "gt", ">=": "ge", "≥": "ge",
    "+": "add", "-": "sub", "*": "mul", "×": "mul",
    "=>": "implies", "&&": "and", "||": "or",
}
OPERATIONS = {
    "not": (1, 1),
    "implies": (2, 2),
    "xor": (2, 10000),
    "and": (0, 10000),
    "or": (0, 10000),
    "eq": (2, 10000),
    "ne": (2, 2),
    "le": (2, 10000),
    "lt": (2, 10000),
    "ge": (2, 10000),
    "gt": (2, 10000),
    "add": (0, 10000),
    "sub": (2, 2),
    "mul": (2, 10000),
    "div": (2, 2),
    "div_euclid": (2, 2),
    "div_trunc": (2, 2),
    "div_floor": (2, 2),
    "mod_euclid": (2, 2),
    "mod_trunc": (2, 2),
    "mod_floor": (2, 2),
    "ite": (3, 3),
    "select": (2, 2),
    "array.map.and": (2, 10000),
    "array.map.or": (2, 10000),
    "array.map.not": (1, 1),
    "store": (3, 3),
    "distinct": (0, 10000),
    "all_different": (0, 10000),
    "all_different_except_0": (0, 10000),
    "abs": (1, 1),
    "connected": (2, 100000),
    "dconnected": (2, 100000),
    "count": (0, 10000),
    # Bit-vectors: n-ary where SMT-LIB is associative, binary elsewhere.
    "bvnot": (1, 1),
    "bvneg": (1, 1),
    "bvand": (2, 10000),
    "bvor": (2, 10000),
    "bvxor": (2, 10000),
    "bvadd": (2, 10000),
    "bvmul": (2, 10000),
    "bvudiv": (2, 2),
    "bvurem": (2, 2),
    "bvshl": (2, 2),
    "bvlshr": (2, 2),
    "bvashr": (2, 2),
    "bvult": (2, 2),
    "bvule": (2, 2),
    "bvugt": (2, 2),
    "bvuge": (2, 2),
    "bvslt": (2, 2),
    "bvsle": (2, 2),
    "bvsgt": (2, 2),
    "bvsge": (2, 2),
    "concat": (2, 10000),
    # Floating point: comparisons and the unrounded pair take only
    # FloatingPoint operands; the arithmetic group is (rounding mode, x, y).
    "fp.eq": (2, 2),
    "fp.lt": (2, 2),
    "fp.leq": (2, 2),
    "fp.gt": (2, 2),
    "fp.geq": (2, 2),
    "fp.add": (3, 3),
    "fp.sub": (3, 3),
    "fp.mul": (3, 3),
    "fp.div": (3, 3),
    "fp.abs": (1, 1),
    "fp.neg": (1, 1),
    # Strings, minus the regular-expression fragment.
    "str.++": (2, 10000),
    "str.len": (1, 1),
    "str.at": (2, 2),
    "str.contains": (2, 2),
    "str.prefixof": (2, 2),
    "str.suffixof": (2, 2),
    "str.indexof": (3, 3),
    "str.substr": (3, 3),
    "str.replace": (3, 3),
    "str.to_int": (1, 1),
    "str.from_int": (1, 1),
    "str.to_re": (1, 1),
    "str.in_re": (2, 2),
    "re.++": (2, 10000),
    "re.union": (2, 10000),
    "re.inter": (2, 10000),
    "re.diff": (2, 2),
    "re.*": (1, 1),
    "re.+": (1, 1),
    "re.opt": (1, 1),
    "re.comp": (1, 1),
    "re.range": (2, 2),
    "set.singleton": (1, 1),
    "set.union": (2, 10000),
    "set.inter": (2, 10000),
    "set.minus": (2, 2),
    "set.insert": (2, 10000),
    "set.member": (2, 2),
    "set.subset": (2, 2),
    "set.card": (1, 1),
    "set.complement": (1, 1),
}

# Indexed operators, built through the dedicated checked HIR builders rather
# than the op table: name -> (index count, argument count). Width relations
# between the indices and the operand sorts are enforced by the native HIR
# type checker at translate time, not here.
INDEXED_OPERATIONS = {
    "extract": (2, 1),
    "zero_extend": (1, 1),
    "sign_extend": (1, 1),
    "rotate_left": (1, 1),
    "rotate_right": (1, 1),
    "repeat": (1, 1),
    "int2bv": (1, 1),
    "divisible": (1, 1),
    "fp.to_sbv": (1, 2),
    "fp.to_ubv": (1, 2),
    "to_fp": (2, 2),
    "to_fp_unsigned": (2, 2),
    "ieee_bv_to_fp": (2, 1),
    "re.loop": (2, 1),
    "tuple.select": (1, 1),
    "tuple.update": (1, 2),
    "tuple.project": (None, 1),
}

_BV_OPERATIONS = frozenset(
    [
        "bvnot", "bvneg", "bvand", "bvor", "bvxor", "bvadd", "bvmul",
        "bvudiv", "bvurem", "bvshl", "bvlshr", "bvashr",
        "bvult", "bvule", "bvugt", "bvuge",
        "bvslt", "bvsle", "bvsgt", "bvsge", "concat",
    ]
)
_FP_VALUE_OPERATIONS = frozenset(
    ["fp.eq", "fp.lt", "fp.leq", "fp.gt", "fp.geq", "fp.abs", "fp.neg"]
)
_FP_ROUNDED_OPERATIONS = frozenset(["fp.add", "fp.sub", "fp.mul", "fp.div"])
_STRING_SIGNATURES = {
    "str.++": ["String"],  # variadic
    "str.len": ["String"],
    "str.at": ["String", "Int"],
    "str.contains": ["String", "String"],
    "str.prefixof": ["String", "String"],
    "str.suffixof": ["String", "String"],
    "str.indexof": ["String", "String", "Int"],
    "str.substr": ["String", "Int", "Int"],
    "str.replace": ["String", "String", "String"],
    "str.to_int": ["String"],
    "str.from_int": ["Int"],
}
_REGEX_SIGNATURES = {
    "str.to_re": ["String"],
    "str.in_re": ["String", "RegLan"],
    "re.++": ["RegLan"],  # variadic
    "re.union": ["RegLan"],  # variadic
    "re.inter": ["RegLan"],  # variadic
    "re.diff": ["RegLan", "RegLan"],
    "re.*": ["RegLan"],
    "re.+": ["RegLan"],
    "re.opt": ["RegLan"],
    "re.comp": ["RegLan"],
    "re.range": ["String", "String"],
}

_FP_SPECIALS = frozenset(["+oo", "-oo", "+zero", "-zero", "NaN"])
_FP_LITERAL_HINT = (
    "floating-point literals must be decimal strings, one of "
    "+oo/-oo/+zero/-zero/NaN, or ['#bS', '#bE', '#bM'] triples"
)


def _bitvec_literal_width(value):
    """The width a '#b…'/'#x…' literal names; every other spelling is refused."""
    if isinstance(value, str) and len(value) > 2:
        digits = value[2:]
        if value.startswith("#b") and re.fullmatch(r"[01]+", digits):
            return len(digits)
        if value.startswith("#x") and re.fullmatch(r"[0-9a-fA-F]+", digits):
            return 4 * len(digits)
    raise ModelError("bit-vector literals must be '#b...' or '#x...' text")


def _float_literal_text(value, eb, sb):
    """SMT-LIB text for a FloatingPoint literal of format (eb, sb)."""
    if isinstance(value, str):
        if value in _FP_SPECIALS:
            return f"(_ {value} {eb} {sb})"
        if re.fullmatch(r"[+-]?\d+(\.\d+)?", value):
            return value
        raise ModelError(_FP_LITERAL_HINT)
    if isinstance(value, list) and len(value) == 3:
        for part, want in zip(value, [1, eb, sb - 1]):
            if (
                not isinstance(part, str)
                or not re.fullmatch(r"#b[01]+", part)
                or len(part) - 2 != want
            ):
                raise ModelError(
                    f"an (fp #bS #bE #bM) literal needs 1, {eb} and {sb - 1} "
                    "bits for its fields at this format"
                )
        return f"(fp {value[0]} {value[1]} {value[2]})"
    raise ModelError(_FP_LITERAL_HINT)


def hir_api():
    """Machine-readable constructor catalog included in provider requests."""
    # The import stays local because hir_cp uses build_hir for its legacy
    # build_cp_hir convenience entry point.
    from .hir_cp import cp_api

    return {
        "schema": SCHEMA,
        "cp_constructors": cp_api(),
        "soft_constraints": {
            "item": {"expr": "Bool expression", "weight": "positive ASCII integer string",
                     "group": "SMT symbol or empty string for the default group", "span": [0, 1]},
            "semantics": (
                "An optional ordered list of preferences, each charged its exact weight when false. "
                "Duplicates contribute independently; a conjunction is one preference, not separate penalties. "
                "Group costs follow first appearance, then explicit objectives follow their list order. "
                "Use decision='optimization'; more than one effective objective requires "
                "objective_order='lexicographic'. Group g and |g| denote the same group."
            ),
        },
        "interpretation_metadata": {
            "interpretation_notes": "Optional string array explaining the encoded interpretation; adds no constraints and cannot replace source requirements.",
            "assumptions": "Explicitly applied modeling conventions, retained for review.",
            "unresolved": "Competing source readings; a nonempty array always prevents compilation. Never silently move its entries to notes or assumptions.",
        },
        "sorts": [
            "Bool",
            "Int",
            "Real",
            "String",
            "RegLan",
            {"Set": "element sort"},
            {"BitVec": "positive width in bits"},
            {
                "FloatingPoint": [
                    "positive exponent bits",
                    "positive significand bits, sign included",
                ]
            },
            {"Array": ["index sort", "element sort"]},
            {"Tuple": ["field sort", "..."]},
            {"Datatype": {"name": "declared datatype", "args": ["sort", "..."]}},
            {"Parameter": "datatype-local type parameter"},
            {"Uninterpreted": "name"},
        ],
        "constructors": {
            "variable": {"var": "declared_name"},
            "tuple": {"tuple": ["nonempty list of field expressions"]},
            "tuple_unit": {"tuple_unit": True},
            "datatype_constructor": {
                "dt_constructor": "declared constructor",
                "sort": "explicit result datatype instance",
                "args": ["field expression", "..."],
            },
            "datatype_selector": {
                "dt_selector": "declared selector",
                "sort": "explicit result sort checked against declaration",
                "value": "datatype expression",
            },
            "datatype_tester": {"dt_tester": "constructor", "value": "datatype expression"},
            "datatype_declaration": {
                "name": "datatype name",
                "params": ["type parameter", "..."],
                "constructors": [
                    {"name": "constructor", "fields": [{"name": "selector", "sort": "sort"}]}
                ],
                "coinductive": "optional Boolean, default false",
            },
            "literal": {
                "literal": (
                    "exact decimal/rational string for Real; int for Int; "
                    "bool for Bool; JSON string for String; '#b...'/'#x...' "
                    "bit text whose width equals the declared BitVec width; "
                    "RegLan literals are re.none, re.all or re.allchar; Set "
                    "literals are set.empty or set.universe with an explicit "
                    "Set sort; for "
                    "FloatingPoint a decimal string, one of "
                    "+oo/-oo/+zero/-zero/NaN, or ['#bS', '#bE', '#bM'] with "
                    "1/exponent/(significand-1) bits"
                ),
                "sort": "Int|Real|Bool|String|RegLan|{'Set': element sort}|{'BitVec': width}|{'FloatingPoint': [eb, sb]}",
            },
            "operator": {
                "op": "name from operations or operator_aliases",
                "args": ["expression"],
            },
            "indexed_operator": {
                "op_indexed": {
                    "op": "name from indexed_operations",
                    "indices": ["nonnegative integer"],
                    "args": ["expression"],
                }
            },
            "rounding_mode": {"rm": "RNE|RNA|RTP|RTN|RTZ"},
            "application": {"apply": "declared_function", "args": ["expression"]},
            "function": {
                "declaration": {"name": "f", "arguments": ["sort", "..."], "result": "sort"},
                "definition": {
                    "name": "f", "arguments": ["sort", "..."], "result": "sort",
                    "binders": [{"name": "x", "sort": "sort"}],
                    "body": "expression checked against result sort",
                    "span": "[start, end] in the exact source text",
                },
                "rules": "definitions require binders, body, and source span; binder count and sorts match arguments; bodies are exact and non-recursive",
            },
            "array_access": {"at": "declared_or_lexically_bound_array", "indices": ["expression matching each successive Array index sort"]},
            "constant_array": {
                "const_array": {"index_sort": "sort", "value": "expression"},
            },
            "data_lookup": {
                "data": "name in model.data",
                "indices": ["Int expression"],
                "default": "explicit default expression outside table",
            },
            "quantifier": {
                "quantifier": "forall|exists|exists_unique",
                "binders": [{"name": "x", "sort": "sort"}],
                "body": "Bool expression",
            },
            "finite_fold": {
                "fold": "sum|forall|exists",
                "var": "i",
                "range": [0, 10],
                "body": "expression (range excludes 10)",
            },
        },
        "operator_aliases": dict(OPERATOR_ALIASES),
        "operations": {k: list(v) for k, v in OPERATIONS.items()},
        "indexed_operations": {k: list(v) for k, v in INDEXED_OPERATIONS.items()},
        "modeling_patterns": modeling_patterns(),
        "semantics": {
            "source_modeling": MODELING_GUIDANCE,
            "identifiers": IDENTIFIER_RULES,
            "term_namespace": TERM_NAMESPACE_RULES,
            "arithmetic": "exact Int/Real; no implicit numeric domain or integrality. A shape [1] declaration remains an array; omit shape or use [] for a scalar, and use explicit at/select to read an array element",
            "Boolean_indicators": "ite conditions and logical operators require Bool. An Int constrained to 0/1 remains Int: compare it explicitly with the intended value. Convert Bool to an Int indicator explicitly with ite(condition, 1, 0), or use count for a number of true conditions",
            "absolute_value": "abs accepts one exact Int or Real expression and lowers to an exact conditional expression",
            "division": "division conventions are explicit. Denominators must be nonzero numeric literals or numeric variables proved nonzero by local comparison guards in implies, ite, and/or contexts. Guard facts retain lexical scope; arbitrary symbolic or unguarded zero-possible denominators remain unsupported. No global nonzero constraint is added",
            "arrays": "total SMT arrays; finite valid-index and element domains must be constrained explicitly",
            "quantifiers": "forall/exists over declared sorts; never assume a finite universe. exists_unique means exactly one simultaneous tuple of all binders satisfies body, not one value independently per binder; lowers exactly to exists tuple (body and forall fresh_tuple (body[fresh_tuple] implies fresh_tuple=tuple)). No finite domain, existence, or uniqueness assumption is added outside this constructor",
            "count": "sum of Boolean indicators",
            "folds": "explicit finite half-open ranges within the caller construction policy (default 10000 elements); empty sum=0, forall=true, exists=false. Boolean folds with more than 8 elements use exact native Int quantifiers guarded by the same bounds; sums and smaller folds are expanded",
            "all_different": "native HIR global over scalar Int arguments or whole declared finite Int arrays with an explicit shape; arrays flatten in row-major order over exactly their zero-based shape. Unshaped total arrays have no inferred finite extent; bound variables shadowing array names are not expanded. Decomposed by selected profile",
            "all_different_except_0": "native HIR global over exact Int terms, a whole declared finite Int array, or an array with explicit Int half-open bounds [lo, hi); zero entries are ignored and repeated nonzero values are forbidden. Whole shaped arrays flatten in row-major order; indexed arrays retain the native global until the selected profile decomposes it",
            "connected": "exact undirected connectivity global over fixed zero-based endpoints and Bool node/edge selection vectors; selected edges require selected endpoints and at least one selected node is required",
            "dconnected": "exact directed root-reachability global over fixed zero-based endpoints and Bool node/edge selection vectors; some selected root must reach every selected node through selected edges; selected edges require selected endpoints and at least one selected node is required",
            "shape": "optional declaration shape [n,m,...] wraps the declared sort in zero-based nested arrays; [] adds no axes and is equivalent to omitted shape, whereas [0] declares an empty array; lower/upper apply to each in-shape element",
            "data": "optional model.data maps names to exact int/bool/Real-string scalars or rectangular nested lists; lookup checks each zero-based axis and returns the explicit default outside the table. Immutable table values are shared; defaults retain their local binding",
            "bitvectors": "machine-width bit-vectors; arithmetic wraps modulo 2^width; signed and unsigned orderings and divisions are distinct operators",
            "floating_point": "IEEE 754 semantics per SMT-LIB; arithmetic takes an explicit rounding mode; fp.eq is IEEE equality (NaN unequal to itself), distinct from structural =",
            "tuples": "heterogeneous ordered product sorts; Tuple [] is UnitTuple; tuple.project preserves requested field order and permits repeated or zero indices",
            "strings": "SMT-LIB sequences of characters with Int indices; out-of-range at/substr yield the empty string and indexof yields -1",
            "regular_expressions": "SMT-LIB UnicodeStrings RegLan semantics (https://smt-lib.org/theories-UnicodeStrings.shtml); re.range endpoints may be symbolic and non-singleton/reversed endpoints denote the empty language; re.loop uses inclusive uint32 bounds and reversed bounds denote re.none",
            "sets": "cvc5 finite-set theory (https://cvc5.github.io/docs/cvc5-1.3.1/theories/sets-and-relations.html); union/intersection are n-ary over one exact Set sort; minus/subset are binary; member takes element then set; insert takes elements then set; card returns Int; complement is relative to set.universe. The input-active finite universe is not all values of possibly infinite element sorts, and no finite element domain is inferred. Extended Set solving requires a compatible backend configured for sets extensions (cvc5 --sets-exp); generic SMT export does not configure that option automatically, and this syntax is not a portable Z3 Set API. The finite-set guarantee here is quantifier-free: cvc5 quantified sets may be infinite, so quantified formulas are not yet certified under the HIR finite-set contract",
            "scope": "a successful compile still establishes nothing about natural-language correctness",
        },
    }


def hir_schema():
    def ref(name):
        return {"$ref": "#/$defs/" + name}

    def exact_object(required, properties):
        return {"type": "object", "required": list(required),
                "properties": properties, "additionalProperties": False}

    def array(items, minimum=None, maximum=None):
        result = {"type": "array", "items": items}
        if minimum is not None:
            result["minItems"] = minimum
        if maximum is not None:
            result["maxItems"] = maximum
        return result

    identifier_schema = {"type": "string", "description": IDENTIFIER_RULES + " " + TERM_NAMESPACE_RULES}
    identifier = ref("identifier")
    sort_schema = {"anyOf": [
        {"enum": ["Bool", "Int", "Real", "String", "RegLan"]},
        exact_object(["Set"], {"Set": ref("sort")}),
        exact_object(["BitVec"], {"BitVec": {"type": "integer", "minimum": 1}}),
        exact_object(["FloatingPoint"], {"FloatingPoint": array(
            {"type": "integer", "minimum": 1}, 2, 2)}),
        exact_object(["Array"], {"Array": array(ref("sort"), 2, 2)}),
        exact_object(["Tuple"], {"Tuple": array(ref("sort"))}),
        exact_object(["Parameter"], {"Parameter": {"type": "string"}}),
        exact_object(["Uninterpreted"], {"Uninterpreted": {"type": "string"}}),
        exact_object(["Datatype"], {"Datatype": {"oneOf": [
            {"type": "string"},
            exact_object(["name", "args"], {
                "name": identifier, "args": array(ref("sort"))}),
        ]}}),
    ]}
    expression = ref("expression")
    span_schema = array({"type": "integer", "minimum": 0}, 2, 2)
    binder_schema = exact_object(["name", "sort"], {
        "name": identifier, "sort": ref("sort")})
    args_schema = array(expression)
    expression_variants = []

    def add_variant(required, properties):
        expression_variants.append(exact_object(required, properties))

    # The same exact spelling is used for Real bounds and literal operands.
    # The final lookahead also rejects a trailing newline, unlike `$` alone.
    exact_real = {"type": "string", "maxLength": 512,
                  "pattern": r"^[+-]?(?:\d+(?:\.\d+)?|\d+/[1-9]\d*)(?![\s\S])"}
    add_variant(["var"], {"var": identifier})
    add_variant(["literal", "sort"], {
        "literal": {"oneOf": [
            {"type": "boolean"}, {"type": "integer"}, {"type": "string"},
            array({"type": "string"}),
        ]},
        "sort": ref("sort"),
    })
    # Numeric literals name exact values, never declared variables. Make this
    # visible in the provider schema as well as the authoritative HIR builder.
    expression_variants[-1]["allOf"] = [{
        "if": {"properties": {"sort": {"const": name}}},
        "then": {"properties": {"literal": value_schema}},
    } for name, value_schema in (
        ("Bool", {"type": "boolean"}),
        ("Int", {"type": "integer"}),
        ("Real", exact_real),
    )]
    add_variant(["rm"], {"rm": {"enum": sorted(ROUNDING_MODES)}})
    add_variant(["tuple_unit"], {"tuple_unit": {"const": True}})
    add_variant(["tuple"], {"tuple": array(expression, 1)})
    add_variant(["const_array"], {"const_array": exact_object(
        ["index_sort", "value"], {"index_sort": ref("sort"), "value": expression})})
    add_variant(["at", "indices"], {
        "at": identifier, "indices": array(expression, 1)})
    add_variant(["data", "indices", "default"], {
        "data": {"type": "string"}, "indices": array(expression), "default": expression})
    add_variant(["apply", "args"], {"apply": identifier, "args": args_schema})
    add_variant(["fold", "var", "range", "body"], {
        "fold": {"enum": ["sum", "forall", "exists"]},
        "var": identifier,
        "range": array({"type": "integer"}, 2, 2),
        "body": expression,
    })
    add_variant(["quantifier", "binders", "body"], {
        "quantifier": {"enum": ["forall", "exists", "exists_unique"]},
        "binders": array(binder_schema, 1), "body": expression,
    })
    add_variant(["dt_constructor", "sort", "args"], {
        "dt_constructor": {"type": "string"}, "sort": ref("sort"),
        "args": args_schema,
    })
    add_variant(["dt_selector", "sort", "value"], {
        "dt_selector": {"type": "string"}, "sort": ref("sort"), "value": expression,
    })
    add_variant(["dt_tester", "value"], {
        "dt_tester": {"type": "string"}, "value": expression,
    })

    vector_descriptor_schema = exact_object(["array", "length"], {
        "array": {"type": "string"},
        "length": {"type": "integer", "minimum": 0, "maximum": 1000},
        "prefix": array(expression),
    })
    vector_descriptor = ref("cp_vector_descriptor")
    cp_vector_schema = {"oneOf": [array(expression, 0, 1000), vector_descriptor]}
    cp_vector = ref("cp_vector")
    cumulative_vector_descriptor_schema = exact_object(["array", "length"], {
        "array": {"type": "string"},
        "length": {"type": "integer", "minimum": 0, "maximum": 100000},
        "prefix": array(expression),
    })
    cumulative_vector_descriptor = ref("cumulative_vector_descriptor")
    cumulative_vector = {"oneOf": [
        array(expression, 0, 100000), cumulative_vector_descriptor,
    ]}
    int_value = {"type": "integer"}
    nonnegative_int = {"type": "integer", "minimum": 0}
    int_list = array(int_value, 0, 10000)
    nonnegative_int_list = array(nonnegative_int, 0, 10000)
    int_or_expr = {"oneOf": [int_value, expression]}
    int_or_expr_list = array(int_or_expr, 0, 1000)
    nonnegative_int_or_expr = {"oneOf": [nonnegative_int, expression]}
    cumulative_int_or_expr_list = array(nonnegative_int_or_expr, 0, 100000)
    cp_fields = {
        "sum": {"items": cp_vector},
        "minimum": {"items": cp_vector},
        "maximum": {"items": cp_vector},
        "all_different": {"items": cp_vector},
        "all_different_except_0": {"items": cp_vector},
        "connected": {
            "from": {"type": "array", "items": {"type": "integer"}},
            "to": {"type": "array", "items": {"type": "integer"}},
            "nodes": cp_vector,
            "edges": cp_vector,
        },
        "dconnected": {
            "from": {"type": "array", "items": {"type": "integer"}},
            "to": {"type": "array", "items": {"type": "integer"}},
            "nodes": cp_vector,
            "edges": cp_vector,
        },
        "weighted_count": {"items": cp_vector, "weights": cp_vector,
                           "sort": {"enum": ["Int", "Real"]}},
        "count_true": {"items": cp_vector},
        "at_most_one": {"items": cp_vector},
        "abs": {"value": expression},
        "among": {"items": cp_vector, "values": array(int_value, 0, 1000)},
        "global_cardinality": {
            "items": cp_vector, "values": array(int_value, 0, 1000),
            "counts": array(expression, 0, 1000), "closed": {"type": "boolean"},
        },
        "element": {"items": cp_vector, "index": expression, "default": expression},
        "table": {"items": cp_vector,
                  "tuples": array(int_list, 0, 10000),
                  "positive": {"type": "boolean"}},
        "lex": {"left": cp_vector, "right": cp_vector, "strict": {"type": "boolean"}},
        "cumulative": {
            "starts": cumulative_vector,
            "durations": {"oneOf": [cumulative_int_or_expr_list, cumulative_vector_descriptor]},
            "demands": {"oneOf": [cumulative_int_or_expr_list, cumulative_vector_descriptor]},
            "capacity": expression,
        },
        "diffn": {
            "dimensions": {"type": "integer", "minimum": 1, "maximum": 1000},
            "positions": array({"anyOf": [cp_vector, int_or_expr_list]}, 0, 1000),
            "sizes": array({"anyOf": [cp_vector, int_or_expr_list]}, 0, 1000),
            "nonstrict": {"type": "boolean"},
        },
        "no_overlap": {"starts": cp_vector, "durations": nonnegative_int_list},
        "circuit": {"successors": cp_vector},
        "subcircuit": {"successors": cp_vector, "allow_empty": {"type": "boolean"}},
        "regular": {
            "items": cp_vector, "start": int_value, "finals": int_list,
            "transitions": array(array(int_value, 3, 3), 0, 10000),
        },
    }
    operation_schema = exact_object(["op", "args"], {
        "op": {"enum": list(dict.fromkeys([*OPERATIONS, *OPERATOR_ALIASES]))},
        "args": array(expression, 0, max(bounds[1] for bounds in OPERATIONS.values())),
    })
    # Equal arity rules can share a condition; every operator and alias stays
    # in the catalog, and the accepted argument intervals stay unchanged.
    arity_groups = {}
    for op, bounds in {
        **OPERATIONS,
        **{alias: OPERATIONS[canonical]
           for alias, canonical in OPERATOR_ALIASES.items()},
    }.items():
        arity_groups.setdefault(bounds, []).append(op)
    operation_schema["allOf"] = [
        {
            "if": {"required": ["op"], "properties": {"op": {"enum": operators}}},
            "then": {"properties": {"args": {
                "minItems": minimum, "maxItems": maximum,
            }}},
        }
        for (minimum, maximum), operators in arity_groups.items()
    ]

    indexed_schema = exact_object(["op_indexed"], {
        "op_indexed": exact_object(
            ["op", "indices", "args"], {
                "op": {"enum": list(INDEXED_OPERATIONS)},
                "indices": array({"type": "integer", "minimum": 0}, 0, 10000),
                "args": array(expression, 0, 10000),
            }),
    })
    indexed_all_of = []
    indexed_groups = {}
    for op, counts in INDEXED_OPERATIONS.items():
        indexed_groups.setdefault(counts, []).append(op)
    for (index_count, arg_count), operators in indexed_groups.items():
        indexed_all_of.append({
            "if": {
                "required": ["op_indexed"],
                "properties": {"op_indexed": {
                    "required": ["op"], "properties": {"op": {"enum": operators}},
                }},
            },
            "then": {"properties": {"op_indexed": {
                "properties": {
                    "indices": {
                        "minItems": 0 if index_count is None else index_count,
                        "maxItems": 10000 if index_count is None else index_count,
                    },
                    "args": {"minItems": arg_count, "maxItems": arg_count},
                },
            }}},
        })
    indexed_schema["allOf"] = indexed_all_of

    cp_properties = {"cp": {"enum": list(cp_fields)}}
    for fields in cp_fields.values():
        # Shared field names can have different types across CP constructors.
        # Each kind-specific branch below supplies the actual field schema.
        cp_properties.update({field: {} for field in fields})
    cp_string_schema = {
        "type": "object", "required": ["cp"], "properties": cp_properties,
        "additionalProperties": False,
        "allOf": [
            {
                "if": {"required": ["cp"], "properties": {"cp": {"const": kind}}},
                "then": exact_object(["cp", *fields], {"cp": {"const": kind}, **fields}),
            }
            for kind, fields in cp_fields.items()
        ],
    }
    cp_schema = {"oneOf": [
        cp_string_schema,
        exact_object(["cp"], {
            "cp": exact_object(["abs"], {"abs": expression}),
        }),
    ]}
    cp_operator_schema = {
        "oneOf": [
            exact_object(
                ["op", *fields],
                {"op": {"const": kind}, **fields},
            )
            for kind, fields in cp_fields.items()
        ]
    }

    expression_markers = list(dict.fromkeys(
        branch["required"][0] for branch in expression_variants
    )) + ["op", "op_indexed", "cp"]
    expression_checks = []
    for branch in expression_variants:
        marker = branch["required"][0]
        condition = {"required": [marker]}
        # The variable constructor is the only constructor whose marker is
        # intentionally reused as a field in another constructor. Match the
        # builder's fold-before-variable dispatch: a fold node also has `var`.
        if marker == "var":
            condition["not"] = {"required": ["fold"]}
        expression_checks.append({"if": condition, "then": branch})
    expression_checks.extend([
        {"if": {"required": ["op"]}, "then": {"oneOf": [
            operation_schema, cp_operator_schema,
        ]}},
        {"if": {"required": ["op_indexed"]}, "then": indexed_schema},
        {"if": {"required": ["cp"]}, "then": cp_schema},
    ])
    expression_schema = {
        "type": "object",
        "anyOf": [{"required": [marker]} for marker in expression_markers],
        "allOf": expression_checks,
    }

    datatype_constructor = exact_object(["name", "fields"], {
        "name": identifier,
        "fields": array(exact_object(["name", "sort"], {
            "name": identifier, "sort": ref("sort")}), 0),
    })
    datatype_decl = exact_object(["name", "constructors"], {
        "name": identifier,
        "params": array({"type": "string"}),
        "constructors": array(datatype_constructor, 1),
        "coinductive": {"type": "boolean"},
    })
    source_expression = exact_object(["expr", "span"], {
        "expr": expression, "span": span_schema,
    })
    soft_constraint = exact_object(["expr", "weight", "group", "span"], {
        "expr": expression, "span": span_schema,
        "weight": {"type": "string", "pattern": r"^(?=[0-9]*[1-9])[0-9]+(?![\s\S])"},
        "group": {"type": "string"},
    })
    objective = exact_object(["sense", "expr", "span"], {
        "sense": {"enum": ["minimize", "maximize"]},
        "expr": expression, "span": span_schema,
    })
    function = {
        "type": "object",
        "required": ["name", "arguments", "result"],
        "properties": {
            "name": identifier,
            "arguments": array(ref("sort")),
            "result": ref("sort"),
            "binders": array(binder_schema),
            "body": expression,
            "span": span_schema,
        },
        "additionalProperties": False,
        "oneOf": [
            {"not": {"anyOf": [
                {"required": ["binders"]}, {"required": ["body"]},
                {"required": ["span"]},
            ]}},
            {"required": ["binders", "body", "span"]},
        ],
    }
    declaration = exact_object(["name", "sort"], {
        "name": identifier, "sort": ref("sort"),
        "lower": {}, "upper": {},
        "shape": array({"type": "integer", "minimum": 0}, 0, 8),
    })
    declaration["allOf"] = [{
        "if": {"properties": {"sort": {"const": "Int"}}},
        "then": {"properties": {
            field: {"type": ["integer", "null"]} for field in ("lower", "upper")}},
        "else": {
            "if": {"properties": {"sort": {"const": "Real"}}},
            "then": {"properties": {
                field: {"anyOf": [{"type": "null"}, exact_real]}
                for field in ("lower", "upper")}},
            "else": {"properties": {
                field: {"type": "null"} for field in ("lower", "upper")}},
        },
    }]

    return {
        "$comment": (
            "This schema validates constructor shape, closed field sets and catalogued arities. "
            "build_hir remains authoritative for declaration/function resolution, identifier "
            "and sort validity, type/sort compatibility, array rank and bounds, fold interval "
            "width, source-span bounds, cross-field cardinalities, CP vector shapes and budgets, "
            "datatype scope/inhabitation, definedness, and native semantic validity."
        ),
        "$defs": {
            "sort": sort_schema,
            "expression": expression_schema,
            "identifier": identifier_schema,
            "cp_vector_descriptor": vector_descriptor_schema,
            "cumulative_vector_descriptor": cumulative_vector_descriptor_schema,
            "cp_vector": cp_vector_schema,
        },
        "type": "object",
        "required": [
            "schema", "language", "decision", "declarations", "functions",
            "constraints", "objectives", "objective_order", "goal",
            "assumptions", "unresolved",
        ],
        "properties": {
            "schema": {"const": SCHEMA},
            "language": {"const": "hir"},
            "decision": {"enum": ["satisfiability", "optimization", "validity"]},
            "declarations": {
                "type": "array",
                "items": declaration,
            },
            "functions": {"type": "array", "items": function},
            "constraints": {"type": "array", "items": source_expression},
            "soft_constraints": {"type": "array", "items": soft_constraint},
            "objectives": {"type": "array", "items": objective},
            "goal": {"oneOf": [{"type": "null"}, source_expression]},
            "data": {"type": "object"},
            "datatypes": {"type": "array", "items": datatype_decl},
            "context": {},
            "objective_order": {"enum": ["single", "lexicographic"]},
            "assumptions": array({"type": "string"}),
            "unresolved": array({"type": "string"}),
            "interpretation_notes": {
                "type": "array", "items": {"type": "string"},
                "description": (
                    "Informational explanations of an already encoded interpretation; "
                    "never constraints, modeling assumptions, or replacements for unresolved alternatives."
                ),
            },
        },
        "additionalProperties": False,
        "constructor_api": hir_api(),
    }


def _datatype_dependencies(sort, params):
    """Collect nominal datatype references from a JSON sort without erasing them."""
    if isinstance(sort, dict) and set(sort) == {"Parameter"}:
        parameter = name(sort["Parameter"], "datatype parameter")
        if parameter not in params:
            raise ModelError("datatype parameter is out of scope: " + parameter)
        return set()
    if isinstance(sort, dict) and set(sort) == {"Datatype"}:
        spec = sort["Datatype"]
        if isinstance(spec, str):
            return {name(spec, "datatype sort")}
        if not isinstance(spec, dict):
            raise ModelError("invalid datatype sort")
        keys(spec, ["name", "args"])
        if not isinstance(spec["args"], list):
            raise ModelError("datatype sort args must be a list")
        deps = {name(spec["name"], "datatype sort")}
        for arg in spec["args"]:
            deps.update(_datatype_dependencies(arg, params))
        return deps
    if isinstance(sort, dict) and len(sort) == 1:
        key = next(iter(sort))
        if key in {"Set", "Tuple"}:
            values = sort[key] if key == "Tuple" else [sort[key]]
            if not isinstance(values, list):
                raise ModelError(key + " sort requires a list")
            result = set()
            for value in values:
                result.update(_datatype_dependencies(value, params))
            return result
        if key == "Array":
            if not isinstance(sort[key], list) or len(sort[key]) != 2:
                raise ModelError("Array sort requires index and element sorts")
            result = set()
            for value in sort[key]:
                result.update(_datatype_dependencies(value, params))
            return result
    return set()


def _sort_datatype_names(sort, parameter_bindings=None):
    """Collect datatype names, resolving explicit type-parameter substitutions."""
    parameter_bindings = parameter_bindings or {}
    if isinstance(sort, dict) and set(sort) == {"Parameter"}:
        return _sort_datatype_names(
            parameter_bindings.get(sort["Parameter"]), parameter_bindings
        ) if sort["Parameter"] in parameter_bindings else set()
    if isinstance(sort, dict) and set(sort) == {"Datatype"}:
        spec = sort["Datatype"]
        if isinstance(spec, str):
            return {spec}
        result = {spec["name"]}
        for argument in spec["args"]:
            result.update(_sort_datatype_names(argument, parameter_bindings))
        return result
    if isinstance(sort, dict) and len(sort) == 1:
        key = next(iter(sort))
        if key in {"Set", "Tuple"}:
            values = sort[key] if key == "Tuple" else [sort[key]]
            result = set()
            for value in values:
                result.update(_sort_datatype_names(value, parameter_bindings))
            return result
        if key == "Array":
            result = set()
            for value in sort[key]:
                result.update(_sort_datatype_names(value, parameter_bindings))
            return result
    return set()


def _substitute_datatype_sort(sort, bindings):
    """Apply one simultaneous, capture-avoiding parameter substitution.

    Binding values are already resolved in the caller's lexical scope. They
    must be inserted verbatim rather than recursively interpreted as names in
    the callee's parameter environment.
    """
    if isinstance(sort, dict) and set(sort) == {"Parameter"}:
        return bindings.get(sort["Parameter"], sort)
    if isinstance(sort, dict) and set(sort) == {"Datatype"}:
        spec = sort["Datatype"]
        if isinstance(spec, str):
            return {"Datatype": {"name": spec, "args": []}}
        return {"Datatype": {
            "name": spec["name"],
            "args": [_substitute_datatype_sort(arg, bindings)
                     for arg in spec["args"]],
        }}
    if isinstance(sort, dict) and set(sort) == {"Array"}:
        return {"Array": [_substitute_datatype_sort(arg, bindings)
                           for arg in sort["Array"]]}
    if isinstance(sort, dict) and set(sort) == {"Set"}:
        return {"Set": _substitute_datatype_sort(sort["Set"], bindings)}
    if isinstance(sort, dict) and set(sort) == {"Tuple"}:
        return {"Tuple": [_substitute_datatype_sort(arg, bindings)
                           for arg in sort["Tuple"]]}
    return sort


def _sort_tree_size(sort):
    if isinstance(sort, dict):
        return 1 + sum(_sort_tree_size(value) for value in sort.values())
    if isinstance(sort, list):
        return 1 + sum(_sort_tree_size(value) for value in sort)
    return 1


def _datatype_sort_is_inhabited(sort, parameter_bindings, active, declarations):
    """Find a finite ground value, tracking instantiated recursive types.

    Exact instance repetition closes an unproductive recursive branch. A
    strictly smaller instance of the same datatype is allowed (for example
    Box[Box[Int]] -> Box[Int]). Expanding recursive type arguments are refused
    explicitly; this bounds the checker without confusing them with proven
    ill-founded declarations.
    """
    sort = _substitute_datatype_sort(sort, parameter_bindings)
    if isinstance(sort, dict) and set(sort) == {"Parameter"}:
        # A free type parameter ranges over a well-formed, nonempty SMT sort.
        return True
    if isinstance(sort, dict) and set(sort) == {"Set"}:
        return True  # set.empty inhabits every Set sort.
    if isinstance(sort, dict) and set(sort) == {"Tuple"}:
        return all(
            _datatype_sort_is_inhabited(field, {}, active, declarations)
            for field in sort["Tuple"]
        )
    if isinstance(sort, dict) and set(sort) == {"Array"}:
        index_sort, element_sort = sort["Array"]
        recursive_names = _sort_datatype_names(sort)
        unsupported = recursive_names.intersection(active)
        if unsupported:
            raise ModelError(
                "recursive datatype occurrence under an Array sort is "
                "unsupported by the direct HIR API: " + ", ".join(sorted(unsupported))
            )
        index_inhabited = _datatype_sort_is_inhabited(
            index_sort, {}, active, declarations
        )
        # A total array over an empty index sort is the empty function. Over a
        # nonempty index sort its element sort must have a finite value.
        return not index_inhabited or _datatype_sort_is_inhabited(
            element_sort, {}, active, declarations
        )
    if isinstance(sort, dict) and set(sort) == {"Datatype"}:
        spec = sort["Datatype"]
        datatype, arguments = spec["name"], spec["args"]
        declaration = declarations[datatype]
        params, constructors, coinductive = declaration
        if coinductive:
            return True

        instance_key = repr(sort)
        instance_size = _sort_tree_size(sort)
        prior = active.get(datatype, [])
        if any(key == instance_key for key, _ in prior):
            return False
        if prior and instance_size > prior[-1][1]:
            raise ModelError(
                "expanding recursive datatype parameter substitution is "
                "unsupported by the direct HIR API: " + datatype
            )
        nested_active = dict(active)
        nested_active[datatype] = prior + [(instance_key, instance_size)]
        binding = dict(zip(params, arguments))
        unsupported_branches = []
        for fields in constructors:
            if sum(len(instances) for instances in active.values()) + 1 >= 128:
                # Still inspect every constructor alternative at the bound, so
                # a nullary or datatype-free productive alternative can prove
                # inhabitation. Refuse only branches that would descend further.
                resolved_fields = [
                    _substitute_datatype_sort(field_sort, binding)
                    for field_sort in fields
                ]
                if any(_sort_datatype_names(field_sort) for field_sort in resolved_fields):
                    unsupported_branches.append(ModelError(
                        "recursive datatype instance search exceeded its total bound"
                    ))
                    continue
            try:
                if all(
                    _datatype_sort_is_inhabited(field_sort, binding, nested_active, declarations)
                    for field_sort in fields
                ):
                    return True
            except ModelError as error:
                message = str(error)
                if (
                    "unsupported by the direct HIR API" in message
                    or "search exceeded" in message
                ):
                    unsupported_branches.append(error)
                    continue
                raise
        if unsupported_branches:
            raise unsupported_branches[0]
        return False
    # Built-in and uninterpreted SMT sorts are nonempty; sort validation is
    # performed before this search.
    return True


class HirBuilder:
    """Checked builder for declarations, constraints and optimization objectives."""

    def __init__(self):
        self.model = native.HirModel()
        self.symbols = {}
        self.finite_shapes = {}
        self.functions = {}
        self.function_sorts = {}
        from .construction_limits import current_construction_limits
        limits = current_construction_limits()
        self.max_nodes = limits.max_hir_nodes
        self.max_finite_elements = limits.max_finite_elements
        self.nodes = 0
        self.bound_serial = 0
        self._fold_values = {}
        self._source_terms = []
        self._source_term_depth = 0
        self._fold_lookup_cache = {}
        self._fold_expr_snapshots = {}
        self._fold_data_snapshots = {}
        self._fold_data_serial = 0
        # Per-model, exact definitional sharing for repeated finite sums. The
        # helper cap is independent of the unchanged 100,000 expression-node
        # budget; helper definitions and every application are charged there.
        self._sum_template_cache = {}
        self._sum_helper_serial = 0
        self._sum_template_limit = 256
        self.data = {}
        self._data_arrays = {}
        self.datatypes = {}
        self.datatype_constructors = {}
        self.datatype_selectors = {}
        self.datatype_schemas = {}

    def sort(self, value, type_params=()):
        if value == "Bool":
            return native.HirSort.boolean()
        if value == "Int":
            return native.HirSort.integer()
        if value == "Real":
            return native.HirSort.real()
        if value == "String":
            return native.HirSort.string()
        if value == "RegLan":
            return native.HirSort.reglan()
        if isinstance(value, dict) and set(value) == {"Set"}:
            return native.HirSort.set(self.sort(value["Set"], type_params))
        if isinstance(value, dict) and set(value) == {"BitVec"}:
            width = value["BitVec"]
            if type(width) is not int or width <= 0:
                raise ModelError("BitVec sort requires a positive integer width")
            return native.HirSort.bitvec(width)
        if isinstance(value, dict) and set(value) == {"FloatingPoint"}:
            fmt = value["FloatingPoint"]
            if (
                not isinstance(fmt, list)
                or len(fmt) != 2
                or any(type(v) is not int or v <= 0 for v in fmt)
            ):
                raise ModelError(
                    "FloatingPoint sort requires [exponent bits, significand bits]"
                )
            return native.HirSort.floating(*fmt)
        if isinstance(value, dict) and set(value) == {"Array"}:
            if not isinstance(value["Array"], list) or len(value["Array"]) != 2:
                raise ModelError("Array sort requires index and element sorts")
            return native.HirSort.array(
                *(self.sort(v, type_params) for v in value["Array"])
            )
        if isinstance(value, dict) and set(value) == {"Tuple"}:
            if not isinstance(value["Tuple"], list):
                raise ModelError("Tuple sort requires a list of field sorts")
            return native.HirSort.tuple(
                [self.sort(v, type_params) for v in value["Tuple"]]
            )
        if isinstance(value, dict) and set(value) == {"Parameter"}:
            parameter = name(value["Parameter"], "datatype parameter")
            if parameter not in type_params:
                raise ModelError("datatype parameter is out of scope: " + parameter)
            return native._hir_sort_parameter(parameter)
        if isinstance(value, dict) and set(value) == {"Datatype"}:
            spec = value["Datatype"]
            if isinstance(spec, str):
                datatype, arguments = name(spec, "datatype sort"), []
            elif isinstance(spec, dict):
                keys(spec, ["name", "args"])
                datatype, arguments = name(spec["name"], "datatype sort"), spec["args"]
                if not isinstance(arguments, list):
                    raise ModelError("datatype sort args must be a list")
            else:
                raise ModelError("invalid datatype sort")
            if datatype not in self.datatypes:
                raise ModelError("undeclared datatype sort: " + datatype)
            arity = self.datatypes[datatype]
            if len(arguments) != arity:
                raise ModelError(
                    f"datatype sort {datatype} takes {arity} type argument(s), not {len(arguments)}"
                )
            return native._hir_sort_datatype(
                datatype, [self.sort(arg, type_params) for arg in arguments]
            )
        if isinstance(value, dict) and set(value) == {"Uninterpreted"}:
            sort_name = name(value["Uninterpreted"], "sort")
            if sort_name in type_params:
                raise ModelError(
                    "uninterpreted sort name collides with datatype parameter: " + sort_name
                )
            return native.HirSort.uninterpreted(sort_name)
        raise ModelError("unknown HIR sort")

    def declare_datatypes(self, declarations):
        """Atomically declare one recursive or mutually-recursive datatype batch."""
        if not isinstance(declarations, list):
            raise ModelError("datatypes must be a list")
        headers = {}
        normalized = []
        for declaration in declarations:
            keys(declaration, ["name", "constructors"], ["params", "coinductive"])
            datatype = name(declaration["name"], "datatype")
            params = declaration.get("params", [])
            if not isinstance(params, list):
                raise ModelError("datatype params must be a list")
            params = [name(p, "datatype parameter") for p in params]
            if len(params) != len(set(params)):
                raise ModelError("duplicate datatype parameter in " + datatype)
            if datatype in self.datatypes or datatype in headers:
                raise ModelError("duplicate datatype declaration: " + datatype)
            constructors = declaration["constructors"]
            if not isinstance(constructors, list) or not constructors:
                raise ModelError("a datatype requires at least one constructor")
            coinductive = declaration.get("coinductive", False)
            if type(coinductive) is not bool:
                raise ModelError("coinductive must be Boolean")
            headers[datatype] = len(params)
            normalized.append((datatype, params, constructors, coinductive))

        # Keep temporary header state available while validating recursive field
        # sorts. Any failure restores the original registries before returning.
        previous_datatypes = self.datatypes
        self.datatypes = {**self.datatypes, **headers}
        try:
            all_constructor_names = set(self.datatype_constructors)
            all_selector_names = set(self.datatype_selectors)
            all_term_names = set(self.symbols) | set(self.functions)
            parsed = []
            new_constructors, new_selectors = {}, {}
            for datatype, params, constructors, coinductive in normalized:
                parsed_constructors = []
                for constructor in constructors:
                    keys(constructor, ["name", "fields"])
                    cname = name(constructor["name"], "datatype constructor")
                    fields = constructor["fields"]
                    if not isinstance(fields, list):
                        raise ModelError("datatype constructor fields must be a list")
                    if (
                        cname in all_constructor_names
                        or cname in all_selector_names
                        or cname in all_term_names
                    ):
                        raise ModelError("duplicate datatype term name: " + cname)
                    all_constructor_names.add(cname)
                    parsed_fields = []
                    for field in fields:
                        keys(field, ["name", "sort"])
                        sname = name(field["name"], "datatype selector")
                        if (
                            sname in all_selector_names
                            or sname in all_constructor_names
                            or sname in all_term_names
                        ):
                            raise ModelError("duplicate datatype term name: " + sname)
                        all_selector_names.add(sname)
                        parsed_fields.append(
                            (sname, field["sort"], self.sort(field["sort"], set(params)))
                        )
                    parsed_constructors.append((cname, parsed_fields))
                parsed.append((datatype, params, parsed_constructors, coinductive))

            declared_names = set(self.datatypes)
            for _, params, constructors, _ in parsed:
                for _, fields in constructors:
                    for _, raw_sort, _ in fields:
                        unknown = _datatype_dependencies(raw_sort, set(params)) - declared_names
                        if unknown:
                            raise ModelError(
                                "undeclared datatype field sort: " + sorted(unknown)[0]
                            )

            candidate_schemas = dict(self.datatype_schemas)
            for datatype, params, constructors, coinductive in parsed:
                candidate_schemas[datatype] = (
                    params,
                    [[raw_sort for _, raw_sort, _ in fields]
                     for _, fields in constructors],
                    coinductive,
                )
            # Validate each declared inductive type against actual instantiated
            # constructor alternatives, not a graph over raw referenced names.
            # This accepts e.g. D = mk(Box[D]) when Box has an empty constructor.
            for datatype, params, _, coinductive in parsed:
                if coinductive:
                    continue
                root_sort = {
                    "Datatype": {
                        "name": datatype,
                        "args": [{"Parameter": param} for param in params],
                    }
                }
                if not _datatype_sort_is_inhabited(
                    root_sort, {}, {}, candidate_schemas
                ):
                    raise ModelError(
                        "inductive datatype is not well-founded: no finite constructor "
                        "value exists for " + datatype
                    )

            # Stage every native declaration before mutating HirModel, then
            # commit the Python name/signature registries only after the native
            # batch append succeeds.
            native_batch = []
            for datatype, params, constructors, coinductive in parsed:
                native_constructors = []
                for cname, fields in constructors:
                    native_fields = [(sname, sort) for sname, _, sort in fields]
                    native_constructors.append((cname, native_fields))
                    new_constructors[cname] = (datatype, len(fields))
                    for sname, _, sort in fields:
                        new_selectors[sname] = (datatype, sort)
                native_batch.append((datatype, params, native_constructors, coinductive))
            native._hir_declare_datatypes(self.model, native_batch)
        except Exception:
            self.datatypes = previous_datatypes
            raise

        self.datatype_constructors.update(new_constructors)
        self.datatype_selectors.update(new_selectors)
        self.datatype_schemas = candidate_schemas

    def declare_datatype(self, declaration):
        """Convenience for a single datatype; use declare_datatypes for mutual recursion."""
        return self.declare_datatypes([declaration])

    def _check_term_name_available(self, identifier, kind, path):
        # Classify the existing binding without inferring or changing a name.
        for previous_kind, registry in [
            ("declaration", self.symbols), ("function", self.functions),
            ("datatype constructor", self.datatype_constructors),
            ("datatype selector", self.datatype_selectors),
        ]:
            if identifier not in registry:
                continue
            if previous_kind == kind:
                message = "duplicate " + kind + ": " + identifier
            else:
                message = ("name collision: " + kind + " " + repr(identifier)
                           + " conflicts with an existing " + previous_kind)
            message += "; term declarations share one namespace; use distinct identifiers and update their respective uses"
            raise ModelError(message, path + ".name")

    def declare(self, identifier, sort, lower=None, upper=None, shape=None, *, path="declaration"):
        name(identifier, path + ".name")
        self._check_term_name_available(identifier, "declaration", path)
        try:
            declared_sort = self.sort(sort)
        except ModelError as exc:
            raise ModelError(exc.message, path + ".sort") from exc
        # Zero axes add no array wrapper: the schema-valid rank-zero shape is
        # the same declaration as omitting shape. [0] remains an empty array.
        if isinstance(shape, list) and not shape:
            shape = None
        if shape is not None:
            if (
                not isinstance(shape, list)
                or not shape
                or len(shape) > 8
                or any(type(n) is not int or n < 0 for n in shape)
                or (self.max_finite_elements is not None
                    and prod(shape) > self.max_finite_elements)
            ):
                raise ModelError("invalid finite declaration shape", path + ".shape")
        # Validate all fields before constructing terms or reserving a name.
        # An invalid upper bound/shape must not consume expression budget for
        # an otherwise valid lower bound when the caller retries the builder.
        raw_bounds = []
        for field, op, bound in [("lower", "ge", lower), ("upper", "le", upper)]:
            if bound is not None:
                if repr(declared_sort) not in {"Int", "Real"}:
                    raise ModelError("numeric bounds require Int or Real elements", path + "." + field)
                number(bound, repr(declared_sort), path + "." + field)
                raw_bounds.append((field, op, bound))
        bounds = [(field, op, self.expr({"literal": bound, "sort": sort},
                                       _path=path + "." + field))
                  for field, op, bound in raw_bounds]
        if shape is not None:
            for _ in shape:
                declared_sort = native.HirSort.array(
                    native.HirSort.integer(), declared_sort
                )
        var = self.model.declare(identifier, declared_sort, source_path=path)
        self.symbols[identifier] = var
        if shape is not None:
            self.finite_shapes[identifier] = (tuple(shape), repr(self.sort(sort)))
        for field, op, literal in bounds:
            for index in (
                product(*(range(n) for n in shape)) if shape is not None else [()]
            ):
                element = var
                for i in index:
                    element = self._op(
                        "select", [element, native._hir_literal(native.HirSort.integer(), str(i))]
                    )
                self.model.constrain(self._op(op, [element, literal]),
                                     source_path=path + "." + field)
        return var

    def declare_function(self, identifier, arguments, result, *, path="function"):
        name(identifier, path + ".name")
        self._check_term_name_available(identifier, "function", path)
        if not isinstance(arguments, list):
            raise ModelError("function arguments must be a list", path + ".arguments")
        try:
            result = self.sort(result)
            argument_sorts = [self.sort(s) for s in arguments]
        except ModelError as exc:
            raise ModelError(exc.message, path) from exc
        self.model.declare_function(identifier, argument_sorts, result, source_path=path)
        self.functions[identifier] = (len(arguments), result)
        self.function_sorts[identifier] = tuple(argument_sorts)

    def define_function(self, identifier, binders, body, *, path="functions"):
        """Attach an exact, non-recursive body to a previously declared signature."""
        if identifier not in self.functions:
            raise ModelError("cannot define an undeclared function", path)
        if not isinstance(binders, list):
            raise ModelError("function binders must be a list", path + ".binders")
        expected = self.function_sorts[identifier]
        if len(binders) != len(expected):
            raise ModelError("function binder count does not match its argument signature",
                             path + ".binders")
        local = {}
        native_binders = []
        seen = set()
        for i, binder in enumerate(binders):
            binder_path = f"{path}.binders[{i}]"
            keys(binder, ["name", "sort"], path=binder_path)
            binder_name = name(binder["name"], binder_path + ".name")
            if binder_name in seen:
                raise ModelError("duplicate function binder: " + binder_name, binder_path)
            seen.add(binder_name)
            try:
                binder_sort = self.sort(binder["sort"])
            except ModelError as exc:
                raise ModelError(exc.message, binder_path + ".sort") from exc
            if not native._hir_same_sort(binder_sort, expected[i]):
                raise ModelError("function binder sort does not match argument signature",
                                 binder_path + ".sort")
            # Names valid in candidate JSON cannot contain '@', so these
            # internal bound names cannot capture a declaration or binder.
            self.bound_serial += 1
            internal = f"somt@hir_function_{self.bound_serial}"
            local[binder_name] = native._hir_ident(internal, binder_sort, True)
            native_binders.append((internal, binder_sort))
        body_value = self.expr(body, local, _path=path + ".body")
        result_sort = self.functions[identifier][1]
        if not native._hir_same_sort(body_value.sort, result_sort):
            raise ModelError("function body sort does not match declared result",
                             path + ".body")
        try:
            self.model.define_function(identifier, native_binders, body_value,
                                       source_path=path + ".body")
        except Exception as exc:
            raise ModelError(str(exc), path) from exc

    def _retain_source_terms(self, terms, env, path):
        """Keep only inputs that this constructor actually erases."""
        if not terms:
            return
        if not hasattr(native, "_hir_source_term"):
            raise ModelError("native extension lacks source-term validation; rebuild it", path)
        environment = list(env.values())
        self._source_terms.extend(native._hir_source_term(term, environment, path)
                                  for term in terms)

    @staticmethod
    def _operand_sort_message(message, actual_sort, expected):
        # Report the compiled operand's sort, including lexical shadowing.
        # These hints never change declarations, operands or source meaning.
        actual = repr(actual_sort)
        message += f"; expected {expected}, got {actual}"
        if actual.startswith("(Array "):
            message += (
                "; a shaped declaration is an array even when shape is [1]; "
                "use explicit at/select indices for an element, or declare a scalar "
                "with shape omitted or [] if the source requires a scalar")
        elif expected == "Bool" and actual in {"Int", "Real"}:
            message += (
                "; numeric values, including 0/1, are not implicitly Boolean; "
                "use an explicit comparison with the intended value")
        elif expected == "Int or Real" and actual == "Bool":
            message += (
                "; use an explicit ite(condition, Int 1, Int 0) or count for "
                "a Boolean indicator when the source calls for that count")
        return message

    def _op(self, op, args):
        if (
            op not in OPERATIONS
            or not OPERATIONS[op][0] <= len(args) <= OPERATIONS[op][1]
        ):
            raise ModelError("unknown HIR operator or invalid arity: " + op)
        if op in {"lt", "le", "gt", "ge", "add", "sub", "mul", "div"}:
            for i, arg in enumerate(args):
                if repr(arg.sort) not in {"Int", "Real"}:
                    raise ModelError(self._operand_sort_message(
                        "numeric operands required for " + op, arg.sort, "Int or Real"),
                        f"args[{i}]")
        if op == "abs" and repr(args[0].sort) not in {"Int", "Real"}:
            raise ModelError(self._operand_sort_message(
                "absolute value requires an Int or Real operand", args[0].sort,
                "Int or Real"), "args[0]")
        if op == "ite":
            if repr(args[0].sort) != "Bool":
                raise ModelError(self._operand_sort_message(
                    "ite condition must have sort Bool", args[0].sort, "Bool"), "args[0]")
            # The native contract is exact here, unlike numeric arithmetic.
            # Check before an enclosing vacuous constructor can erase the ITE.
            if not native._hir_same_sort(args[1].sort, args[2].sort):
                raise ModelError("ite branches must have the same exact sort", "args[2]")
        if op == "select":
            # mkOp derives SELECT's result sort without validating its index.
            # Reconstruct the expected Array sort; no string parsing or second
            # subtree traversal is needed, and the constructed node is reused.
            selected = native._hir_op(op, args)
            expected = native.HirSort.array(args[1].sort, selected.sort)
            if not native._hir_same_sort(args[0].sort, expected):
                raise ModelError("select requires an Array with this exact index sort", "args[1]")
            return selected
        if op == "store":
            expected = native.HirSort.array(args[1].sort, args[2].sort)
            if not native._hir_same_sort(args[0].sort, expected):
                raise ModelError("store requires exact Array index and element sorts")
        if op in {"not", "implies", "xor", "and", "or", "count"}:
            for i, arg in enumerate(args):
                if repr(arg.sort) != "Bool":
                    raise ModelError(self._operand_sort_message(
                        "Boolean operands required for " + op, arg.sort, "Bool"),
                        f"args[{i}]")
        if op in {"eq", "ne", "distinct"} and args:
            first = args[0].sort
            for i, arg in enumerate(args[1:], 1):
                if not (native._hir_same_sort(first, arg.sort) or
                        {repr(first), repr(arg.sort)} <= {"Int", "Real"}):
                    raise ModelError(f"{op} compares {first!r} with {arg.sort!r}", f"args[{i}]")
        if op in {"all_different", "all_different_except_0"}:
            if (op == "all_different_except_0" and len(args) == 3
                    and repr(args[0].sort).startswith("(Array ")):
                # The indexed global carries its own half-open [lo, hi)
                # semantics and must reach native type checking intact.
                return native._hir_global("alldifferent_except_0", args)
            if any(repr(a.sort) != "Int" for a in args):
                if op == "all_different_except_0":
                    raise ModelError("all_different_except_0 requires exact Int operands")
                raise ModelError("all_different requires scalar Int operands")
        if op in {"connected", "dconnected"}:
            # The raw JSON parser has validated literal counts/endpoints and
            # Bool node/edge offsets before HIR terms are constructed.
            return native._hir_global(op, args)
        if op in _BV_OPERATIONS and any(
            not repr(a.sort).startswith("(_ BitVec ") for a in args
        ):
            raise ModelError("bit-vector operands required")
        if op in _FP_VALUE_OPERATIONS and any(
            not repr(a.sort).startswith("(_ FloatingPoint ") for a in args
        ):
            raise ModelError("floating-point operands required")
        if op in _FP_ROUNDED_OPERATIONS and (
            repr(args[0].sort) != "RoundingMode"
            or any(
                not repr(a.sort).startswith("(_ FloatingPoint ") for a in args[1:]
            )
        ):
            raise ModelError(
                "fp arithmetic takes a rounding mode and FloatingPoint operands"
            )
        if op in _STRING_SIGNATURES:
            sig = _STRING_SIGNATURES[op]
            operands_ok = (
                all(repr(a.sort) == "String" for a in args)
                if op == "str.++"
                else all(repr(a.sort) == want for a, want in zip(args, sig))
            )
            if not operands_ok:
                raise ModelError("string operator operand sort mismatch: " + op)
        if op in _REGEX_SIGNATURES:
            signature = _REGEX_SIGNATURES[op]
            checks = (
                (repr(arg.sort) == signature[0] for arg in args)
                if len(signature) == 1
                else (repr(arg.sort) == want for arg, want in zip(args, signature))
            )
            if not all(checks):
                raise ModelError("regular-expression operand sort mismatch: " + op)
        if op == "count":
            one, zero = native._hir_literal(native.HirSort.integer(), "1"), native._hir_literal(native.HirSort.integer(), "0")
            return self._op(
                "add", [native._hir_op("ite", [e, one, zero]) for e in args]
            )
        if op == "ne":
            return native._hir_op("not", [native._hir_op("eq", args)])
        if op == "abs":
            zero = native._hir_literal(args[0].sort, "0")
            return self._op("ite", [self._op("ge", [args[0], zero]),
                                     args[0], self._op("sub", [zero, args[0]])])
        if op in ["all_different", "all_different_except_0", "distinct"] and len(args) < 2:
            return native._hir_literal(native.HirSort.boolean(), "true")
        if op == "all_different":
            return native._hir_global("alldifferent", args)
        if op == "all_different_except_0":
            return native._hir_global("alldifferent_except_0", args)
        if op in ["add", "and", "or"]:
            if not args:
                return (
                    native._hir_literal(native.HirSort.integer(), "0")
                    if op == "add"
                    else native._hir_literal(native.HirSort.boolean(), "false" if op == "or" else "true")
                )
            if len(args) == 1:
                return args[0]
        return native._hir_op(op, args)

    def _regular_deterministic(self, items, start, finals, transitions):
        """Run a partial DFA as a total finite table with a fresh rejecting sink.

        None selects the general NFA encoding. A repeated identical edge is
        still deterministic; different targets for one (state, symbol) are not.
        The table contains only constants, so nested source binders stay local
        to the input expressions and no auxiliary quantified witness is needed.
        """
        rows = {}
        used_states = {start, *finals}
        for source, symbol, target in transitions:
            row = rows.setdefault(source, {})
            if symbol in row and row[symbol] != target:
                return None
            row[symbol] = target
            used_states.update((source, target))
        sink = 0
        while sink in used_states:
            sink += 1
        # Charge every constructed node before allocating the table. Original
        # exact-label validation and the overall builder budget still apply.
        self.nodes += (10 + 3 * sum(len(row) for row in rows.values())
                       + 2 * len(rows) + 2 * len(set(finals)) + 2 * len(items))
        if self.max_nodes is not None and self.nodes > self.max_nodes:
            raise ModelError("HIR construction budget exceeded")
        integer = native.HirSort.integer()
        literal = lambda value: native._hir_literal(integer, str(value))
        false = native._hir_literal(native.HirSort.boolean(), "false")
        true = native._hir_literal(native.HirSort.boolean(), "true")
        missing = native._hir_const_array(integer, literal(sink))
        table = native._hir_const_array(integer, missing)
        for source, row in sorted(rows.items()):
            targets = missing
            for symbol, target in sorted(row.items()):
                targets = self._op("store", [targets, literal(symbol), literal(target)])
            table = self._op("store", [table, literal(source), targets])
        accepting = native._hir_const_array(integer, false)
        for state in sorted(set(finals)):
            accepting = self._op("store", [accepting, literal(state), true])
        state = literal(start)
        for item in items:
            state = self._op("select", [self._op("select", [table, state]), item])
        return self._op("select", [accepting, state])

    def _regular(self, items, start, finals, transitions):
        """An exact DFA run or local NFA witness using shared finite tables.

        Entry numbers are internal witnesses, not automaton states or symbols.
        Arbitrary integer labels and nondeterministic transitions are preserved.
        """
        integer = native.HirSort.integer()
        literal = lambda value: native._hir_literal(integer, str(value))
        boolean = lambda value: native._hir_literal(native.HirSort.boolean(), str(value).lower())
        if not items:
            return boolean(start in finals)
        if not transitions or not finals:
            return boolean(False)
        deterministic = self._regular_deterministic(items, start, finals, transitions)
        if deterministic is not None:
            return deterministic
        self.nodes += 25 * len(items) + 3 * len(finals) + 10
        if self.max_nodes is not None and self.nodes > self.max_nodes:
            raise ModelError("HIR construction budget exceeded")
        columns = [self._data_array("Int", tuple(str(row[j]) for row in transitions))
                   for j in range(3)]
        self.bound_serial += 1
        state_name = f"somt@hir_regular_state_{self.bound_serial}"
        entry_name = f"somt@hir_regular_entry_{self.bound_serial}"
        array_sort = native.HirSort.array(integer, integer)
        states = native._hir_ident(state_name, array_sort, True)
        entries = native._hir_ident(entry_name, array_sort, True)
        at = lambda array, index: self._op("select", [array, literal(index)])
        path = [self._op("eq", [at(states, 0), literal(start)]),
                self._op("or", [self._op("eq", [at(states, len(items)), literal(f)])
                                 for f in finals])]
        for i, item in enumerate(items):
            choice = at(entries, i)
            path.extend([self._op("ge", [choice, literal(0)]),
                         self._op("lt", [choice, literal(len(transitions))])])
            for value, column in zip((at(states, i), item, at(states, i+1)), columns):
                path.append(self._op("eq", [value, self._op("select", [column, choice])]))
        return native._hir_quantifier(False, [(state_name, array_sort),
                                              (entry_name, array_sort)],
                                      self._op("and", path))

    def _data_table(self, table):
        """Validate mutable public data and return an immutable exact snapshot."""
        steps = 0

        def scan(value, depth):
            nonlocal steps
            steps += 1
            if depth > 64 or steps > 100000:
                raise ModelError("HIR data validation budget exceeded")
            if isinstance(value, list):
                if not value:
                    return (0,), None, ()
                children = [scan(item, depth + 1) for item in value]
                shape = children[0][0]
                if any(child[0] != shape for child in children[1:]):
                    raise ModelError("data table must be rectangular and have uniform rank")
                sorts = {sort for _, sort, _ in children if sort is not None}
                if len(sorts) > 1:
                    raise ModelError("data table leaves must have one exact scalar sort")
                return ((len(value),) + shape, next(iter(sorts), None),
                        tuple(leaf for _, _, leaves in children for leaf in leaves))
            if type(value) is bool:
                return (), "Bool", (str(value).lower(),)
            if type(value) is int:
                return (), "Int", (str(number(value, "Int", "data table leaf")),)
            if isinstance(value, str):
                return (), "Real", (str(number(value, "Real", "data table leaf")),)
            raise ModelError("data table leaves must be exact Bool, Int, or Real values")

        return scan(table, 0)

    def _data_array(self, leaf_sort, leaves):
        # Cache content, not the mutable JSON object's address. Distinct source
        # shapes can share flattened values; guards/strides remain at each use.
        key = leaf_sort, tuple(leaves)
        if key in self._data_arrays:
            return self._data_arrays[key]
        self.nodes += 2 + 3 * len(leaves)
        if self.max_nodes is not None and self.nodes > self.max_nodes:
            raise ModelError("HIR construction budget exceeded")
        integer, element = native.HirSort.integer(), self.sort(leaf_sort)
        zero = "false" if leaf_sort == "Bool" else "0"
        result = native._hir_const_array(integer, native._hir_literal(element, zero))
        for i, value in enumerate(leaves):
            if value != zero:
                result = self._op("store", [result, native._hir_literal(integer, str(i)),
                                             native._hir_literal(element, value)])
        self._data_arrays[key] = result
        return result

    def _guard_nonzero(self, condition, env, truth=True):
        """Sufficient local facts only; each fact retains its lexical binding.

        Strong references and identity checks prevent facts about an outer name
        from applying to a shadowing quantifier/fold, or a later reused wrapper.
        No solver is invoked and no extra constraints are asserted.
        """
        facts, pending, steps = {}, [(condition, truth)], 0
        while pending:
            term, value = pending.pop()
            steps += 1
            if steps > 100000:
                raise ModelError("HIR guard analysis budget exceeded")
            if not isinstance(term, dict) or set(term) != {"op", "args"}:
                continue
            op, args = term["op"], term["args"]
            if not isinstance(op, str) or not isinstance(args, list):
                continue
            op = OPERATOR_ALIASES.get(op, op)
            if op == "not" and len(args) == 1:
                pending.append((args[0], not value))
                continue
            if (op == "and" and value) or (op == "or" and not value):
                pending.extend((arg, value) for arg in args)
                continue
            if op not in {"eq", "ne", "lt", "le", "gt", "ge"} or len(args) != 2:
                continue
            left, right = args
            if isinstance(right, dict) and set(right) == {"var"}:
                left, right = right, left
                op = {"eq": "eq", "ne": "ne", "lt": "gt", "le": "ge", "gt": "lt", "ge": "le"}[op]
            if (not isinstance(left, dict) or set(left) != {"var"}
                    or not isinstance(left["var"], str)
                    or not isinstance(right, dict) or set(right) != {"literal", "sort"}
                    or right["sort"] not in ["Int", "Real"]):
                continue
            identifier = left["var"]
            binding = env.get(identifier, self.symbols.get(identifier))
            if binding is None or repr(binding.sort) not in ["Int", "Real"]:
                continue
            constant = number(right["literal"], right["sort"], "guard constant")
            if not value:
                op = {"eq": "ne", "ne": "eq", "lt": "ge", "le": "gt", "gt": "le", "ge": "lt"}[op]
            excludes_zero = ((op == "eq" and constant != 0)
                or (op == "ne" and constant == 0)
                or (op == "gt" and constant >= 0)
                or (op == "ge" and constant > 0)
                or (op == "lt" and constant <= 0)
                or (op == "le" and constant < 0))
            if excludes_zero:
                facts[identifier] = binding
        return facts

    def _fold_lookup_key(self, expr, env, nonzero, depth):
        """Key total subexpressions under identical finite-fold values.

        Only expressions whose source binders have concrete expanded-fold values
        are shared. Symbolically bound variables and partial arithmetic are
        left on the ordinary checked path.
        """
        if not isinstance(expr, dict) or not any(key in expr for key in ("at", "data", "op")):
            return None

        variables = set()
        data_names = set()
        unsupported = False
        scanned = {}
        scan_steps = 0

        def inspect(value, depth=0):
            nonlocal unsupported, scan_steps
            scan_steps += 1
            if depth > 64 or scan_steps > 10000:
                unsupported = True
                return
            if isinstance(value, list):
                for item in value:
                    inspect(item, depth + 1)
                return
            if not isinstance(value, dict):
                return
            if scanned.get(id(value), -1) >= depth:
                return
            scanned[id(value)] = depth
            if set(value) == {"var"}:
                if not isinstance(value["var"], str):
                    unsupported = True
                    return
                variables.add(value["var"])
                return
            if ("at" in value and isinstance(value["at"], str)
                    and value["at"] in env):
                unsupported = True
                return
            if any(key in value for key in ("fold", "quantifier", "cp")):
                unsupported = True
                return
            if "op" in value:
                if not isinstance(value["op"], str) or value["op"] in {
                    "div", "div_euclid", "div_trunc", "div_floor",
                    "mod", "mod_euclid", "mod_trunc", "mod_floor",
                }:
                    unsupported = True
                    return
            if "data" in value and isinstance(value["data"], str):
                data_names.add(value["data"])
            for child in value.values():
                inspect(child, depth + 1)

        # A subtree cached at a shallow occurrence must not bypass the depth
        # check when reused deeper in another expression. Falling back is safe
        # even when this conservative JSON-depth check exceeds HIR depth.
        inspect(expr, depth)
        if unsupported:
            return None
        # An `at` base name is an ordinary declared array in the current API;
        # do not cache if a lexical binding shadows it.
        if ("at" in expr and isinstance(expr["at"], str)
                and expr["at"] in env):
            return None
        fold_bindings = []
        for variable in sorted(variables):
            if variable in env:
                if variable not in self._fold_values:
                    return None
                fold_bindings.append((variable, self._fold_values[variable]))
        if not fold_bindings:
            return None
        data_pins = []
        for data_name in sorted(data_names):
            table = self.data.get(data_name)
            try:
                table_key = json.dumps(table, sort_keys=True, separators=(",", ":"))
            except (TypeError, ValueError, RecursionError):
                return None
            prior = self._fold_data_snapshots.get(data_name)
            if prior is None or prior[0] != table_key:
                self._fold_data_serial += 1
                prior = (table_key, self._fold_data_serial)
                self._fold_data_snapshots[data_name] = prior
            data_pins.append((data_name, prior[1]))
        try:
            expression = json.dumps(expr, sort_keys=True, separators=(",", ":"))
        except (TypeError, ValueError, RecursionError):
            return None
        expression_digest = hashlib.sha256(expression.encode("utf-8")).digest()
        snapshots = self._fold_expr_snapshots.setdefault(expression_digest, [])
        try:
            expression_index = snapshots.index(expression)
        except ValueError:
            expression_index = len(snapshots)
            snapshots.append(expression)
        return (
            expression_digest,
            expression_index,
            tuple(fold_bindings),
            tuple(data_pins),
            tuple(sorted(nonzero)),
        )

    def _sum_template(self, fold_expr, env):
        """Build a typed alpha/literal template for a safe finite sum.

        Fold and free-variable names, array bases, and typed literals become
        helper parameters. Nested binders and partial division/modulo are
        deliberately excluded so guard facts and capture rules stay local.
        The key includes the exact range, parameter sorts, and current data
        snapshots; values themselves remain call arguments.
        """
        fold_identifier = fold_expr["var"]
        descriptors, free_slots, array_slots, literal_slots = [], {}, {}, 0
        data_pins = {}
        unsafe = False
        scan_steps = 0
        fold_placeholder = "__somt_sum_index"

        def resolved(identifier):
            value = env.get(identifier, self.symbols.get(identifier))
            if value is None or not hasattr(value, "sort"):
                raise ModelError("undeclared variable: " + identifier)
            return value

        def add_variable(identifier, kind, source_path):
            table = free_slots if kind == "variable" else array_slots
            if identifier not in table:
                table[identifier] = len(table)
                value = resolved(identifier)
                descriptor = {"kind": kind, "source": identifier,
                              "slot": table[identifier],
                              "sort": value.sort,
                              "sort_key": repr(value.sort),
                              "source_path": source_path}
                if kind == "array":
                    # A binder in env can shadow a declared finite array with
                    # the same source name. Only attach declaration metadata
                    # when the array reference resolves to that declaration.
                    shape = (None if identifier in env else
                             self.finite_shapes.get(identifier))
                    descriptor["shape"] = tuple(shape[0]) if shape is not None else None
                    descriptor["shape_key"] = descriptor["shape"]
                descriptors.append(descriptor)
            return table[identifier]

        def normalize(value, depth=0, source_path=".body", preserve_index_literals=False):
            nonlocal unsafe, literal_slots, scan_steps
            scan_steps += 1
            if depth > 64 or scan_steps > 10000:
                unsafe = True
                return value
            if isinstance(value, list):
                return [normalize(item, depth + 1, f"{source_path}[{index}]",
                                  preserve_index_literals)
                        for index, item in enumerate(value)]
            if not isinstance(value, dict):
                return value
            if set(value) == {"literal", "sort"}:
                if preserve_index_literals:
                    return value
                try:
                    sort_value = self.sort(value["sort"])
                except ModelError:
                    unsafe = True
                    return value
                slot = literal_slots
                literal_slots += 1
                descriptors.append({"kind": "literal", "source": value,
                                    "slot": slot,
                                    "sort": sort_value,
                                    "sort_key": repr(sort_value),
                                    "source_path": source_path})
                return {"var": f"__somt_sum_literal_{slot}"}
            if set(value) == {"var"}:
                identifier = value["var"]
                if not isinstance(identifier, str):
                    unsafe = True
                    return value
                if identifier == fold_identifier:
                    return {"var": fold_placeholder}
                try:
                    slot = add_variable(identifier, "variable", source_path)
                except ModelError:
                    unsafe = True
                    return value
                return {"var": f"__somt_sum_free_{slot}"}
            if any(key in value for key in ("fold", "quantifier", "cp")):
                unsafe = True
                return value
            if set(value) == {"at", "indices"}:
                array_name, indices = value["at"], value["indices"]
                if not isinstance(array_name, str) or not isinstance(indices, list):
                    unsafe = True
                    return value
                shape_info = (None if array_name in env else
                              self.finite_shapes.get(array_name))
                # Preserve the ordinary checked path whenever a literal access
                # is statically out of bounds or the source index rank cannot
                # be compared with the known finite declaration shape.
                if shape_info is not None:
                    shape = shape_info[0]
                    if len(indices) > len(shape):
                        unsafe = True
                        return value
                    for index, extent in zip(indices, shape):
                        if (isinstance(index, dict) and set(index) == {"literal", "sort"}
                                and index.get("sort") == "Int"
                                and type(index.get("literal")) is int
                                and not 0 <= index["literal"] < extent):
                            unsafe = True
                            return value
            if "op" in value:
                operator = value.get("op")
                if not isinstance(operator, str) or operator in {
                    "div", "div_euclid", "div_trunc", "div_floor",
                    "mod", "mod_euclid", "mod_trunc", "mod_floor",
                }:
                    unsafe = True
                    return value
            result = {}
            if not (set(value) & {"op", "at", "data", "var", "literal", "apply"}):
                unsafe = True
                return value
            for key, child in value.items():
                if key == "at":
                    if not isinstance(child, str):
                        unsafe = True
                        result[key] = child
                        continue
                    try:
                        slot = add_variable(child, "array", source_path + ".at")
                    except ModelError:
                        unsafe = True
                        result[key] = child
                        continue
                    result[key] = f"__somt_sum_array_{slot}"
                elif key == "indices" and "at" in value:
                    result[key] = normalize(child, depth + 1,
                                            source_path + "." + key)
                elif key == "indices" and "data" in value:
                    # Data lookup literal indices can trigger static handling
                    # in the normal path; keep them concrete in helper bodies.
                    result[key] = normalize(child, depth + 1,
                                            source_path + "." + key,
                                            preserve_index_literals=True)
                elif key == "data" and isinstance(child, str):
                    try:
                        snapshot = json.dumps(
                            self.data[child], sort_keys=True, separators=(",", ":")
                        )
                    except (KeyError, TypeError, ValueError, RecursionError):
                        unsafe = True
                        result[key] = child
                        continue
                    data_pins[child] = hashlib.sha256(snapshot.encode("utf-8")).hexdigest()
                    result[key] = child
                elif key == "data":
                    unsafe = True
                    result[key] = child
                else:
                    result[key] = normalize(child, depth + 1,
                                            source_path + "." + key)
            return result

        body = normalize(fold_expr["body"])
        if unsafe:
            return None
        # Slot identity and descriptor kind are part of the key. Dict key
        # insertion order controls traversal, so two equivalent source maps
        # can encounter an Int variable and an Int literal in different
        # orders even though their normalized body is the same. The helper
        # call arguments must retain the exact formal-to-actual association.
        signature = [(item["kind"], item["slot"], item["sort_key"],
                      item.get("shape_key"))
                     for item in descriptors]
        key_data = {
            "range": fold_expr["range"], "body": body,
            "signature": signature, "data_sha256": data_pins,
        }
        encoded = json.dumps(key_data, sort_keys=True, separators=(",", ":"))
        key = hashlib.sha256(encoded.encode("utf-8")).digest()
        return key, body, descriptors, fold_placeholder

    def _sum_function_name(self):
        reserved = (set(self.symbols) | set(self.functions)
                    | set(self.datatype_constructors) | set(self.datatype_selectors))
        while True:
            self._sum_helper_serial += 1
            identifier = f"somt_hir_sum_template_{self._sum_helper_serial}"
            if identifier not in reserved:
                return identifier

    def _charge_sum_helper_nodes(self, count, path):
        self.nodes += count
        if self.max_nodes is not None and self.nodes > self.max_nodes:
            raise ModelError("HIR construction budget exceeded", path)

    def _sum_terms(self, terms, path):
        # Large finite sums still obey each native application's arity. Group
        # an associative exact sum without dropping terms or changing scope.
        width = OPERATIONS["add"][1]
        while len(terms) > width:
            self._charge_sum_helper_nodes((len(terms) + width - 1) // width, path)
            terms = [self._op("add", terms[i:i + width])
                     for i in range(0, len(terms), width)]
        return self._op("add", terms)

    def _define_sum_helper(self, fold_expr, env, depth, nonzero, path,
                           template, function_name):
        key, body, descriptors, fold_placeholder = template
        lower, upper = fold_expr["range"]
        integer = native.HirSort.integer()
        local = {}
        binders = []
        argument_sorts = []
        for index, descriptor in enumerate(descriptors):
            # Internal SMT binder names contain '@', which cannot occur in API
            # identifiers. Template placeholders live only in this private AST.
            internal = f"somt@hir_sum_{self._sum_helper_serial}_{index}"
            sort = descriptor["sort"]
            argument_sorts.append(sort)
            binders.append((internal, sort))
            if descriptor["kind"] == "literal":
                placeholder = f"__somt_sum_literal_{sum(1 for d in descriptors[:index] if d['kind'] == 'literal')}"
            elif descriptor["kind"] == "array":
                placeholder = f"__somt_sum_array_{sum(1 for d in descriptors[:index] if d['kind'] == 'array')}"
            else:
                placeholder = f"__somt_sum_free_{sum(1 for d in descriptors[:index] if d['kind'] == 'variable')}"
            local[placeholder] = native._hir_ident(internal, sort, True)

        try:
            saved_lookup_cache = self._fold_lookup_cache
            # The helper body uses private placeholder identifiers, and each
            # helper has its own lexical function binders. Existing lookup
            # cache entries are keyed by source names/values, not binder
            # identity, so do not share terms across helper scopes.
            self._fold_lookup_cache = None
            terms = []
            try:
                for value in range(lower, upper):
                    iteration_env = dict(local)
                    iteration_env[fold_placeholder] = native._hir_literal(integer, str(value))
                    had_previous = fold_placeholder in self._fold_values
                    previous = self._fold_values.get(fold_placeholder)
                    self._fold_values[fold_placeholder] = value
                    try:
                        terms.append(self.expr(body, iteration_env, depth + 1, nonzero,
                                               _path=path + ".body"))
                    finally:
                        if had_previous:
                            self._fold_values[fold_placeholder] = previous
                        else:
                            self._fold_values.pop(fold_placeholder, None)
            finally:
                self._fold_lookup_cache = saved_lookup_cache
            total = self._sum_terms(terms, path + ".body")
            result_sort = total.sort
            if repr(result_sort) not in {"Int", "Real"}:
                raise ModelError("sum fold body must have exact numeric sort", path + ".body")
            # Charge the auxiliary declaration/definition before mutating the
            # native model. A cap failure therefore leaves no dangling helper.
            self._charge_sum_helper_nodes(3 + len(descriptors), path)
            self.model.declare_function(function_name, argument_sorts, result_sort,
                                        auxiliary=True, source_path=path)
            self.functions[function_name] = (len(argument_sorts), result_sort)
            self.function_sorts[function_name] = tuple(argument_sorts)
            self.model.define_function(function_name, binders, total,
                                       source_path=path + ".body")
        except ModelError as exc:
            if getattr(exc, "_hir_located", False):
                # Keep the most specific source path produced while checking
                # the helper body (for example data.indices[0]).
                raise
            located = ModelError(exc.message, path + ".body")
            located._hir_located = True
            raise located from exc
        except Exception as exc:
            raise ModelError(str(exc), path + ".body") from exc

        return result_sort

    def _sum_helper_apply(self, fold_expr, env, depth, nonzero, path):
        # A checked-but-erased body must not create helper declarations or
        # mutate the helper cache. Its nested sums remain expression DAGs.
        if self._source_term_depth:
            return None
        template = self._sum_template(fold_expr, env)
        if template is None or fold_expr["range"][0] == fold_expr["range"][1]:
            return None
        key, _, descriptors, _ = template
        cached = self._sum_template_cache.get(key)
        if cached is None:
            if len(self._sum_template_cache) >= self._sum_template_limit:
                return None
            function_name = self._sum_function_name()
            result_sort = self._define_sum_helper(
                fold_expr, env, depth, nonzero, path, template, function_name
            )
            cached = (function_name, result_sort, tuple(d["sort"] for d in descriptors))
            self._sum_template_cache[key] = cached
        function_name, result_sort, expected_sorts = cached
        arguments = []
        for descriptor, expected in zip(descriptors, expected_sorts):
            if descriptor["kind"] == "literal":
                argument = self.expr(descriptor["source"], env, depth + 1, nonzero,
                                     _path=path + descriptor["source_path"])
            else:
                argument = self.expr({"var": descriptor["source"]}, env, depth + 1,
                                     nonzero, _path=path + descriptor["source_path"])
            if not native._hir_same_sort(argument.sort, expected):
                raise ModelError("sum helper argument sort mismatch", path)
            arguments.append(argument)
        self._charge_sum_helper_nodes(1, path)  # helper application node
        return native._hir_apply(function_name, result_sort, arguments)

    def expr(self, expr, env=None, depth=0, _nonzero=None, *, _path="model"):
        env = {} if env is None else env
        nonzero = {} if _nonzero is None else _nonzero
        if (isinstance(expr, dict) and isinstance(expr.get("op"), str)
                and "args" not in expr):
            from .hir_cp import normalize_cp_operator_form
            cp_expression = normalize_cp_operator_form(expr)
            if cp_expression is not None:
                expr = cp_expression
        if (isinstance(expr, dict) and isinstance(expr.get("op"), str)
                and expr["op"] in OPERATOR_ALIASES):
            # Copy only this node; never mutate a sealed candidate in place.
            expr = dict(expr)
            expr["op"] = OPERATOR_ALIASES[expr["op"]]
        if (isinstance(expr, dict) and isinstance(expr.get("cp"), dict)
                and set(expr["cp"]) == {"abs"} and set(expr) == {"cp"}):
            # Accept the compact CP spelling {cp: {abs: expr}} as well as
            # the documented {cp: abs, value: expr} form.
            expr = dict(expr)
            expr["value"] = expr["cp"]["abs"]
            expr["cp"] = "abs"
        try:
            key = (self._fold_lookup_key(expr, env, nonzero, depth)
                   if depth <= 64 and self._fold_lookup_cache is not None else None)
            if (key is not None and self._fold_lookup_cache is not None
                    and key in self._fold_lookup_cache):
                self.nodes += 1
                if self.max_nodes is not None and self.nodes > self.max_nodes:
                    raise ModelError("HIR construction budget exceeded")
                return self._fold_lookup_cache[key]
            result = self._expr_uncached(expr, env, depth, nonzero, _path)
            if key is not None and self._fold_lookup_cache is not None:
                self._fold_lookup_cache[key] = result
            return result
        except ModelError as exc:
            # Attach the source JSON path at the innermost failing expression.
            # Outer folds/constructors must not overwrite that location.
            # CP expansion can introduce expressions absent from the source
            # JSON. Its enclosing constructor is the honest source location.
            if isinstance(expr, dict) and "cp" in expr:
                located = ModelError(exc.message, _path)
                located._hir_located = True
                raise located from exc
            if getattr(exc, "_hir_located", False):
                raise
            suffix = ""
            detail = exc.message
            if exc.path != "model":
                # Older helpers use semantic labels, e.g. "data table leaf".
                # Only append a label when it resolves in this source object.
                value = expr
                try:
                    if not re.fullmatch(r"[A-Za-z_]\w*(?:\[\d+\]|\.[A-Za-z_]\w*)*", exc.path):
                        raise KeyError(exc.path)
                    for field, index in re.findall(r"([A-Za-z_]\w*)|\[(\d+)\]", exc.path):
                        value = value[field] if field else value[int(index)]
                    suffix = "." + exc.path
                except (KeyError, IndexError, TypeError):
                    detail = exc.path + ": " + detail
            located = ModelError(detail, _path + suffix)
            located._hir_located = True
            raise located from exc

    def _cp_expr(self, expr, env, depth, nonzero, _path):
        from .hir_cp import cp_validation_guards

        # Other constructors are checked by their explicit JSON expansion,
        # which carries the same local guards. Native fast paths do not consume
        # that expansion and therefore retain their guards directly in HIR.
        kind = expr.get("cp")
        if not isinstance(kind, str) or kind not in {
            "minimum", "maximum", "regular", "diffn", "cumulative",
            "among", "global_cardinality", "table", "element", "no_overlap",
        }:
            return self._cp_expr_result(expr, env, depth, nonzero, _path)
        finite_shapes = {identifier: shape for identifier, shape in self.finite_shapes.items()
                         if identifier not in env}
        guards = cp_validation_guards(
            expr, reserved=set(self.symbols) | set(self.functions) | set(env),
            finite_shapes=finite_shapes, erased_only=True,
        )
        checked = [self.expr(guard, env, depth + 1, nonzero, _path=_path)
                   for guard in guards]
        result = self._cp_expr_result(expr, env, depth, nonzero, _path)
        if not checked:
            return result
        # Keep every original operand visible to native type/scope checking,
        # even if the CP relation is empty or a task has zero duration. The
        # shared result makes this an identity in every surrounding polarity;
        # nothing is asserted globally and lexical bound terms stay local.
        return self._op("ite", [self._op("and", checked), result, result])

    def _cp_expr_result(self, expr, env, depth, nonzero, _path):
        # Lazy import avoids the hir <-> hir_cp module cycle. The adapter
        # expands into base JSON constructors; this builder remains the
        # sole authority for native type and scope checks.
        from .hir_cp import expand_cp_expression, expand_cp_vector

        reserved = set(self.symbols) | set(self.functions) | set(env)
        # Lexical arrays may shadow a finite declaration with a different
        # rank. Its global shape must not constrain the local binding.
        finite_shapes = {name: shape for name, shape in self.finite_shapes.items()
                         if name not in env}
        kind = expr.get("cp")
        if isinstance(kind, str) and kind in {"element", "no_overlap"}:
            # Share only identical immutable source objects within this one
            # call and lexical environment. No structural subtree scan or
            # cross-scope cache is needed, and each operand is checked once.
            compiled = {}

            def operand(value):
                key = id(value)
                if key not in compiled:
                    compiled[key] = self.expr(value, env, depth + 1, nonzero, _path=_path)
                return compiled[key]

            integer = native.HirSort.integer()
            literal = lambda value: native._hir_literal(integer, str(value))
            if kind == "element":
                from .hir_cp import element_inputs
                items, index, default = element_inputs(expr, reserved, finite_shapes=finite_shapes)
                selected = operand(index)
                if repr(selected.sort) != "Int":
                    raise ModelError("CP element index must have exact sort Int")
                result = operand(default)
                values = [operand(item) for item in items]
                if any(not native._hir_same_sort(value.sort, result.sort) for value in values):
                    raise ModelError("CP element items and default must have one exact sort")
                self.nodes += 3 * len(values) + (2 if not values else 0)
                if self.max_nodes is not None and self.nodes > self.max_nodes:
                    raise ModelError("HIR construction budget exceeded")
                for i in reversed(range(len(values))):
                    result = self._op("ite", [self._op("eq", [selected, literal(i)]), values[i], result])
                if not values:
                    # Retain the already built index for deep native checking;
                    # inspecting its result sort alone would miss a bad select.
                    result = self._op("ite", [self._op("eq", [selected, selected]), result, result])
                return result
            from .hir_cp import no_overlap_inputs
            starts, durations = no_overlap_inputs(expr, reserved, finite_shapes=finite_shapes)
            values = [operand(start) for start in starts]
            if any(repr(value.sort) != "Int" for value in values):
                raise ModelError("CP no_overlap starts must have exact sort Int")
            active = [i for i, duration in enumerate(durations) if duration]
            if len(active) >= 64:
                # Half-open intervals do not overlap exactly when their unit
                # demands fit a capacity of one. Retain the native cumulative
                # relation instead of building a quadratic Python/HIR formula.
                # Keep zero-duration operands too: native checking must still
                # validate their complete expressions, even under negation.
                one = literal(1)
                duration_terms = {duration: literal(duration) for duration in set(durations)}
                self.nodes += 1 + len(duration_terms)
                if self.max_nodes is not None and self.nodes > self.max_nodes:
                    raise ModelError("HIR construction budget exceeded")
                arguments = [one]
                for start, duration in zip(values, durations):
                    arguments.extend((start, duration_terms[duration], one))
                return native._hir_global("cumulative", arguments)
            pair_count = len(active) * (len(active) - 1) // 2
            if pair_count > OPERATIONS["and"][1]:
                raise ModelError("CP no_overlap exceeds native conjunction arity")
            self.nodes += 7 * pair_count + len(values) + 3
            if self.max_nodes is not None and self.nodes > self.max_nodes:
                raise ModelError("HIR construction budget exceeded")
            checks = []
            for offset, i in enumerate(active):
                for previous in range(offset):
                    j = active[previous]
                    checks.append(self._op("or", [
                        self._op("le", [self._op("add", [values[i], literal(durations[i])]), values[j]]),
                        self._op("le", [self._op("add", [values[j], literal(durations[j])]), values[i]]),
                    ]))
            # Normal participating starts already occur in the relation. Only
            # removed operands need a retained check; zero duration adds no
            # scheduling constraint, including under negation.
            erased = [value for i, value in enumerate(values)
                      if not durations[i] or len(active) < 2]
            result = self._op("and", checks)
            if erased:
                guard = self._op("and", [self._op("eq", [value, value]) for value in erased])
                result = self._op("ite", [guard, result, result])
            return result
        if isinstance(kind, str) and kind in {"minimum", "maximum"}:
            from .hir_cp import extrema_inputs
            items = extrema_inputs(expr, reserved, finite_shapes=finite_shapes)
            values = [self.expr(item, env, depth + 1, nonzero, _path=_path)
                      for item in items]
            if any(repr(value.sort) != "Int" for value in values):
                raise ModelError("CP minimum/maximum items must have exact sort Int")
            # Compile each operand once and share native results across the
            # comparison and selected branch. Balance the DAG to keep its
            # depth logarithmic, including when lowered and serialized.
            self.nodes += 2 * (len(values) - 1)
            if self.max_nodes is not None and self.nodes > self.max_nodes:
                raise ModelError("HIR construction budget exceeded")
            comparison = "le" if kind == "minimum" else "ge"
            while len(values) > 1:
                values = [self._op("ite", [self._op(comparison, values[i:i + 2]),
                                          values[i], values[i + 1]])
                          if i + 1 < len(values) else values[i]
                          for i in range(0, len(values), 2)]
            return values[0]
        if kind == "regular":
            from .hir_cp import regular_inputs
            items, start, finals, transitions = regular_inputs(expr, reserved, finite_shapes=finite_shapes)
            values = [self.expr(item, env, depth + 1, nonzero, _path=_path) for item in items]
            if any(repr(value.sort) != "Int" for value in values):
                raise ModelError("CP regular items must have exact sort Int")
            if not finals or not transitions:
                self._retain_source_terms(values, env, _path)
            return self._regular(values, start, finals, transitions)
        if kind == "diffn":
            from .hir_cp import diffn_inputs
            dimensions, positions, sizes, nonstrict = diffn_inputs(expr, reserved, finite_shapes=finite_shapes)
            arguments = [native._hir_literal(native.HirSort.integer(), str(dimensions))]
            for box, extent in zip(positions, sizes):
                for position, size in zip(box, extent):
                    arguments.extend([self.expr(position, env, depth + 1, nonzero, _path=_path),
                                      self.expr(size, env, depth + 1, nonzero, _path=_path)])
            if any(repr(value.sort) != "Int" for value in arguments):
                raise ModelError("CP diffn arguments must have exact sort Int")
            return native._hir_global("diffn_nonstrict" if nonstrict else "diffn", arguments)
        if kind == "cumulative":
            from .hir_cp import cumulative_inputs
            starts, durations, demands, capacity = cumulative_inputs(expr, reserved, finite_shapes=finite_shapes)
            # Scope-local identity sharing: each source operand is checked
            # once. Keep all operands alive throughout this call so IDs cannot
            # be reused, and never share across distinct lexical environments.
            compiled = {}
            def compile_operand(value):
                key = id(value)
                if key not in compiled:
                    compiled[key] = self.expr(value, env, depth + 1, nonzero, _path=_path)
                return compiled[key]
            arguments = [compile_operand(capacity)]
            for triple in zip(starts, durations, demands):
                arguments.extend(compile_operand(value) for value in triple)
            if any(repr(value.sort) != "Int" for value in arguments):
                raise ModelError("CP cumulative arguments must have exact sort Int")
            return native._hir_global("cumulative", arguments)
        if isinstance(kind, str) and kind in {"among", "global_cardinality"}:
            from .hir_cp import cardinality_inputs
            items, values, counts, closed = cardinality_inputs(expr, reserved, finite_shapes=finite_shapes)
            compiled_items = [self.expr(item, env, depth + 1, nonzero, _path=_path)
                              for item in items]
            if any(repr(item.sort) != "Int" for item in compiled_items):
                raise ModelError("CP among/global_cardinality items must have exact sort Int")
            compiled_counts = [self.expr(count, env, depth + 1, nonzero, _path=_path)
                               for count in counts]
            if any(repr(count.sort) != "Int" for count in compiled_counts):
                raise ModelError("CP global_cardinality counts must have exact sort Int")
            if not values:
                # Both open GCC's true identity and closed GCC's false
                # membership erase all original items, as does an empty membership set in among.
                self._retain_source_terms(compiled_items, env, _path)
            integer = native.HirSort.integer()
            # Native DAG operands are shared. Re-expanding their JSON once
            # per listed value rejects ordinary 200-item car-sequencing
            # inputs before any HIR can be built.
            columns = [[self._op("eq", [item, native._hir_literal(integer, str(value))])
                        for item in compiled_items] for value in values]
            memberships = ([self._op("or", [column[i] for column in columns])
                            for i in range(len(compiled_items))]
                           if kind == "among" or closed else [])
            if kind == "among":
                return self._op("count", memberships)
            checks = [self._op("eq", [self._op("count", column), count])
                      for column, count in zip(columns, compiled_counts)]
            checks.extend(memberships)
            return self._op("and", checks)

        expanded = expand_cp_expression(
            expr, reserved=reserved, finite_shapes=finite_shapes
        )
        if kind == "table":
            items = expand_cp_vector(expr["items"], reserved=reserved,
                                     finite_shapes=finite_shapes)
            values = [self.expr(item, env, depth + 1, nonzero, _path=_path) for item in items]
            if any(repr(value.sort) != "Int" for value in values):
                raise ModelError("CP table items must have exact sort Int")
            integer = native.HirSort.integer()
            literal = lambda value: native._hir_literal(integer, str(value))
            rows = expr["tuples"]  # validated by the expansion above
            args = [literal(len(values)), literal(len(rows)), *values]
            args.extend(literal(value) for row in rows for value in row)
            relation = native._hir_global("table", args)
            return relation if expr["positive"] else native._hir_op("not", [relation])
        return self.expr(expanded, env, depth, nonzero, _path=_path)

    def _expr_uncached(self, expr, env=None, depth=0, _nonzero=None, _path="model"):
        env = {} if env is None else env
        nonzero = {} if _nonzero is None else _nonzero
        self.nodes += 1
        if depth > 64 or (self.max_nodes is not None and self.nodes > self.max_nodes):
            raise ModelError("HIR construction budget exceeded")
        if not isinstance(expr, dict):
            raise ModelError("expression must be an object")

        if "cp" in expr:
            return self._cp_expr(expr, env, depth, nonzero, _path)

        def visit(e, scope=env, facts=nonzero, path=""):
            return self.expr(e, scope, depth + 1, facts, _path=_path + path)

        if "const_array" in expr:
            keys(expr, ["const_array"])
            spec = expr["const_array"]
            keys(spec, ["index_sort", "value"])
            return native._hir_const_array(self.sort(spec["index_sort"]), visit(spec["value"], path=".const_array.value"))
        if "tuple_unit" in expr:
            keys(expr, ["tuple_unit"])
            if expr["tuple_unit"] is not True:
                raise ModelError("tuple_unit must be exactly true")
            return native._hir_tuple_unit()
        if "tuple" in expr:
            keys(expr, ["tuple"])
            if not isinstance(expr["tuple"], list) or not expr["tuple"]:
                raise ModelError("tuple constructor requires a nonempty list of fields; use tuple_unit for UnitTuple")
            return native._hir_tuple([visit(field, path=f".tuple[{i}]") for i, field in enumerate(expr["tuple"])])
        if "at" in expr:
            keys(expr, ["at", "indices"])
            if not isinstance(expr["indices"], list) or not expr["indices"]:
                raise ModelError("array access requires indices")
            result = visit({"var": expr["at"]})
            for i, index in enumerate(expr["indices"]):
                result = self._op("select", [result, visit(index, path=f".indices[{i}]")])
            return result
        if "data" in expr:
            keys(expr, ["data", "indices", "default"])
            if expr["data"] not in self.data or not isinstance(expr["indices"], list):
                raise ModelError("unknown data table or invalid indices")
            indices = [visit(e, path=f".indices[{i}]") for i, e in enumerate(expr["indices"])]
            default = visit(expr["default"], path=".default")
            for position, index in enumerate(indices):
                if repr(index.sort) != "Int":
                    raise ModelError("data lookup indices must have sort Int",
                                     f"indices[{position}]")

            shape, leaf_sort, leaves = self._data_table(self.data[expr["data"]])
            if len(indices) != len(shape):
                raise ModelError("data lookup index count does not match table rank")
            if leaf_sort is not None and repr(default.sort) != leaf_sort:
                raise ModelError("data lookup default sort does not match table leaves")
            if not leaves:
                return default
            if not shape:
                return native._hir_literal(self.sort(leaf_sort), leaves[0])

            # Validate the whole rectangular table before specializing constant
            # indices. An unused ragged row or wrong-sort leaf remains an error.
            fixed = [arg["literal"] if (isinstance(arg, dict)
                     and set(arg) == {"literal", "sort"} and arg["sort"] == "Int"
                     and type(arg["literal"]) is int) else None
                     for arg in expr["indices"]]
            if any(i is not None and not 0 <= i < n for i, n in zip(fixed, shape)):
                return default
            if any(i is not None for i in fixed):
                strides = [prod(shape[k+1:]) for k in range(len(shape))]
                leaves = tuple(leaves[sum(i*s for i, s in zip(index, strides))]
                               for index in product(*(range(n) if i is None else (i,)
                                                      for n, i in zip(shape, fixed))))
                shape, indices = (tuple(n for n, i in zip(shape, fixed) if i is None),
                                  [index for index, i in zip(indices, fixed) if i is None])
                if not shape:
                    return native._hir_literal(self.sort(leaf_sort), leaves[0])
            array = self._data_array(leaf_sort, leaves)
            integer = native.HirSort.integer()
            literal = lambda n: native._hir_literal(integer, str(n))
            offset = literal(0)
            guards = []
            for n, index in zip(shape, indices):
                guards.extend([self._op("ge", [index, literal(0)]),
                               self._op("lt", [index, literal(n)])])
                offset = self._op("add", [self._op("mul", [offset, literal(n)]), index])
            # Each source axis is checked separately: an out-of-range column
            # must not alias the next flattened row. Defaults stay local to
            # this lookup and may depend on a bound variable.
            return self._op("ite", [self._op("and", guards),
                                    self._op("select", [array, offset]), default])

        if "var" in expr and "fold" not in expr:
            keys(expr, ["var"])
            identifier = name(expr["var"], "var")
            if identifier in env:
                return env[identifier]
            if identifier not in self.symbols:
                raise ModelError("undeclared variable: " + identifier)
            return self.symbols[identifier]
        if "literal" in expr:
            keys(expr, ["literal", "sort"])
            sort, value = expr["sort"], expr["literal"]
            if sort == "Bool":
                if type(value) is not bool:
                    raise ModelError("Bool literal must be Boolean")
                return native._hir_literal(
                    native.HirSort.boolean(), str(value).lower()
                )
            if sort in ["Int", "Real"]:
                exact = number(value, sort, "literal")
                return native._hir_literal(self.sort(sort), str(exact))
            if sort == "String":
                if not isinstance(value, str):
                    raise ModelError("String literal must be a JSON string")
                return native._hir_literal(native.HirSort.string(), value)
            if sort == "RegLan":
                if value not in ("re.none", "re.all", "re.allchar"):
                    raise ModelError("RegLan literal must be re.none, re.all or re.allchar")
                return native._hir_literal(native.HirSort.reglan(), value)
            if isinstance(sort, dict) and set(sort) == {"Set"}:
                if value not in ("set.empty", "set.universe"):
                    raise ModelError("Set literal must be set.empty or set.universe")
                return native._hir_literal(self.sort(sort), value)
            if isinstance(sort, dict) and set(sort) == {"BitVec"}:
                declared = self.sort(sort)
                if _bitvec_literal_width(value) != sort["BitVec"]:
                    raise ModelError(
                        "bit-vector literal width does not match its sort"
                    )
                return native._hir_literal(declared, value)
            if isinstance(sort, dict) and set(sort) == {"FloatingPoint"}:
                declared = self.sort(sort)
                eb, sb = sort["FloatingPoint"]
                return native._hir_literal(declared, _float_literal_text(value, eb, sb))
            raise ModelError("unsupported literal sort")
        if "rm" in expr:
            keys(expr, ["rm"])
            if expr["rm"] not in ROUNDING_MODES:
                raise ModelError("unknown rounding mode")
            return native._hir_rounding_mode(expr["rm"])
        if "op_indexed" in expr:
            keys(expr, ["op_indexed"])
            spec = expr["op_indexed"]
            keys(spec, ["op", "indices", "args"])
            op_name = spec["op"]
            if not isinstance(op_name, str) or op_name not in INDEXED_OPERATIONS:
                raise ModelError("unknown indexed HIR operator")
            want_indices, want_args = INDEXED_OPERATIONS[op_name]
            indices, args = spec["indices"], spec["args"]
            indices_ok = (
                isinstance(indices, list)
                and (want_indices is None or len(indices) == want_indices)
                and all(type(i) is int and i >= 0 for i in indices)
            )
            if not indices_ok:
                suffix = "any number of" if want_indices is None else str(want_indices)
                raise ModelError(op_name + f" requires {suffix} nonnegative integer indices")
            if not isinstance(args, list) or len(args) != want_args:
                raise ModelError(op_name + f" requires {want_args} arguments")
            visited = [visit(a, path=f".op_indexed.args[{i}]") for i, a in enumerate(args)]
            if op_name.startswith("tuple."):
                return native._hir_tuple_op(op_name, indices, visited)
            if want_indices is None:
                raise ModelError(op_name + " requires a variable number of indices")
            return native._hir_op_indexed(op_name, indices, visited)
        if "op" in expr:
            keys(expr, ["op", "args"])
            op, args = expr["op"], expr["args"]
            if not isinstance(op, str) or not isinstance(args, list):
                raise ModelError("invalid operator")
            graph_counts = None
            if op in {"connected", "dconnected"}:
                if len(args) < 2:
                    raise ModelError(op + " requires N and E count literals")

                def fixed_graph_int(value, field, *, endpoint=False):
                    path = ".args[" + str(field) + "]"
                    if not isinstance(value, dict):
                        raise ModelError("graph counts and endpoints must be Int literals", path)
                    keys(value, ["literal", "sort"], ["span"])
                    if value["sort"] != "Int":
                        raise ModelError("graph counts and endpoints require exact Int literals", path)
                    integer = number(value["literal"], "Int", path + ".literal")
                    if integer.denominator != 1 or integer < 0:
                        raise ModelError("graph counts and endpoints must be nonnegative", path)
                    integer = int(integer)
                    if integer >= 2**63:
                        raise ModelError("graph count or endpoint exceeds native Int range", path)
                    return integer

                node_count = fixed_graph_int(args[0], 0)
                edge_count = fixed_graph_int(args[1], 1)
                expected = 2 + node_count + 3 * edge_count
                if len(args) != expected:
                    raise ModelError(
                        op + " argument count does not match N and E (expected "
                        + str(expected) + ")"
                    )
                for index in range(2, 2 + 2 * edge_count):
                    endpoint = fixed_graph_int(args[index], index, endpoint=True)
                    if endpoint >= node_count:
                        raise ModelError(
                            "edge endpoint is outside zero-based range [0,N)",
                            ".args[" + str(index) + "]",
                        )
                graph_counts = (node_count, edge_count)
            if op in {"all_different", "all_different_except_0"}:
                indexed_except_zero = (
                    op == "all_different_except_0" and len(args) == 3
                    and isinstance(args[0], dict) and set(args[0]) == {"var"}
                )
                expanded = []
                for index, arg in enumerate(args):
                    identifier = arg.get("var") if isinstance(arg, dict) else None
                    if indexed_except_zero and index == 0:
                        expanded.append(arg)
                        continue
                    if (isinstance(identifier, str) and set(arg) == {"var"}
                            and identifier not in env and identifier in self.finite_shapes):
                        shape, element_sort = self.finite_shapes[identifier]
                        if element_sort != "Int":
                            raise ModelError(
                                op + " finite arrays require exact Int elements"
                            )
                        if len(expanded) + prod(shape) > OPERATIONS[op][1]:
                            raise ModelError(op + " expansion exceeds 10000 operands")
                        expanded.extend(
                            {"at": identifier, "indices": [
                                {"literal": i, "sort": "Int"} for i in index
                            ]}
                            for index in (product(*(range(n) for n in shape))
                                          if all(shape) else ())
                        )
                    else:
                        expanded.append(arg)
                    if len(expanded) > OPERATIONS[op][1]:
                        raise ModelError(op + " expansion exceeds 10000 operands")
                args = expanded
            if graph_counts is not None:
                visited = [visit(a, path=f".args[{i}]") for i, a in enumerate(args)]
                n, e = graph_counts
                edge_begin = 2 + 2 * e + n
                for i in range(2, 2 + 2 * e):
                    if repr(visited[i].sort) != "Int":
                        raise ModelError("graph endpoints require exact Int sort",
                                         ".args[" + str(i) + "]")
                for i in range(2 + 2 * e, edge_begin):
                    if repr(visited[i].sort) != "Bool":
                        raise ModelError("graph node selections require exact Bool sort",
                                         ".args[" + str(i) + "]")
                for i in range(edge_begin, len(visited)):
                    if repr(visited[i].sort) != "Bool":
                        raise ModelError("graph edge selections require exact Bool sort",
                                         ".args[" + str(i) + "]")
                return self._op(op, visited)
            if op.startswith(("div", "mod")):
                if len(args) != 2 or not isinstance(args[1], dict):
                    raise ModelError("division requires a nonzero denominator")
                denominator = args[1]
                if "literal" in denominator:
                    if (denominator.get("sort") not in ["Int", "Real"]
                            or number(denominator["literal"], denominator["sort"], "args[1].literal") == 0):
                        raise ModelError("division requires a nonzero numeric denominator")
                else:
                    identifier = denominator.get("var")
                    binding = (env.get(identifier, self.symbols.get(identifier))
                               if isinstance(identifier, str) else None)
                    if (set(denominator) != {"var"} or binding is None
                            or nonzero.get(identifier) is not binding):
                        raise ModelError("division requires a nonzero literal denominator or a locally guarded numeric variable")
            if op == "implies" and len(args) == 2:
                consequent_facts = dict(nonzero, **self._guard_nonzero(args[0], env))
                return self._op(op, [visit(args[0], path=".args[0]"), visit(args[1], facts=consequent_facts, path=".args[1]")])
            if op == "ite" and len(args) == 3:
                positive = dict(nonzero, **self._guard_nonzero(args[0], env))
                negative = dict(nonzero, **self._guard_nonzero(args[0], env, False))
                return self._op(op, [visit(args[0], path=".args[0]"), visit(args[1], facts=positive, path=".args[1]"),
                                     visit(args[2], facts=negative, path=".args[2]")])
            if op in {"and", "or"}:
                # Only the assignment region in which all other operands are
                # relevant matters. Outside it one conjunct is false or one
                # disjunct is true, independently of SMT's zero-division value.
                facts = dict(nonzero, **self._guard_nonzero(expr, env, op == "and"))
                return self._op(op, [visit(arg, facts=facts, path=f".args[{i}]") for i, arg in enumerate(args)])
            compiled = [visit(a, path=f".args[{i}]") for i, a in enumerate(args)]
            if op in {"distinct", "all_different", "all_different_except_0"} and len(compiled) == 1:
                self._retain_source_terms(compiled, env, _path + ".args[0]")
            return self._op(op, compiled)
        if "dt_constructor" in expr:
            keys(expr, ["dt_constructor", "sort", "args"])
            constructor = name(expr["dt_constructor"], "datatype constructor")
            if constructor not in self.datatype_constructors:
                raise ModelError("unknown datatype constructor: " + constructor)
            arity = self.datatype_constructors[constructor][1]
            if not isinstance(expr["args"], list) or len(expr["args"]) != arity:
                raise ModelError("datatype constructor arity mismatch: " + constructor)
            result_sort = self.sort(expr["sort"])
            return native._hir_dt_constructor(
                constructor, result_sort, [visit(arg, path=f".args[{i}]") for i, arg in enumerate(expr["args"])]
            )
        if "dt_selector" in expr:
            keys(expr, ["dt_selector", "sort", "value"])
            selector = name(expr["dt_selector"], "datatype selector")
            if selector not in self.datatype_selectors:
                raise ModelError("unknown datatype selector: " + selector)
            return native._hir_dt_selector(
                selector, self.sort(expr["sort"]), visit(expr["value"], path=".value")
            )
        if "dt_tester" in expr:
            keys(expr, ["dt_tester", "value"])
            constructor = name(expr["dt_tester"], "datatype constructor")
            if constructor not in self.datatype_constructors:
                raise ModelError("unknown datatype tester constructor: " + constructor)
            return native._hir_dt_tester(constructor, visit(expr["value"], path=".value"))
        if "apply" in expr:
            keys(expr, ["apply", "args"])
            identifier = expr["apply"]
            if identifier not in self.functions:
                raise ModelError("undeclared function")
            arity, result = self.functions[identifier]
            if not isinstance(expr["args"], list) or len(expr["args"]) != arity:
                raise ModelError("function arity mismatch")
            arguments = [visit(a, path=f".args[{i}]") for i, a in enumerate(expr["args"])]
            for i, (argument, expected) in enumerate(zip(arguments, self.function_sorts[identifier])):
                if not native._hir_same_sort(argument.sort, expected):
                    raise ModelError(
                        "function argument sort does not match declared signature: " + identifier,
                        f"args[{i}]",
                    )
            return native._hir_apply(identifier, result, arguments)
        if "fold" in expr:
            keys(expr, ["fold", "var", "range", "body"])
            fold, r = expr["fold"], expr["range"]
            if (
                fold not in ["sum", "forall", "exists"]
                or not isinstance(r, list)
                or len(r) != 2
                or any(type(v) is not int for v in r)
                or r[1] < r[0]
                or (self.max_finite_elements is not None
                    and r[1] - r[0] > self.max_finite_elements)
            ):
                raise ModelError(
                    "finite fold requires an explicit increasing range"
                    + (f" of at most {self.max_finite_elements} elements"
                       if self.max_finite_elements is not None else "")
                )
            identifier = name(expr["var"], "fold")
            if r[0] == r[1]:
                if not hasattr(native, "_hir_source_term"):
                    raise ModelError("native extension lacks source-term validation; rebuild it")
                integer = native.HirSort.integer()
                self.bound_serial += 1
                internal = f"somt@hir_fold_{self.bound_serial}"
                local = dict(env, **{identifier: native._hir_ident(internal, integer, True)})
                had_previous = identifier in self._fold_values
                previous = self._fold_values.pop(identifier, None)
                self._source_term_depth += 1
                try:
                    body = visit(expr["body"], local, path=".body")
                finally:
                    self._source_term_depth -= 1
                    if had_previous:
                        self._fold_values[identifier] = previous
                expected = {"Int", "Real"} if fold == "sum" else {"Bool"}
                if repr(body.sort) not in expected:
                    raise ModelError(
                        "sum fold body must have exact numeric sort" if fold == "sum"
                        else "Boolean fold body must have exact sort Bool", "body")
                self._retain_source_terms([body], local, _path + ".body")
                # Empty sums retain their body's numeric sort. Empty Boolean
                # folds keep their usual identities, irrespective of the body.
                return native._hir_literal(
                    body.sort, "0" if fold == "sum" else
                    "true" if fold == "forall" else "false")
            if fold == "sum":
                helper = self._sum_helper_apply(
                    expr, env, depth, nonzero, _path
                )
                if helper is not None:
                    return helper
            if fold in {"forall", "exists"} and r[1] - r[0] > 8:
                # Preserve the explicitly finite domain without a Cartesian
                # expansion of nested folds. A quantified Int is restricted
                # by the original half-open bounds, never by a guessed horizon.
                integer = native.HirSort.integer()
                self.bound_serial += 1
                internal = f"somt@hir_fold_{self.bound_serial}"
                bound = native._hir_ident(internal, integer, True)
                local = dict(env, **{identifier: bound})
                had_previous = identifier in self._fold_values
                previous = self._fold_values.pop(identifier, None)
                try:
                    body = visit(expr["body"], local, path=".body")
                finally:
                    if had_previous:
                        self._fold_values[identifier] = previous
                if repr(body.sort) != "Bool":
                    raise ModelError("Boolean fold body must have exact sort Bool")
                domain = self._op("and", [
                    self._op("ge", [bound, native._hir_literal(integer, str(r[0]))]),
                    self._op("lt", [bound, native._hir_literal(integer, str(r[1]))]),
                ])
                guarded = self._op("implies" if fold == "forall" else "and", [domain, body])
                return native._hir_quantifier(fold == "forall", [(internal, integer)], guarded)
            terms = []
            previous = self._fold_values.get(identifier)
            had_previous = identifier in self._fold_values
            for i in range(*r):
                self._fold_values[identifier] = i
                local = dict(env, **{
                    identifier: native._hir_literal(native.HirSort.integer(), str(i))
                })
                try:
                    terms.append(visit(expr["body"], local, path=".body"))
                finally:
                    if had_previous:
                        self._fold_values[identifier] = previous
                    else:
                        self._fold_values.pop(identifier, None)
            if fold == "sum":
                return self._sum_terms(terms, _path + ".body")
            return self._op({"forall": "and", "exists": "or"}[fold], terms)
        if "quantifier" in expr:
            keys(expr, ["quantifier", "binders", "body"])
            if (
                expr["quantifier"] not in ["forall", "exists", "exists_unique"]
                or not isinstance(expr["binders"], list)
                or not expr["binders"]
            ):
                raise ModelError("invalid quantifier")
            bindings, local, seen = [], dict(env), set()
            binder_sorts = []
            for b in expr["binders"]:
                keys(b, ["name", "sort"])
                identifier, sort = name(b["name"], "binder"), self.sort(b["sort"])
                if identifier in seen:
                    raise ModelError("duplicate binder")
                seen.add(identifier)
                binder_sorts.append((identifier, sort))
                # The native HIR requires distinct binder names. Source-level
                # shadowing is resolved here, before that invariant is checked.
                # '@' cannot occur in API identifiers (name uses isidentifier),
                # so fresh internal names cannot capture a user declaration,
                # including one added to this builder after the quantifier.
                self.bound_serial += 1
                internal = f"somt@hir_bound_{self.bound_serial}"
                bindings.append((internal, sort))
                local[identifier] = native._hir_ident(internal, sort, True)
            previous = {key: self._fold_values.pop(key) for key in local
                        if key in self._fold_values and key in env}
            try:
                body = visit(expr["body"], local, path=".body")
                if expr["quantifier"] == "exists_unique":
                    # Compile the same source body under a second lexical
                    # environment rather than substituting identifier strings.
                    # Nested binders may shadow either name; fresh native names
                    # cannot capture declarations, functions, or outer binders.
                    alternatives, other_local, equalities = [], dict(env), []
                    self.nodes += 2 * len(binder_sorts) + 4
                    if self.max_nodes is not None and self.nodes > self.max_nodes:
                        raise ModelError("HIR construction budget exceeded")
                    for identifier, sort in binder_sorts:
                        self.bound_serial += 1
                        internal = f"somt@hir_bound_{self.bound_serial}"
                        other = native._hir_ident(internal, sort, True)
                        alternatives.append((internal, sort))
                        other_local[identifier] = other
                        equalities.append(self._op("eq", [other, local[identifier]]))
                    other_body = visit(expr["body"], other_local, path=".body")
                    unique = native._hir_quantifier(
                        True, alternatives,
                        self._op("implies", [other_body, self._op("and", equalities)]),
                    )
                    body = self._op("and", [body, unique])
            finally:
                self._fold_values.update(previous)
            return native._hir_quantifier(expr["quantifier"] == "forall", bindings, body)
        raise ModelError("unknown HIR constructor")

    def constrain(self, expr):
        self.model.constrain(self.expr(expr))

    def soft_constrain(self, expr, weight, *, group="", source_path=""):
        """Add one weighted Bool preference; never split or deduplicate it."""
        _soft_parameters(weight, group, source_path or "soft_constraint")
        if not hasattr(self.model, "soft_constrain"):
            raise ModelError("native extension lacks the soft-constraint API; rebuild it", source_path)
        expression = self.expr(expr, _path=source_path or "soft_constraint.expr")
        try:
            self.model.soft_constrain(expression, weight, group=group, source_path=source_path)
        except (ValueError, TypeError) as error:
            raise ModelError(str(error), source_path or "soft_constraint") from error

    def validate(self):
        """Check the complete native HIR without lowering or invoking a solver.

        Raises ModelError for the first error; well-typed unsatisfiable models
        remain valid. JSON builds retain the containing source expression path.
        """
        diagnostics = (self.model.validate(self._source_terms) if self._source_terms
                       else self.model.validate())
        for diagnostic in diagnostics:
            if diagnostic.severity == native.Severity.ERROR:
                raise ModelError(diagnostic.message, diagnostic.file or "model")
        return diagnostics

    def translate(self, *, profile="default", dialect=None, details: bool = True) -> "native.Translation":
        options = {"source_terms": self._source_terms} if self._source_terms else {}
        return self.model.translate(
            profile, native.OmtDialect.Z3 if dialect is None else dialect, details=details, **options
        )


def _soft_parameters(weight, group, path):
    # Do not route arbitrary-precision coefficients through int or float.
    if (not isinstance(weight, str) or re.fullmatch(r"[0-9]+", weight) is None
            or not weight.strip("0")):
        raise ModelError("expected a positive ASCII integer string", path + ".weight")
    if not isinstance(group, str):
        raise ModelError("expected a group symbol string", path + ".group")


def build_hir(model, source):
    """Validate source-linked candidate and build native HIR without text parsing."""
    keys(model, hir_schema()["required"],
         ["context", "data", "datatypes", "interpretation_notes", "soft_constraints"])
    if model["schema"] != SCHEMA or model["language"] != "hir":
        raise ModelError("invalid HIR schema")
    for field in [
        "declarations",
        "functions",
        "constraints",
        "objectives",
        "assumptions",
        "unresolved",
    ]:
        if not isinstance(model[field], list):
            raise ModelError("expected list", field)
    soft_constraints = model.get("soft_constraints", [])
    if not isinstance(soft_constraints, list):
        raise ModelError("expected list", "soft_constraints")
    if any(
        not isinstance(x, str) for k in ["assumptions", "unresolved"] for x in model[k]
    ):
        raise ModelError("assumptions and unresolved must contain strings")
    notes = model.get("interpretation_notes", [])
    if not isinstance(notes, list):
        raise ModelError("expected list", "interpretation_notes")
    for i, note in enumerate(notes):
        if not isinstance(note, str):
            raise ModelError("expected string", f"interpretation_notes[{i}]")
    if model["unresolved"]:
        raise ModelError("unresolved interpretation: " + "; ".join(model["unresolved"]))
    decision = model["decision"]
    if decision not in ["satisfiability", "optimization", "validity"]:
        raise ModelError("unknown decision")
    objective_order = model["objective_order"]
    if type(objective_order) is not str or objective_order not in ("single", "lexicographic"):
        raise ModelError(
            "expected 'single' or 'lexicographic'", "objective_order"
        )
    if bool(model["objectives"] or soft_constraints) != (decision == "optimization") or (
        model["goal"] is not None
    ) != (decision == "validity"):
        raise ModelError("decision/objective/goal mismatch")
    builder = HirBuilder()
    if soft_constraints and not hasattr(builder.model, "soft_constrain"):
        raise ModelError("native extension lacks the soft-constraint API; rebuild it", "soft_constraints")
    if not isinstance(model.get("data", {}), dict):
        raise ModelError("data must be an object")
    builder.data = model.get("data", {})
    builder.declare_datatypes(model.get("datatypes", []))
    for i, d in enumerate(model["declarations"]):
        path = f"declarations[{i}]"
        keys(d, ["name", "sort"], ["lower", "upper", "shape"], path=path)
        builder.declare(
            d["name"], d["sort"], d.get("lower"), d.get("upper"), d.get("shape"),
            path=path,
        )
    for i, f in enumerate(model["functions"]):
        path = f"functions[{i}]"
        keys(f, ["name", "arguments", "result"],
             ["binders", "body", "span"], path=path)
        definition_fields = {"binders", "body", "span"} & f.keys()
        if definition_fields and definition_fields != {"binders", "body", "span"}:
            raise ModelError("function definitions require binders, body, and span", path)
        builder.declare_function(f["name"], f["arguments"], f["result"], path=path)
    for i, f in enumerate(model["functions"]):
        if "body" in f:
            span = f["span"]
            if (
                not isinstance(span, list)
                or len(span) != 2
                or any(type(v) is not int for v in span)
                or not 0 <= span[0] < span[1] <= len(source)
            ):
                raise ModelError("invalid source span", f"functions[{i}].span")
            builder.define_function(f["name"], f["binders"], f["body"],
                                    path=f"functions[{i}]")

    def linked(item, path, extra=()):
        keys(item, ["expr", "span", *extra], path=path)
        span = item["span"]
        if (
            not isinstance(span, list)
            or len(span) != 2
            or any(type(v) is not int for v in span)
            or not 0 <= span[0] < span[1] <= len(source)
        ):
            raise ModelError("invalid source span", path + ".span")
        return builder.expr(item["expr"], _path=path + ".expr")

    pending_constraints = [
        (linked(c, f"constraints[{i}]"), f"constraints[{i}].expr")
        for i, c in enumerate(model["constraints"])
    ]
    if model["goal"] is not None:
        goal = linked(model["goal"], "goal")
        if repr(goal.sort) != "Bool":
            raise ModelError("validity goal must have sort Bool", "goal.expr")
        pending_constraints.append(
            (builder._op("not", [goal]), "goal.expr")
        )
    pending_objectives = []
    for i, obj in enumerate(model["objectives"]):
        if obj.get("sense") not in ["minimize", "maximize"]:
            raise ModelError("unknown objective sense")
        pending_objectives.append(
            (obj["sense"] == "maximize", linked(obj, f"objectives[{i}]", ("sense",)),
             f"objectives[{i}].expr")
        )
    pending_soft = []
    for i, item in enumerate(soft_constraints):
        path = f"soft_constraints[{i}]"
        keys(item, ["expr", "weight", "group", "span"], path=path)
        _soft_parameters(item["weight"], item["group"], path)
        expression = linked(item, path, ("weight", "group"))
        if repr(expression.sort) != "Bool":
            raise ModelError("soft constraint must have sort Bool", path + ".expr")
        pending_soft.append((expression, item["weight"], item["group"], path + ".expr"))
    # Sum helper definitions can also be discovered in soft constraints.
    # Stage every expression before appending any roots so all auxiliary
    # declarations/definitions precede their applications in model order.
    for constraint, path in pending_constraints:
        builder.model.constrain(constraint, source_path=path)
    for expression, weight, group, path in pending_soft:
        try:
            builder.model.soft_constrain(expression, weight, group=group, source_path=path)
        except (ValueError, TypeError) as error:
            raise ModelError(str(error), path) from error
    builder.model.objective_order(model["objective_order"])
    for maximize, objective, path in pending_objectives:
        builder.model.objective(maximize, objective, source_path=path)
    builder.validate()
    return builder
