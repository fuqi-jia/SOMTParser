"""Complete small-domain relations for MiniZinc 2.9.4/Gecode emitted globals.

Signatures come from the official 2.9.4 share/minizinc/gecode library:
redefinitions-2.0.2.mzn, redefinitions-2.5.2.mzn and the corresponding
fzn_*.mzn files. Gecode's circuit singleton and GCC duplicate-cover contracts
are also checked against release-6.3.0 int/circuit/val.hpp and int/gcc.cpp.
The independent Python predicates enumerate values, never reuse HIR lowering.
"""
from itertools import product

import pytest
import somtparser as sp
import z3


PROFILES = ("default", "ground", "quantified")


def assert_relation(source, domains, expected, profile):
    """Compare every assignment of the given finite scalar domains.

    Any generated internal witnesses are existentially solved at each complete
    source assignment. This also checks that accepted assignments are not lost.
    """
    result = sp.translate(source=source + "\nsolve satisfy;", language="flatzinc",
                          profile=profile, dialect=sp.OmtDialect.Z3)
    assert result.ok, [d.message for d in result.diagnostic_items]
    assert result.report.fidelity.sound and result.report.fidelity.complete
    whole = z3.Optimize()
    whole.set(timeout=0)
    whole.from_string(result.to_smt2(sp.OmtDialect.Z3))
    assert len(whole.objectives()) == 0
    solver = z3.Solver()
    solver.set(timeout=0)
    solver.add(*whole.assertions())
    variables = {name: (z3.Bool(name) if type(values[0]) is bool else z3.Int(name))
                 for name, values in domains.items()}
    for values in product(*domains.values()):
        assignment = dict(zip(domains, values))
        solver.push()
        solver.add(*[variables[name] == value for name, value in assignment.items()])
        observed = solver.check()
        assert observed in (z3.sat, z3.unsat), (assignment, solver.reason_unknown())
        assert (observed == z3.sat) == bool(expected(assignment)), assignment
        solver.pop()


@pytest.mark.parametrize("profile", PROFILES)
@pytest.mark.parametrize("offset", [-3, 1, 2**80 + 17, -(2**80) + 13])
def test_bool_element_offset_literals_and_repeated_aliases(profile, offset):
    source = ("var int: i; var bool: a; var bool: out;"
              "array [1..4] of var bool: cells = [a,false,a,true];"
              f"constraint gecode_bool_element(i,{offset},cells,out);")
    assert_relation(source, {"i": list(range(offset - 1, offset + 5)),
                             "a": [False, True], "out": [False, True]},
                    lambda v: offset <= v["i"] < offset + 4 and
                    v["out"] == [v["a"], False, v["a"], True][v["i"] - offset],
                    profile)


@pytest.mark.parametrize("profile", PROFILES)
@pytest.mark.parametrize("offset", [2**80 + 17, -(2**80) + 13])
def test_existing_int_element_keeps_arbitrary_precision_offset(profile, offset):
    source = ("var int: i; var int: a; var int: out;"
              f"constraint gecode_int_element(i,{offset},[a,7],out);")
    assert_relation(source, {"i": list(range(offset - 1, offset + 3)),
                             "a": [-2, 3], "out": [-2, 3, 7, 8]},
                    lambda v: offset <= v["i"] < offset + 2 and
                    v["out"] == [v["a"], 7][v["i"] - offset], profile)


@pytest.mark.parametrize("profile", PROFILES)
@pytest.mark.parametrize("sets", [("-2..-1", "4..5"), ("{-1,-2}", "{5,4,4}")])
def test_int_element2d_is_row_major_with_independent_axis_bounds(profile, sets):
    source = ("var int: row; var int: col; var int: a; var int: out;"
              f"set of int: rows = {sets[0]}; set of int: cols = {sets[1]};"
              "array [1..4] of var int: cells = [a,7,-3,a];"
              "constraint gecode_int_element2d(row,col,cells,rows,cols,out);")
    assert_relation(source, {"row": [-3, -2, -1, 0], "col": [3, 4, 5, 6],
                             "a": [-3, 0, 2], "out": [-3, 0, 2, 7, 8]},
                    lambda v: v["row"] in (-2, -1) and v["col"] in (4, 5) and
                    v["out"] == [v["a"], 7, -3, v["a"]][
                        (v["row"] + 2) * 2 + v["col"] - 4], profile)


@pytest.mark.parametrize("profile", PROFILES)
@pytest.mark.parametrize("cover", [[0, 2], [2, 2]])
def test_global_cardinality_is_open_and_duplicate_cover_counts_agree(profile, cover):
    source = ("var int: x; var int: y; var int: c0; var int: c1;"
              f"constraint gecode_global_cardinality([x,y,x],{cover},[c0,c1]);")
    def expected(v):
        values = [v["x"], v["y"], v["x"]]
        return v["c0"] == values.count(cover[0]) and v["c1"] == values.count(cover[1])
    assert_relation(source, {"x": [-1, 0, 2], "y": [-1, 0, 2],
                             "c0": [-1, 0, 1, 2, 3, 4], "c1": [-1, 0, 1, 2, 3, 4]},
                    expected, profile)


@pytest.mark.parametrize("profile", PROFILES)
def test_open_global_cardinality_empty_cover_does_not_close_values(profile):
    assert_relation("var int: x; constraint gecode_global_cardinality([x],[],[]);",
                    {"x": [-2, 0, 3]}, lambda v: True, profile)


@pytest.mark.parametrize("profile", PROFILES)
@pytest.mark.parametrize("cover,lower,upper", [
    ([-1, 2], [1, 0], [2, 1]),
    ([-1, 2], [-3, 0], [2, 2]),
    ([-1, 2], [-3, 0], [-1, 2]),
    ([-1, 2], [2, 0], [1, 2]),
    ([2, 2], [1, 2], [3, 2]),
    ([2, 2], [0, 2], [1, 3]),
])
def test_closed_cardinality_bounds_and_duplicate_cover_intersection(profile, cover, lower, upper):
    source = ("var int: x; var int: y;"
              f"constraint fzn_global_cardinality_low_up_closed([x,y],{cover},{lower},{upper});")
    def expected(v):
        values = [v["x"], v["y"]]
        return (all(value in cover for value in values) and
                all(low <= values.count(value) <= high
                    for value, low, high in zip(cover, lower, upper)))
    assert_relation(source, {"x": [-1, 0, 2], "y": [-1, 0, 2]}, expected, profile)


@pytest.mark.parametrize("profile", PROFILES)
@pytest.mark.parametrize("constraint,truth", [
    ("gecode_global_cardinality([],[2],[0])", True),
    ("gecode_global_cardinality([],[2],[1])", False),
    ("fzn_global_cardinality_low_up_closed([],[2],[0],[0])", True),
    ("fzn_global_cardinality_low_up_closed([],[2],[1],[2])", False),
    ("fzn_global_cardinality_low_up_closed([2],[],[],[])", False),
])
def test_cardinality_empty_arrays_retain_zero_count_semantics(profile, constraint, truth):
    assert_relation("constraint " + constraint + ";", {}, lambda v: truth, profile)


@pytest.mark.parametrize("profile", PROFILES)
@pytest.mark.parametrize("offset", [-2, 5])
@pytest.mark.parametrize("weights", [[0, 2], [2, 3]])
def test_bin_packing_counts_every_item_and_bounds_even_zero_weight_bins(profile, offset, weights):
    source = ("var int: b0; var int: b1; var int: l0; var int: l1;"
              f"constraint gecode_bin_packing_load([l0,l1],[b0,b1],{weights},{offset});")
    def expected(v):
        bins = [v["b0"], v["b1"]]
        return (all(offset <= b < offset + 2 for b in bins) and
                all(v[f"l{i}"] == sum(weight for b, weight in zip(bins, weights)
                                       if b == offset + i) for i in range(2)))
    loads = sorted({-1, 0, 1, *weights, sum(weights), sum(weights) + 1})
    assert_relation(source, {"b0": list(range(offset - 1, offset + 3)),
                             "b1": list(range(offset - 1, offset + 3)),
                             "l0": loads, "l1": loads}, expected, profile)


@pytest.mark.parametrize("profile", PROFILES)
def test_bin_packing_repeated_bin_alias_keeps_both_weights(profile):
    source = ("var int: b; var int: l0; var int: l1;"
              "constraint gecode_bin_packing_load([l0,l1],[b,b],[2,3],4);")
    assert_relation(source, {"b": [3, 4, 5, 6], "l0": [0, 2, 3, 5], "l1": [0, 2, 3, 5]},
                    lambda v: ((v["b"] == 4 and v["l0"] == 5 and v["l1"] == 0) or
                               (v["b"] == 5 and v["l0"] == 0 and v["l1"] == 5)), profile)


@pytest.mark.parametrize("profile", PROFILES)
def test_bin_packing_no_items_still_fixes_every_load_to_zero(profile):
    assert_relation("var int: l0; var int: l1;"
                    "constraint gecode_bin_packing_load([l0,l1],[],[],-2);",
                    {"l0": [-1, 0, 1], "l1": [-1, 0, 1]},
                    lambda v: v["l0"] == v["l1"] == 0, profile)


@pytest.mark.parametrize("profile", PROFILES)
def test_nvalue_counts_values_not_occurrences_or_variable_names(profile):
    source = "var int: x; var int: y; var int: n; constraint fzn_nvalue(n,[x,y,x,5]);"
    assert_relation(source, {"x": [-1, 0, 5], "y": [-1, 0, 5], "n": [-1, 0, 1, 2, 3, 4]},
                    lambda v: v["n"] == len({v["x"], v["y"], 5}), profile)


@pytest.mark.parametrize("profile", PROFILES)
@pytest.mark.parametrize("array,count", [("[]", 0), ("[7]", 1), ("[7,7,7]", 1), ("[-3,7,-3]", 2)])
def test_nvalue_empty_and_literal_arrays(profile, array, count):
    assert_relation("var int: n; constraint fzn_nvalue(n," + array + ");",
                    {"n": [-1, 0, 1, 2, 3]}, lambda v: v["n"] == count, profile)


def is_single_cycle(values, offset):
    domain = set(range(offset, offset + len(values)))
    if set(values) != domain:
        return False
    seen = set()
    node = offset
    while node not in seen:
        seen.add(node)
        node = values[node - offset]
    return node == offset and seen == domain


@pytest.mark.parametrize("profile", PROFILES)
@pytest.mark.parametrize("offset,size", [(0, 1), (7, 1), (2**80 + 9, 1), (3, 2), (2, 3), (0, 4)])
def test_circuit_is_one_cycle_with_gecode_singleton_semantics(profile, offset, size):
    names = [f"s{i}" for i in range(size)]
    source = "".join(f"var int: {name};" for name in names)
    source += f"constraint gecode_circuit({offset},[" + ",".join(names) + "] );"
    values = list(range(offset, offset + size)) if size == 4 else list(range(offset - 1, offset + size + 1))
    assert_relation(source, {name: values for name in names},
                    lambda v: is_single_cycle([v[name] for name in names], offset), profile)


@pytest.mark.parametrize("profile", PROFILES)
def test_circuit_repeated_successor_alias_cannot_form_two_node_cycle(profile):
    assert_relation("var int: s; constraint gecode_circuit(0,[s,s]);",
                    {"s": [-1, 0, 1, 2]}, lambda v: False, profile)


@pytest.mark.parametrize("profile", PROFILES)
@pytest.mark.parametrize("array", ["[x,y,z]", "[x,y,x]", "[x,x,y]"])
def test_increasing_is_nonstrict_and_preserves_array_order(profile, array):
    names = array.strip("[]").split(",")
    source = "var int: x; var int: y; var int: z; constraint fzn_increasing_int(" + array + ");"
    assert_relation(source, {"x": [-2, 0, 3], "y": [-2, 0, 3], "z": [-2, 0, 3]},
                    lambda v: all(v[a] <= v[b] for a, b in zip(names, names[1:])), profile)


@pytest.mark.parametrize("profile", PROFILES)
@pytest.mark.parametrize("array,truth", [("[]", True), ("[5]", True), ("[-2,-2,4]", True), ("[4,-2]", False)])
def test_increasing_empty_singleton_and_constant_relations(profile, array, truth):
    assert_relation("constraint fzn_increasing_int(" + array + ");", {}, lambda v: truth, profile)


@pytest.mark.parametrize("profile", PROFILES)
@pytest.mark.parametrize("rows,columns", [("{}", "4..5"), ("1..0", "4..5"), ("-2..-1", "{}")])
def test_element2d_empty_axis_is_an_empty_relation(profile, rows, columns):
    source = ("var int: row; var int: col; var int: out;"
              f"constraint gecode_int_element2d(row,col,[],{rows},{columns},out);")
    assert_relation(source, {"row": [-2, 0, 4], "col": [-2, 0, 4], "out": [-1, 0, 1]},
                    lambda v: False, profile)


@pytest.mark.parametrize("profile", PROFILES)
def test_element2d_set_parameter_aliases_keep_wide_lower_bounds(profile):
    start = 2**80 + 7
    source = ("var int: row; var int: col; var int: out;"
              f"set of int: original = {start}..{start + 1};"
              "set of int: rows = original; set of int: cols = {-3};"
              "constraint gecode_int_element2d(row,col,[7,9],rows,cols,out);")
    assert_relation(source, {"row": [start - 1, start, start + 1, start + 2],
                             "col": [-4, -3, -2], "out": [7, 9, 11]},
                    lambda v: v["row"] in (start, start + 1) and v["col"] == -3 and
                    v["out"] == [7, 9][v["row"] - start], profile)


@pytest.mark.parametrize("profile", PROFILES)
@pytest.mark.parametrize("items,weights,truth", [("[]", "[]", True), ("[0]", "[0]", False), ("[0]", "[2]", False)])
def test_bin_packing_empty_load_has_no_valid_bin_even_for_zero_weight(profile, items, weights, truth):
    assert_relation(f"constraint gecode_bin_packing_load([],{items},{weights},0);",
                    {}, lambda v: truth, profile)


NEGATIVE_POLARITY_CASES = [
    ("var int: i; var bool: value;", "gecode_bool_element", "i,4,[true,false],value",
     {"i": [3, 4, 5, 6], "value": [False, True]},
     lambda v: v["i"] in (4, 5) and v["value"] == [True, False][v["i"] - 4]),
    ("var int: row; var int: col; var int: out;", "gecode_int_element2d",
     "row,col,[10,20],-1..-1,4..5,out",
     {"row": [-2, -1, 0], "col": [3, 4, 5, 6], "out": [10, 20, 30]},
     lambda v: v["row"] == -1 and v["col"] in (4, 5) and
     v["out"] == [10, 20][v["col"] - 4]),
    ("var int: x; var int: count;", "gecode_global_cardinality", "[x],[2],[count]",
     {"x": [1, 2, 3], "count": [-1, 0, 1, 2]},
     lambda v: v["count"] == int(v["x"] == 2)),
    ("var int: x;", "fzn_global_cardinality_low_up_closed", "[x],[2],[1],[1]",
     {"x": [1, 2, 3]}, lambda v: v["x"] == 2),
    ("var int: b; var int: load;", "gecode_bin_packing_load", "[load],[b],[0],5",
     {"b": [4, 5, 6], "load": [-1, 0, 1]}, lambda v: v["b"] == 5 and v["load"] == 0),
    ("var int: x; var int: n;", "fzn_nvalue", "n,[x,0]",
     {"x": [-1, 0, 1], "n": [-1, 0, 1, 2, 3]}, lambda v: v["n"] == len({v["x"], 0})),
    ("var int: x; var int: y;", "gecode_circuit", "5,[x,y]",
     {"x": [4, 5, 6, 7], "y": [4, 5, 6, 7]}, lambda v: v["x"] == 6 and v["y"] == 5),
    ("var int: x; var int: y;", "fzn_increasing_int", "[x,y]",
     {"x": [-1, 0, 1], "y": [-1, 0, 1]}, lambda v: v["x"] <= v["y"]),
]


@pytest.mark.parametrize("profile", PROFILES)
@pytest.mark.parametrize("mode", ["_reif", "_imp"])
@pytest.mark.parametrize("declarations,name,args,domains,relation", NEGATIVE_POLARITY_CASES,
                         ids=[row[1] for row in NEGATIVE_POLARITY_CASES])
def test_false_guards_keep_the_entire_global_relation_under_negative_polarity(
        profile, mode, declarations, name, args, domains, relation):
    source = declarations + f"constraint {name}{mode}({args},false);"
    assert_relation(source, domains,
                    lambda v: not relation(v) if mode == "_reif" else True, profile)


VALID_ARGUMENTS = [
    ("gecode_bool_element", ["1", "1", "[true,false]", "true"]),
    ("gecode_int_element2d", ["1", "1", "[3]", "1..1", "1..1", "3"]),
    ("gecode_global_cardinality", ["[1]", "[1]", "[1]"]),
    ("fzn_global_cardinality_low_up_closed", ["[1]", "[1]", "[0]", "[1]"]),
    ("gecode_bin_packing_load", ["[1]", "[1]", "[1]", "1"]),
    ("fzn_nvalue", ["1", "[1]"]),
    ("gecode_circuit", ["1", "[1]"]),
    ("fzn_increasing_int", ["[1]"]),
]


@pytest.mark.parametrize("name,args", VALID_ARGUMENTS, ids=[row[0] for row in VALID_ARGUMENTS])
@pytest.mark.parametrize("change", ["missing", "extra"])
def test_globals_reject_wrong_arity(name, args, change):
    bad = args[:-1] if change == "missing" else args + ["0"]
    result = sp.translate(source="constraint " + name + "(" + ",".join(bad) + "); solve satisfy;",
                          language="flatzinc")
    assert not result.ok
    assert result.diagnostic_items


@pytest.mark.parametrize("call", [
    "gecode_bool_element(true,0,[true],false)",
    "gecode_bool_element(0,false,[true],false)",
    "gecode_bool_element(0,i,[true],false)",
    "gecode_bool_element(0,0,[1],false)",
    "gecode_bool_element(0,0,[true],1)",
    "gecode_int_element2d(true,1,[1],1..1,1..1,1)",
    "gecode_int_element2d(1,false,[1],1..1,1..1,1)",
    "gecode_int_element2d(1,1,[true],1..1,1..1,1)",
    "gecode_int_element2d(1,1,[1],[1],1..1,1)",
    "gecode_int_element2d(1,1,[1],s,1..1,1)",
    "gecode_int_element2d(1,1,[1],1..1,1..1,true)",
    "gecode_global_cardinality([true],[1],[1])",
    "gecode_global_cardinality([1],[false],[1])",
    "gecode_global_cardinality([1],[i],[1])",
    "gecode_global_cardinality([1],[1],[true])",
    "fzn_global_cardinality_low_up_closed([true],[1],[0],[1])",
    "fzn_global_cardinality_low_up_closed([1],[false],[0],[1])",
    "fzn_global_cardinality_low_up_closed([1],[1],[true],[1])",
    "fzn_global_cardinality_low_up_closed([1],[1],[0],[i])",
    "gecode_bin_packing_load([true],[1],[1],1)",
    "gecode_bin_packing_load([1],[false],[1],1)",
    "gecode_bin_packing_load([1],[1],[i],1)",
    "gecode_bin_packing_load([1],[1],[1],true)",
    "fzn_nvalue(true,[1])",
    "fzn_nvalue(1,[true])",
    "gecode_circuit(true,[1])",
    "gecode_circuit(i,[1])",
    "gecode_circuit(1,[true])",
    "fzn_increasing_int([true,false])",
])
def test_globals_reject_wrong_sorts_and_variable_parameters(call):
    result = sp.translate(source="var int: i; var set of 1..2: s; constraint " + call + "; solve satisfy;",
                          language="flatzinc")
    assert not result.ok
    assert result.diagnostic_items


@pytest.mark.parametrize("call", [
    "gecode_int_element2d(1,1,[1,2,3],1..2,1..2,1)",
    "gecode_int_element2d(1,1,[1,2,3,4,5],1..2,1..2,1)",
    "gecode_int_element2d(1,1,[1,2],{1,3},1..1,1)",
    "gecode_int_element2d(1,1,[1,2],1..1,{1,3},1)",
    "gecode_global_cardinality([1],[1,2],[1])",
    "fzn_global_cardinality_low_up_closed([1],[1,2],[0],[1,1])",
    "fzn_global_cardinality_low_up_closed([1],[1],[0],[1,2])",
    "gecode_bin_packing_load([1],[1,1],[1],1)",
    "gecode_bin_packing_load([1],[1],[-1],1)",
    "gecode_circuit(0,[])",
    "gecode_circuit(-1,[-1])",
])
def test_globals_reject_invalid_shapes_and_gecode_preconditions(call):
    result = sp.translate(source="constraint " + call + "; solve satisfy;", language="flatzinc")
    assert not result.ok
    assert result.diagnostic_items
