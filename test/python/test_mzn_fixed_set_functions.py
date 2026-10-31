"""Focused source fixtures for fixed-set and double-dollar user functions.

Checks concrete and polymorphic set types, finite recursion, and source-level
function constraints through the public translation API.
"""

import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


def _check(source):
    translated = sp.translate(source=source, language="minizinc")
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.set(timeout=5000)
    solver.add(*z3.parse_smt2_string(
        translated.to_smt2(sp.OmtDialect.Z3), ctx=context))
    status = solver.check()
    assert status != z3.unknown, solver.reason_unknown()
    return status


def _reject(source):
    result = sp.translate(source=source, language="minizinc")
    assert not result.ok
    assert result.diagnostic_items


def test_polymorphic_fixed_set_result_unifies_scalar_and_set_enum():
    source = """
enum NODE = {a, b, c};
function set of $$T: extend($$T: value, set of $$T: seen) =
  seen union {value};
constraint extend(b, {a}) = {a, b};
constraint not (extend(b, {a}) = {a});
solve satisfy;
"""
    assert _check(source) == z3.sat


def test_empty_polymorphic_set_arguments_and_results_use_call_context():
    source = """
enum NODE = {a, b};
function set of $$T: insert(set of $$T: values, $$T: value) =
  values union {value};
function set of $$T: empty_for($$T: value) = {};
constraint insert({}, b) = {b};
constraint empty_for(a) = {};
solve satisfy;
"""
    assert _check(source) == z3.sat


def test_double_dollar_scalar_unifies_bool_with_int_via_minizinc_coercion():
    source = """
function bool: same($$T: left, $$T: right) = left = right;
constraint same(true, 1);
solve satisfy;
"""
    assert _check(source) == z3.sat


@pytest.mark.parametrize("value", ["2.5", '"node"'])
def test_double_dollar_scalar_rejects_float_and_string(value):
    _reject(f"""
function bool: same($$T: left, $$T: right) = left = right;
constraint same({value}, {value});
solve satisfy;
""")


@pytest.mark.parametrize("typ,values,value", [("bool", "[true, false]", "true"),
                                               ("int", "[1, 2]", "1")])
def test_double_dollar_array_element_and_scalar_unify_as_int(typ, values, value):
    source = f"""
array[1..2] of {typ}: values = {values};
function bool: first_is(array[int] of $$T: items, $$T: item) =
  items[1] = item;
constraint first_is(values, {value});
solve satisfy;
"""
    assert _check(source) == z3.sat


@pytest.mark.parametrize("typ,values,value", [("float", "[1.5, 2.5]", "1.5"),
                                               ("string", '["left", "right"]', '"left"')])
def test_double_dollar_array_element_rejects_float_and_string(typ, values, value):
    _reject(f"""
array[1..2] of {typ}: values = {values};
function bool: first_is(array[int] of $$T: items, $$T: item) =
  items[1] = item;
constraint first_is(values, {value});
solve satisfy;
""")


def test_array_index_element_and_scalar_share_one_nominal_type_variable():
    source = """
enum NODE = {a, b, c};
array[NODE] of NODE: successor = [b, c, a];
function set of $$N: step($$N: node, set of $$N: seen,
                          array[$$N] of $$N: next) =
  seen union {next[node]};
constraint step(a, {a}, successor) = {a, b};
constraint not (step(a, {a}, successor) = {a, c});
solve satisfy;
"""
    assert _check(source) == z3.sat


def test_recursive_fixed_set_function_uses_generic_sets_and_arrays():
    # This is the recursive helper shape from the official Hitori model. A
    # call unfolds over the finite `seen` set until there are no fresh adjacent
    # nodes, while each invocation receives the same typed array arguments.
    source = """
enum NODE = {a, b, c};
enum EDGE = {e0, e1};
array[EDGE] of NODE: from = [a, b];
array[EDGE] of NODE: to = [b, c];
array[NODE] of bool: ns = [true, true, true];
array[EDGE] of bool: es = [true, true];
function set of $$N: reachable_nodes(
  $$N: node, set of $$N: seen,
  array[$$E] of $$N: from, array[$$E] of $$N: to,
  array[$$N] of bool: ns, array[$$E] of bool: es) = let {
    any: adjacent = {n | i in index_set(es)
                       where es[i] /\\ (from[i] = node \\/ to[i] = node),
                       n in [from[i], to[i]] where n != node} diff seen;
    any: seen_next = seen union adjacent;
  } in seen union {x | adj in adjacent,
                        x in reachable_nodes(adj, seen_next, from, to, ns, es)};
constraint reachable_nodes(a, {a}, from, to, ns, es) = {a, b, c};
constraint not (reachable_nodes(a, {a}, from, to, ns, es) = {a, b});
solve satisfy;
"""
    assert _check(source) == z3.sat


def test_named_set_return_sort_shorthand_is_a_fixed_function_with_domain():
    source = """
set of int: ROW = 1..3;
ROW: identity(ROW: row) = row;
constraint identity(2) = 2;
solve satisfy;
"""
    assert _check(source) == z3.sat


def test_named_set_return_sort_rejects_fixed_result_outside_domain():
    source = """
set of int: ROW = 1..3;
ROW: identity(int: value) = value;
constraint identity(4) = 4;
solve satisfy;
"""
    _reject(source)


def test_array_type_variable_unification_preserves_distinct_enum_identity():
    source = """
enum NODE = {a, b};
enum EDGE = {e0, e1};
array[EDGE] of NODE: next = [a, b];
function bool: same_axis_and_element(array[$$T] of $$T: values) =
  values[a] = a;
constraint same_axis_and_element(next);
solve satisfy;
"""
    result = sp.translate(source=source, language="minizinc")
    assert not result.ok
    assert any("type variable" in d.message for d in result.diagnostic_items)


def test_fixed_set_arguments_require_matching_enum_types():
    source = """
enum NODE = {a, b};
enum EDGE = {e0, e1};
function set of $$T: extend($$T: value, set of $$T: seen) =
  seen union {value};
constraint extend(a, {e0}) = {a, e0};
solve satisfy;
"""
    result = sp.translate(source=source, language="minizinc")
    assert not result.ok
    assert result.diagnostic_items


def test_concrete_int_set_formal_accepts_enum_set_by_ordinal_coercion():
    source = """
enum NODE = {a, b};
function set of int: keep(set of int: values) = values union {1};
constraint keep({a}) = {1};
solve satisfy;
"""
    assert _check(source) == z3.sat


def test_ambiguous_empty_generic_set_is_rejected():
    source = """
function set of $$T: empty_for(set of $$T: values) = {};
constraint empty_for({}) = {};
solve satisfy;
"""
    result = sp.translate(source=source, language="minizinc")
    assert not result.ok
    assert result.diagnostic_items


def test_function_with_set_result_cannot_be_used_as_scalar_expression():
    source = """
function set of int: singleton(int: x) = {x};
constraint singleton(1) = 1;
solve satisfy;
"""
    _reject(source)


def test_variable_set_formal_is_explicitly_rejected():
    source = """
function bool: contains(var set of int: values, int: item) = item in values;
constraint contains({1}, 1);
solve satisfy;
"""
    _reject(source)


def test_non_decreasing_recursive_set_generator_fails_at_existing_depth_budget():
    source = """
function set of int: loop(set of int: seen) =
  {value | value in loop(seen)};
constraint loop({1}) = {1};
solve satisfy;
"""
    result = sp.translate(source=source, language="minizinc")
    assert not result.ok
    assert result.diagnostic_items
