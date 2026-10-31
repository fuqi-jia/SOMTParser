"""Typed enum-set data: exact Boolean relations, without depending on tag IDs."""

import json
import pytest
import z3
import somtparser as sp


def _translate(tmp_path, source, data, *, dzn=False):
    path = tmp_path / ("values.dzn" if dzn else "values.json")
    path.write_text(data if dzn else json.dumps(data, indent=2), encoding="utf-8")
    result = sp.translate(source=source, data=[str(path)], language="minizinc")
    return result, path


def _exact_booleans(result, values):
    assert result.ok, [d.message for d in result.diagnostic_items]
    actual = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    expected = z3.And(*[z3.Bool(name) == value for name, value in values.items()])
    solver = z3.Solver()
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat
    solver = z3.Solver()
    solver.add(actual)
    assert solver.check() == z3.sat


@pytest.mark.parametrize("tagged", [False, True])
@pytest.mark.parametrize("forward", [False, True])
def test_sparse_enum_set_arrays_preserve_every_member(tmp_path, tagged, forward):
    wrap = (lambda value: {"e": value}) if tagged else (lambda value: value)
    data = {"allowed": [{"set": [wrap("Red"), wrap("Blue"), wrap("Red")]},
                        {"set": []}, {"set": [wrap("Green")]}], "label": "Red"}
    enum = "enum COLOR = {Red, Green, Blue};"
    body = """
        array[-1..1] of set of COLOR: allowed;
        string: label;
        var bool: red;
        var bool: blue;
        var bool: green;
        var bool: empty;
        constraint red <-> Red in allowed[-1];
        constraint blue <-> Blue in allowed[-1];
        constraint green <-> Green in allowed[-1];
        constraint empty <-> card(allowed[0]) = 0;
        constraint Green in allowed[1];
        constraint label = "Red";
    """
    source = (body + enum if forward else enum + body) + "solve satisfy;"
    result, _ = _translate(tmp_path, source, data)
    _exact_booleans(result, {"red": True, "blue": True, "green": False, "empty": True})


@pytest.mark.parametrize("data,dzn", [
    ({"s": {"set": ["Red", "Blue"]}}, False),
    ({"s": {"set": [{"e": "Red"}, {"e": "Blue"}]}}, False),
    ({"s": ["Red", "Blue"]}, False),
    ("s = {Red, Blue};", True),
])
def test_scalar_enum_sets_bind_after_type_is_known(tmp_path, data, dzn):
    source = """
        set of COLOR: s;
        var bool: red; var bool: green;
        constraint red <-> Red in s;
        constraint green <-> Green in s;
        enum COLOR = {Red, Green, Blue};
        solve satisfy;
    """
    result, _ = _translate(tmp_path, source, data, dzn=dzn)
    _exact_booleans(result, {"red": True, "green": False})


def test_dzn_member_lists_define_enums_and_set_arrays(tmp_path):
    source = """
        array[COLOR] of set of COLOR: allowed;
        var bool: yes; var bool: no;
        constraint yes <-> Blue in allowed[Red];
        constraint no <-> Red in allowed[Blue];
        enum COLOR;
        solve satisfy;
    """
    data = "COLOR={Red,Green,Blue}; allowed=[{Blue},{Red,Green},{}];"
    result, _ = _translate(tmp_path, source, data, dzn=True)
    _exact_booleans(result, {"yes": True, "no": False})


def test_json_member_lists_define_enums_and_set_arrays(tmp_path):
    source = """
        array[COLOR] of set of COLOR: allowed;
        var bool: yes;
        constraint yes <-> Blue in allowed[Red];
        enum COLOR;
        solve satisfy;
    """
    result, _ = _translate(tmp_path, source, {
        "allowed": [{"set": ["Blue"]}, {"set": []}, {"set": []}],
        "COLOR": ["Red", "Green", "Blue"],
    })
    _exact_booleans(result, {"yes": True})


@pytest.mark.parametrize("tagged", [False, True])
def test_nested_json_member_lists_coerce_to_enum_set_arrays(tmp_path, tagged):
    wrap = (lambda value: {"e": value}) if tagged else (lambda value: value)
    source = """
        array[0..1]of set of COLOR:a;enum COLOR={Red,Green,Blue};
        var bool:b;var bool:c;
        constraint b <-> Blue in a[0];constraint c <-> Red in a[1];
        solve satisfy;
    """
    result, _ = _translate(tmp_path, source,
                          {"a": [[wrap("Red"), wrap("Blue")], [wrap("Green"), wrap("Green")]]})
    _exact_booleans(result, {"b": True, "c": False})


def test_integer_list_does_not_masquerade_as_enum_set_array(tmp_path):
    result, _ = _translate(tmp_path, "array[1..1]of set of COLOR:a;"
                          "enum COLOR={Red,Blue};solve satisfy;", {"a": [[1, 2]]})
    assert not result.ok


@pytest.mark.parametrize("assignment", [
    "s={Red,Blue};", "a=[{Red,Blue},{}];",
])
def test_model_assignments_reread_after_declaration_preserve_binding(assignment):
    declaration = "set of COLOR:s;" if assignment.startswith("s=") else "array[1..2]of set of COLOR:a;"
    term = "s" if assignment.startswith("s=") else "a[1]"
    source = (declaration + assignment + "enum COLOR={Red,Green,Blue};"
              "var bool:b;constraint b <-> (Red in " + term + " /\\ not (Green in "
              + term + "));solve satisfy;")
    result = sp.translate(source=source, language="minizinc")
    _exact_booleans(result, {"b": True})


def test_include_frames_retain_predicates_and_forward_enum_definitions(tmp_path):
    (tmp_path / "types.mzn").write_text("enum COLOR={Red,Green,Blue};")
    (tmp_path / "helpers.mzn").write_text(
        'predicate allowed(int:i) = Blue in a[i]; include "types.mzn";')
    model = tmp_path / "model.mzn"
    # Predicate declarations must precede calls in the current frontend. The
    # enum declaration still occurs after the array using COLOR.
    model.write_text('array[1..2]of set of COLOR:a;include "helpers.mzn";'
                     'var bool:b;constraint b <-> allowed(1);solve satisfy;')
    data = tmp_path / "values.json"
    data.write_text(json.dumps({"a": [{"set": ["Blue"]}, {"set": []}]}))
    result = sp.translate(path=str(model), data=[str(data)], language="minizinc")
    _exact_booleans(result, {"b": True})


@pytest.mark.parametrize("value", ["Other", "Missing", 1, True])
@pytest.mark.parametrize("array", [False, True])
def test_wrong_nominal_type_is_an_error_with_original_json_parameter_location(tmp_path, value, array):
    # One preceding member and several blank lines distinguish a real JSON
    # location from the second synthetic assignment line.
    payload = [{"set": [value]}] if array else {"set": [value]}
    path = tmp_path / "bad.json"
    path.write_text('{\n  "label": "Red",\n\n\n\n  "bad": ' + json.dumps(payload) + '\n}\n')
    declaration = "array[1..1]of set of COLOR:bad;" if array else "set of COLOR:bad;"
    result = sp.translate(source=declaration + "string:label;enum COLOR={Red,Blue};"
                          "enum DIFFERENT={Other};solve satisfy;",
                          data=[str(path)], language="minizinc")
    assert not result.ok
    errors = [d for d in result.diagnostic_items if d.file == str(path)]
    assert errors, [d.message for d in result.diagnostic_items]
    assert any(d.line == 6 and d.column == 3 for d in errors)


def test_plain_json_strings_do_not_initialize_integer_sets(tmp_path):
    result, _ = _translate(tmp_path,
                          "set of int:s;enum COLOR={Red,Blue};solve satisfy;",
                          {"s": {"set": ["Red"]}})
    assert not result.ok


def test_integer_set_arrays_keep_ranges_holes_and_empty_cells(tmp_path):
    result, _ = _translate(tmp_path, """
        array[0..1]of set of int:a;
        var bool:lo;var bool:hole;var bool:hi;var bool:empty;
        constraint lo <-> -2 in a[0];constraint hi <-> 4 in a[0];
        constraint hole <-> 2 in a[0];constraint empty <-> card(a[1])=0;
        solve satisfy;
    """, {"a": [{"set": [[-2, 0], 4]}, {"set": []}]})
    _exact_booleans(result, {"lo": True, "hole": False, "hi": True, "empty": True})


def test_data_set_can_reference_a_later_model_integer_parameter(tmp_path):
    result, _ = _translate(tmp_path, """
        set of int:s;int:n=7;var bool:b;
        constraint b <-> 7 in s;solve satisfy;
    """, "s={n};", dzn=True)
    _exact_booleans(result, {"b": True})


@pytest.mark.parametrize("size,expected", [(0, z3.unsat), (1, z3.sat)])
def test_forward_enum_set_array_keeps_its_typed_nonempty_cell(tmp_path, size, expected):
    # Typed forward binding must retain Red rather than inventing an empty
    # cell. Both outcomes were checked with MiniZinc 2.9.4 and Gecode.
    result, _ = _translate(tmp_path, f"""
        constraint card(a[1])={size};
        array[1..1]of set of COLOR:a;
        enum COLOR={{Red}};solve satisfy;
    """, {"a": [{"set": ["Red"]}]})
    assert result.ok, [d.message for d in result.diagnostics]
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.add(z3.parse_smt2_string(result.to_smt2(), ctx=context))
    assert solver.check() == expected


@pytest.mark.parametrize("source", [
    "enum COLOR={Red};enum COLOR={Blue};solve satisfy;",
    "enum COLOR={Red};enum OTHER={Red};solve satisfy;",
    "enum COLOR={Red,Red};solve satisfy;",
    "set of COLOR:s={Other};enum COLOR={Red};enum OTHER={Other};solve satisfy;",
    "array[1..1]of set of COLOR:a=[{Other}];enum COLOR={Red};enum OTHER={Other};solve satisfy;",
    'set of COLOR:s={"Red"};enum COLOR={Red};solve satisfy;',
])
def test_forward_elaboration_does_not_hide_invalid_models(source):
    result = sp.translate(source=source, language="minizinc")
    assert not result.ok
    assert all("E_INTERNAL" not in str(d.code) for d in result.diagnostic_items)
