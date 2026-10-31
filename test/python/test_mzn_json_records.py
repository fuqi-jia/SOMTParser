"""Static acceptance tests for typed MiniZinc records from JSON data.

This candidate covers named and nested records, fixed record arrays, and
record lists, including finite list-valued fields represented with frontend
shape metadata.
"""
import json

import pytest
import z3

import somtparser as sp


MODEL = """
enum Shade = {red, blue};
type Detail = record(int: offset, string: label);
type Entry = record(int: units, Shade: shade, Detail: detail, bool: enabled);
Entry: entry;
var int: total;
constraint total = entry.units + entry.detail.offset;
constraint entry.shade = blue;
constraint entry.detail.label = "nested";
constraint entry.enabled;
solve satisfy;
"""


def _translate(tmp_path, obj):
    data = tmp_path / "record.json"
    data.write_text(json.dumps(obj), encoding="utf-8")
    return sp.translate(source=MODEL, language="minizinc", data=[str(data)])


def _assert_exact_total(formula, total, expected):
    """For these fixtures, total is the sole free value in the relation."""
    solver = z3.Solver()
    solver.add(formula)
    assert solver.check() == z3.sat
    solver = z3.Solver()
    solver.add(z3.Xor(formula, total == expected))
    assert solver.check() == z3.unsat


def test_json_record_fields_bind_by_name_and_nested_selection_is_typed(tmp_path):
    # The JSON order deliberately differs at both record levels from the
    # declared order. A positional flattening would swap incompatible fields.
    result = _translate(tmp_path, {"entry": {
        "enabled": True,
        "detail": {"label": "nested", "offset": 5},
        "shade": {"e": "blue"},
        "units": 2,
    }})
    assert result.ok, [d.message for d in result.diagnostic_items]
    formula = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    _assert_exact_total(formula, z3.Int("total"), 7)


@pytest.mark.parametrize(("record", "diagnostic"), [
    ({"units": 2, "shade": "blue", "detail": {"offset": 5, "label": "nested"}},
     "missing field 'enabled'"),
    ({"units": "two", "shade": "blue", "detail": {"offset": 5, "label": "nested"},
      "enabled": True}, "wrong type for record field 'units'"),
    ({"units": 2, "shade": "green", "detail": {"offset": 5, "label": "nested"},
      "enabled": True}, "not a member of enum 'Shade'"),
    ({"units": 2, "shade": "blue", "detail": {"offset": 5, "label": "nested"},
      "enabled": True, "extra": 9}, "unknown field 'extra'"),
])
def test_typed_record_binding_rejects_missing_unknown_and_mistyped_fields(
        tmp_path, record, diagnostic):
    result = _translate(tmp_path, {"entry": record})
    assert not result.ok
    assert any(diagnostic in d.message for d in result.diagnostic_items)


def test_duplicate_record_field_is_rejected_by_json_reader(tmp_path):
    data = tmp_path / "duplicate.json"
    data.write_text(
        '{"entry":{"units":1,"units":2,"shade":"blue",'
        '"detail":{"offset":5,"label":"nested"},"enabled":true}}',
        encoding="utf-8")
    result = sp.translate(source=MODEL, language="minizinc", data=[str(data)])
    assert not result.ok
    assert any("duplicate JSON record field 'units'" in d.message
               for d in result.diagnostic_items)


@pytest.mark.parametrize("declaration", [
    "array[1..2] of Entry: entries;",
    "list of Entry: entries;",
])
def test_record_arrays_and_lists_keep_cell_order_and_field_values(tmp_path, declaration):
    source = """
type Entry = record(int: units, string: label);
""" + declaration + """
var int: total;
constraint total = entries[1].units + entries[2].units;
constraint total = sum(e in entries)(e.units);
constraint entries[1].label = "first" /\\ entries[2].label = "second";
solve satisfy;
"""
    data = tmp_path / "records.json"
    data.write_text(json.dumps({"entries": [
        {"label": "first", "units": 3},
        {"units": 4, "label": "second"},
    ]}), encoding="utf-8")
    result = sp.translate(source=source, language="minizinc", data=[str(data)])
    assert result.ok, [d.message for d in result.diagnostic_items]
    formula = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    _assert_exact_total(formula, z3.Int("total"), 7)


@pytest.mark.parametrize("nested", [False, True])
@pytest.mark.parametrize("declaration", ["array[1..2] of Patient", "list of Patient"])
def test_indexed_record_list_fields_drive_nested_generators(tmp_path, nested, declaration):
    field = "details.incompatible_room_ids" if nested else "incompatible_room_ids"
    schema = ("type Details = record(list of string: incompatible_room_ids);"
              "type Patient = record(int: index, Details: details);") if nested else (
              "type Patient = record(int: index, list of string: incompatible_room_ids);")
    source = schema + declaration + ":patients;" + """
array[1..3] of string: room_ids = ["r1", "r2", "r3"];
array[1..3] of var 0..9: x;
constraint forall(p in 1..2, room_id in patients[p].""" + field + """,
                  r in 1..3 where room_ids[r] = room_id)(x[r] != p);
solve satisfy;
"""
    records = []
    for index, rooms in [(1, ["r2", "r3"]), (2, ["r1"])]:
        fields = {"incompatible_room_ids": rooms}
        records.append({"index": index, **({"details": fields} if nested else fields)})
    data = tmp_path / "patients.json"
    data.write_text(json.dumps({"patients": records}), encoding="utf-8")
    result = sp.translate(source=source, language="minizinc", data=[str(data)])
    assert result.ok, [d.message for d in result.diagnostic_items]
    formula = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    x = z3.Array("x", z3.IntSort(), z3.IntSort())
    expected = z3.And(*[z3.And(x[i] >= 0, x[i] <= 9) for i in range(1, 4)],
                      x[1] != 2, x[2] != 1, x[3] != 1)
    solver = z3.Solver()
    solver.add(z3.Xor(formula, expected))
    assert solver.check() == z3.unsat


def test_inline_record_array_matches_cgt_declaration_and_generator_field_access(tmp_path):
    source = """
enum Trade = {buy, sell};
array[int] of record(int: units, Trade: action): trades;
var int: bought_units;
constraint bought_units = sum(t in trades where t.action = buy)(t.units);
solve satisfy;
"""
    data = tmp_path / "trades.json"
    data.write_text(json.dumps({"trades": [
        {"action": "buy", "units": 3},
        {"units": 5, "action": "sell"},
        {"units": 4, "action": "buy"},
    ]}), encoding="utf-8")
    result = sp.translate(source=source, language="minizinc", data=[str(data)])
    assert result.ok, [d.message for d in result.diagnostic_items]
    formula = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    _assert_exact_total(formula, z3.Int("bought_units"), 7)


@pytest.mark.parametrize("threshold, expected", [(0, 10), (4, 7), (20, 0)])
def test_local_record_lists_filter_and_restore_shadowed_outer_list(tmp_path, threshold, expected):
    source = f"""
type Entry = record(int: units);
list of Entry: entries;
var int: selected;
var int: outer_total;
constraint selected = let {{
  list of Entry: entries = [e | e in entries where e.units >= {threshold}],
  list of Entry: copied = [e | e in entries]
}} in sum(e in copied)(e.units);
constraint outer_total = sum(e in entries)(e.units);
solve satisfy;
"""
    data = tmp_path / "local-records.json"
    data.write_text(json.dumps({"entries": [{"units": 3}, {"units": 7}]}))
    result = sp.translate(source=source, language="minizinc", data=[str(data)])
    assert result.ok, [d.message for d in result.diagnostic_items]
    formula = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    reference = z3.And(z3.Int("selected") == expected, z3.Int("outer_total") == 10)
    solver = z3.Solver()
    solver.add(z3.Xor(formula, reference))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("entries", [[{"units": 3}], []])
def test_local_record_list_rejects_incompatible_fields(tmp_path, entries):
    source = """
type Entry = record(int: units);
type Other = record(string: units);
list of Entry: entries;
constraint let { list of Other: wrong = [e | e in entries] } in true;
solve satisfy;
"""
    data = tmp_path / "wrong-list-type.json"
    data.write_text(json.dumps({"entries": entries}))
    result = sp.translate(source=source, language="minizinc", data=[str(data)])
    assert not result.ok
    assert any("not structurally compatible" in d.message for d in result.diagnostic_items)


def test_local_record_list_coerces_structural_aliases_and_field_order(tmp_path):
    source = """
type Entry = record(int: units, string: label);
type Alias = record(string: label, float: units);
list of Entry: entries;
var float: total;
constraint total = let { list of Alias: converted = [e | e in entries] }
                   in sum(e in converted where e.label = "selected")(e.units);
solve satisfy;
"""
    data = tmp_path / "record-list-alias.json"
    data.write_text(json.dumps({"entries": [
        {"units": 3, "label": "selected"}, {"units": 7, "label": "other"}]}))
    result = sp.translate(source=source, language="minizinc", data=[str(data)])
    assert result.ok, [d.message for d in result.diagnostic_items]
    formula = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    _assert_exact_total(formula, z3.Real("total"), 3)


def test_local_record_list_rejects_nonunit_source_index(tmp_path):
    source = """
type Entry = record(int: units);
array[2..3] of Entry: entries;
constraint let { list of Entry: local = entries } in true;
solve satisfy;
"""
    data = tmp_path / "record-list-indices.json"
    data.write_text('{"entries":[{"units":3},{"units":7}]}')
    result = sp.translate(source=source, language="minizinc", data=[str(data)])
    assert not result.ok
    assert any("indexed from 1" in d.message for d in result.diagnostic_items)


@pytest.mark.parametrize("declaration", ["var int: x;", "var 0..2: x;"])
@pytest.mark.parametrize("initializer", ["[(units: x)]", "[(units: x) | i in 1..0]"])
def test_fixed_local_record_list_rejects_decision_fields(declaration, initializer):
    source = """
type Entry = record(int: units);
""" + declaration + """
constraint let { list of Entry: entries = """ + initializer + """ }
           in sum(e in entries)(e.units) >= 0;
solve satisfy;
"""
    result = sp.translate(source=source, language="minizinc")
    assert not result.ok
    assert any("cannot depend on a decision value" in d.message for d in result.diagnostic_items)


@pytest.mark.parametrize("rooms, occupants, expected", [
    ([{"id": 1, "capacity": 7}], [], 0),
    ([], [], 0),
    ([{"id": 1, "capacity": 7}], [{"room_id": 1}], 7),
])
def test_empty_record_generator_checks_lookup_type_without_reading_a_cell(
        tmp_path, rooms, occupants, expected):
    # This is the room lookup used by the official IHTC model. An empty
    # occupant list must not execute room() on a fabricated room_id = 0.
    source = """
type Room = record(int: id, int: capacity);
type Occupant = record(int: room_id);
list of Room: rooms;
list of Occupant: occupants;
function Room: room(Occupant: o) = [r | r in rooms where r.id = o.room_id][1];
var int: total;
constraint total = sum(o in occupants)(room(o).capacity);
solve satisfy;
"""
    data = tmp_path / "room-lookup.json"
    data.write_text(json.dumps({"rooms": rooms, "occupants": occupants}))
    result = sp.translate(source=source, language="minizinc", data=[str(data)])
    assert result.ok, [d.message for d in result.diagnostic_items]
    formula = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    _assert_exact_total(formula, z3.Int("total"), expected)


@pytest.mark.parametrize("generator", ["entries", "[e | e in entries where false]"])
def test_empty_record_list_probe_preserves_nested_record_list_fields(tmp_path, generator):
    source = """
type Child = record(int: units);
type Entry = record(list of Child: children);
list of Entry: entries;
var int: total;
constraint total = sum(e in """ + generator + """)(e.children[1].units);
solve satisfy;
"""
    data = tmp_path / "nested-empty-records.json"
    data.write_text('{"entries":[]}')
    result = sp.translate(source=source, language="minizinc", data=[str(data)])
    assert result.ok, [d.message for d in result.diagnostic_items]
    formula = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    _assert_exact_total(formula, z3.Int("total"), 0)


@pytest.mark.parametrize("selection", ["[true].units", "[1].missing"])
def test_empty_record_lookup_probe_still_rejects_type_errors(tmp_path, selection):
    source = """
type Entry = record(int: units);
list of Entry: entries;
constraint sum(e in entries)([r | r in entries]""" + selection + """) = 0;
solve satisfy;
"""
    data = tmp_path / "ill-typed-empty-records.json"
    data.write_text('{"entries":[]}')
    result = sp.translate(source=source, language="minizinc", data=[str(data)])
    assert not result.ok
    assert any("Int" in d.message or "no field" in d.message for d in result.diagnostic_items)


def test_nonempty_generator_does_not_hide_missing_record_lookup(tmp_path):
    source = """
type Entry = record(int: units);
list of Entry: entries;
constraint sum(e in entries)([r | r in entries where r.units = 99][1].units) = 0;
solve satisfy;
"""
    data = tmp_path / "missing-real-record.json"
    data.write_text('{"entries":[{"units":1}]}')
    result = sp.translate(source=source, language="minizinc", data=[str(data)])
    # The pinned MiniZinc compiler closes the missing read to false at the
    # equality. It must neither reject a valid partial expression nor let the
    # record probe's placeholder zero turn this constraint into true.
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.add(z3.parse_smt2_string(result.to_smt2()))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("context", [
    "negated", "reified", "field_default", "sum_default",
    "empty_generator", "successful_lookup",
])
def test_computed_record_lookup_preserves_context(tmp_path, context):
    lookup = "[r | r in entries where r.units = 99][1].units"
    aggregate = f"sum(e in entries)({lookup})"
    entries = [{"units": 1}]
    if context == "negated":
        body = f"constraint not ({aggregate} = 0);"
        expected = z3.BoolVal(True)
    elif context == "reified":
        body = f"var bool: accepted; constraint accepted = ({aggregate} = 0);"
        expected = z3.Not(z3.Bool("accepted"))
    elif context == "field_default":
        body = f"var int: total; constraint total = sum(e in entries)(({lookup}) default 5);"
        expected = z3.Int("total") == 5
    elif context == "sum_default":
        body = f"var int: total; constraint total = ({aggregate} default 5);"
        expected = z3.Int("total") == 5
    elif context == "empty_generator":
        entries = []
        body = f"var int: total; constraint total = {aggregate};"
        expected = z3.Int("total") == 0
    else:
        entries = [{"units": 99}]
        body = f"var int: total; constraint total = {aggregate};"
        expected = z3.Int("total") == 99
    source = "type Entry = record(int: units); list of Entry: entries;" + body + "solve satisfy;"
    data = tmp_path / "record-lookup-context.json"
    data.write_text(json.dumps({"entries": entries}))
    result = sp.translate(source=source, language="minizinc", data=[str(data)])
    assert result.ok, [d.message for d in result.diagnostic_items]
    formula = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    solver = z3.Solver()
    solver.add(z3.Xor(formula, expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize(("field", "value"), [("e", "buy"), ("set", "label")])
def test_reserved_singleton_tag_names_are_typed_as_record_fields(tmp_path, field, value):
    source = f"""
type Tagged = record(string: {field});
Tagged: tagged;
constraint tagged.{field} = {json.dumps(value)};
solve satisfy;
"""
    data = tmp_path / "tag-field.json"
    data.write_text(json.dumps({"tagged": {field: value}}), encoding="utf-8")
    result = sp.translate(source=source, language="minizinc", data=[str(data)])
    assert result.ok, [d.message for d in result.diagnostic_items]
    formula = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    solver = z3.Solver()
    solver.add(formula)
    assert solver.check() == z3.sat


def test_singleton_enum_tag_can_bind_to_an_enum_record_field_named_e(tmp_path):
    source = """
enum Shade = {red, blue};
type Tagged = record(Shade: e);
Tagged: tagged;
constraint tagged.e = blue;
solve satisfy;
"""
    data = tmp_path / "enum-tag-field.json"
    data.write_text('{"tagged":{"e":"blue"}}', encoding="utf-8")
    result = sp.translate(source=source, language="minizinc", data=[str(data)])
    assert result.ok, [d.message for d in result.diagnostic_items]
    formula = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    solver = z3.Solver()
    solver.add(formula)
    assert solver.check() == z3.sat


def test_record_arrays_preserve_full_nonunit_and_enum_index_shape(tmp_path):
    source = """
enum Slot = {morning, evening};
enum Other = {first, last};
type Entry = record(int: units);
array[Slot] of Entry: entries;
var int: total;
constraint total = entries[morning].units + entries[evening].units;
solve satisfy;
"""
    data = tmp_path / "enum-record-array.json"
    data.write_text(json.dumps({"entries": [{"units": -3}, {"units": 10}]}),
                    encoding="utf-8")
    result = sp.translate(source=source, language="minizinc", data=[str(data)])
    assert result.ok, [d.message for d in result.diagnostic_items]
    formula = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    _assert_exact_total(formula, z3.Int("total"), 7)

    wrong_index = source.replace("entries[morning]", "entries[first]")
    rejected = sp.translate(source=wrong_index, language="minizinc", data=[str(data)])
    assert not rejected.ok
    assert any(d.code == sp.ErrorCode.E_TYPE
               and "expected enum 'Slot'" in d.message
               and "source type 'Other'" in d.message
               for d in rejected.diagnostic_items)


def test_negative_integer_and_real_record_cells_keep_their_numeric_values(tmp_path):
    source = """
type Limits = record(int: floor, float: offset);
Limits: limits;
var int: total;
constraint total = limits.floor;
constraint limits.offset < 0.0;
solve satisfy;
"""
    data = tmp_path / "negative-record.json"
    data.write_text(
        '{"limits":{"floor":-9223372036854775808,"offset":-0.25}}',
        encoding="utf-8")
    result = sp.translate(source=source, language="minizinc", data=[str(data)])
    assert result.ok, [d.message for d in result.diagnostic_items]
    formula = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    _assert_exact_total(formula, z3.Int("total"), -(2 ** 63))

    data.write_text(
        '{"limits":{"floor":-9223372036854775809,"offset":-0.25}}',
        encoding="utf-8")
    rejected = sp.translate(source=source, language="minizinc", data=[str(data)])
    assert not rejected.ok
    assert any("integer record field 'floor' is out of range" in d.message
               for d in rejected.diagnostic_items)


def test_record_array_at_maximum_index_does_not_reconstruct_overflowed_shape(tmp_path):
    source = """
type Entry = record(int: units);
array[9223372036854775807..9223372036854775807] of Entry: entries;
var int: total;
constraint total = entries[9223372036854775807].units;
solve satisfy;
"""
    data = tmp_path / "maximum-index.json"
    data.write_text('{"entries":[{"units":11}]}', encoding="utf-8")
    result = sp.translate(source=source, language="minizinc", data=[str(data)])
    assert result.ok, [d.message for d in result.diagnostic_items]
    formula = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    _assert_exact_total(formula, z3.Int("total"), 11)


@pytest.mark.parametrize("declaration", [
    "array[1..0] of Entry: entries;",
    "list of Entry: entries;",
])
def test_empty_record_array_and_list_are_valid_empty_sources(tmp_path, declaration):
    source = """
type Entry = record(int: units);
""" + declaration + """
array[1..0] of int: ordinary;
var int: total;
constraint total = sum(e in entries)(e.units);
constraint length(ordinary) = 0;
solve satisfy;
"""
    data = tmp_path / "empty-records.json"
    data.write_text('{"entries":[],"ordinary":[]}', encoding="utf-8")
    result = sp.translate(source=source, language="minizinc", data=[str(data)])
    assert result.ok, [d.message for d in result.diagnostic_items]
    formula = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    _assert_exact_total(formula, z3.Int("total"), 0)


def test_nested_record_lists_keep_each_rows_length_and_support_selection(tmp_path):
    source = """
type WorkingShift = record(int: day, bool: active);
type Nurse = record(int: id, list of WorkingShift: working_shifts,
                    list of int: skills);
list of Nurse: nurses;
var int: total;
constraint total = sum(n in nurses)(n.id
    + sum(w in n.working_shifts)(w.day)
    + sum(s in n.skills)(s));
constraint nurses[1].working_shifts[2].day = 3;
solve satisfy;
"""
    data = tmp_path / "nested-record-lists.json"
    data.write_text(json.dumps({"nurses": [
        {"id": 10, "working_shifts": [
            {"day": 1, "active": True}, {"day": 3, "active": False}],
         "skills": [2]},
        {"skills": [1, 2], "working_shifts": [
            {"active": True, "day": 4}], "id": 20},
    ]}), encoding="utf-8")
    result = sp.translate(source=source, language="minizinc", data=[str(data)])
    assert result.ok, [d.message for d in result.diagnostic_items]
    formula = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    _assert_exact_total(formula, z3.Int("total"), 43)


def test_empty_and_ragged_nested_record_lists_have_independent_lengths(tmp_path):
    source = """
type WorkingShift = record(int: day);
type Nurse = record(int: id, list of WorkingShift: working_shifts,
                    list of int: skills);
list of Nurse: nurses;
var int: total;
constraint total = sum(n in nurses)(n.id
    + length(n.working_shifts) + length(n.skills)
    + sum(w in n.working_shifts)(w.day) + sum(s in n.skills)(s));
solve satisfy;
"""
    data = tmp_path / "empty-and-ragged-record-lists.json"
    data.write_text(json.dumps({"nurses": [
        {"id": 9, "working_shifts": [], "skills": []},
        {"id": 2, "working_shifts": [{"day": 5}], "skills": [7, 8]},
    ]}), encoding="utf-8")
    result = sp.translate(source=source, language="minizinc", data=[str(data)])
    assert result.ok, [d.message for d in result.diagnostic_items]
    formula = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    _assert_exact_total(formula, z3.Int("total"), 34)


@pytest.mark.parametrize(("constraint", "expected"), [
    ("constraint r.flags[2];", z3.unsat),
    ("constraint not r.flags[2];", z3.sat),
    ("constraint forall(i in 1..2)(r.flags[i]);", z3.unsat),
])
def test_boolean_record_list_oob_matches_r228_observed_closure(
        tmp_path, constraint, expected):
    source = """
type R = record(list of bool: flags);
R: r;
""" + constraint + "\nsolve satisfy;\n"
    data = tmp_path / "boolean-list-oob.json"
    data.write_text('{"r":{"flags":[true]}}', encoding="utf-8")
    result = sp.translate(source=source, language="minizinc", data=[str(data)])
    assert result.ok, [d.message for d in result.diagnostic_items]
    formula = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    solver = z3.Solver()
    solver.add(formula)
    assert solver.check() == expected


def test_record_equality_is_refused_until_nominal_semantics_are_implemented(tmp_path):
    source = """
type Left = record(int: a, int: b);
type Right = record(int: b, int: a);
Left: left;
Right: right;
constraint left = right;
solve satisfy;
"""
    data = tmp_path / "whole-record.json"
    data.write_text('{"left":{"a":1,"b":2},'
                    '"right":{"b":2,"a":1}}', encoding="utf-8")
    result = sp.translate(source=source, language="minizinc", data=[str(data)])
    assert not result.ok
    assert any("whole-record equality is not implemented" in d.message
               for d in result.diagnostic_items)


def test_list_of_lists_is_refused_instead_of_flattened(tmp_path):
    source = """
type Box = record(list of list of int: values);
Box: box;
constraint length(box.values) = 2;
solve satisfy;
"""
    data = tmp_path / "list-record.json"
    data.write_text('{"box":{"values":[[4,9]]}}', encoding="utf-8")
    result = sp.translate(source=source, language="minizinc", data=[str(data)])
    assert not result.ok
    # The JSON binder rejects the nested value before the source record schema
    # is lowered. Keep this data-path regression as well as a parser-only check
    # of the source construct so neither route can silently flatten the list.
    assert any("unsupported value in JSON record" in d.message
               for d in result.diagnostic_items)
    schema_only = sp.translate(source=source, language="minizinc")
    assert not schema_only.ok
    assert any(d.code == sp.ErrorCode.E_UNSUPPORTED_CONSTRUCT
               and "nested list-valued record fields are not implemented" in d.message
               for d in schema_only.diagnostic_items)


def test_ihtc_top_level_scalar_lists_bind_json_length_iteration_and_index(tmp_path):
    # Source slice: official-model-sources/ihtc-2024-marte/model.mzn:29-30.
    # Data slice: i01.json age_groups/genders (file SHA-256
    # 9e9767a0d7013badfeb8babb2ead3ea3847b078a4572b31b91838392992bbe6e).
    source = """
list of string: age_groups;
list of string: genders;
constraint length(age_groups) = 3 /\\ length(genders) = 2;
constraint age_groups[1] = \"infant\" /\\ genders[2] = \"B\";
constraint forall(group in age_groups)(group != \"\");
solve satisfy;
"""
    data = tmp_path / "ihtc-scalar-lists.json"
    data.write_text(json.dumps({
        "age_groups": ["infant", "adult", "elderly"],
        "genders": ["A", "B"],
    }), encoding="utf-8")
    result = sp.translate(source=source, language="minizinc", data=[str(data)])
    assert result.ok, [d.message for d in result.diagnostic_items]
    formula = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    solver = z3.Solver()
    solver.add(formula)
    assert solver.check() == z3.sat


def test_top_level_scalar_lists_preserve_empty_and_exact_float_values(tmp_path):
    source = """
list of int: empty_values;
list of float: prices;
constraint length(empty_values) = 0;
constraint length(prices) = 2;
constraint sum(price in prices)(price) = 3.75;
constraint prices[1] = 1.0 /\\ prices[2] = 2.75;
solve satisfy;
"""
    data = tmp_path / "scalar-lists.json"
    data.write_text(json.dumps({"empty_values": [], "prices": [1, 2.75]}),
                    encoding="utf-8")
    result = sp.translate(source=source, language="minizinc", data=[str(data)])
    assert result.ok, [d.message for d in result.diagnostic_items]
    formula = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    solver = z3.Solver()
    solver.add(formula)
    assert solver.check() == z3.sat


def test_top_level_bool_list_keeps_boolean_cells(tmp_path):
    source = """
list of bool: flags;
constraint length(flags) = 2 /\\ flags[1] /\\ not flags[2];
constraint count(flag in flags)(flag) = 1;
solve satisfy;
"""
    data = tmp_path / "bool-list.json"
    data.write_text('{"flags":[true,false]}', encoding="utf-8")
    result = sp.translate(source=source, language="minizinc", data=[str(data)])
    assert result.ok, [d.message for d in result.diagnostic_items]
    formula = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    solver = z3.Solver()
    solver.add(formula)
    assert solver.check() == z3.sat


def test_top_level_enum_list_binds_nominal_members_and_rejects_other_enum(tmp_path):
    source = """
enum Color = {Red, Blue};
list of Color: colors;
constraint length(colors) = 2 /\\ colors[1] = Red /\\ colors[2] = Blue;
solve satisfy;
"""
    data = tmp_path / "enum-list.json"
    data.write_text(json.dumps({"colors": ["Red", "Blue"]}), encoding="utf-8")
    result = sp.translate(source=source, language="minizinc", data=[str(data)])
    assert result.ok, [d.message for d in result.diagnostic_items]

    mismatched_source = """
enum Color = {Red, Blue};
enum Shape = {Circle};
list of Color: colors;
constraint length(colors) = 1;
solve satisfy;
"""
    bad_data = tmp_path / "enum-list-mismatch.json"
    bad_data.write_text(json.dumps({"colors": ["Circle"]}), encoding="utf-8")
    mismatch = sp.translate(source=mismatched_source, language="minizinc",
                            data=[str(bad_data)])
    assert not mismatch.ok
    assert any("not a member of enum 'Color'" in d.message
               or "not a member of type 'Color'" in d.message
               for d in mismatch.diagnostic_items)


def test_top_level_scalar_list_rejects_wrong_element_type(tmp_path):
    source = "list of int: counts; constraint length(counts) = 1; solve satisfy;"
    data = tmp_path / "wrong-list-type.json"
    data.write_text('{"counts":["seven"]}', encoding="utf-8")
    result = sp.translate(source=source, language="minizinc", data=[str(data)])
    assert not result.ok
    assert any(d.code == sp.ErrorCode.E_TYPE for d in result.diagnostic_items)


def test_record_functions_from_included_frame_return_and_filter_records(tmp_path):
    source = tmp_path / "main.mzn"
    helpers = tmp_path / "helpers.mzn"
    helpers.write_text("""
function Room: room(Occupant: occupant) =
  [room | room in rooms where occupant.room_id == room.id][1];
function bool: has_room(Occupant: occupant, Room: candidate) =
  room(occupant).id == candidate.id;
""", encoding="utf-8")
    source_text = """
type Occupant = record(string: id, string: room_id);
type Room = record(string: id);
list of Occupant: occupants;
list of Room: rooms;
include "helpers.mzn";
constraint has_room(occupants[1], rooms[2]);
solve satisfy;
"""
    source.write_text(source_text, encoding="utf-8")
    data = tmp_path / "function-records.json"
    data.write_text(json.dumps({
        "occupants": [{"id": "p0", "room_id": "r0"}],
        "rooms": [{"id": "r1"}, {"id": "r0"}],
    }), encoding="utf-8")
    result = sp.translate(path=str(source), language="minizinc", data=[str(data)])
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.add(z3.And(*z3.parse_smt2_string(result.to_smt2())))
    assert solver.check() == z3.sat

    source.write_text(source_text.replace(
        "constraint has_room(occupants[1], rooms[2]);",
        "constraint has_room(occupants[1], rooms[2]) /\\ not has_room(occupants[1], rooms[2]);"),
        encoding="utf-8")
    contradictory = sp.translate(path=str(source), language="minizinc", data=[str(data)])
    assert contradictory.ok, [d.message for d in contradictory.diagnostic_items]
    solver = z3.Solver()
    solver.add(z3.And(*z3.parse_smt2_string(contradictory.to_smt2())))
    assert solver.check() == z3.unsat


def test_function_invocations_get_fresh_let_binders(tmp_path):
    source = """
array[1..2] of var int: choices;
function var bool: choose(var int: value) =
  let { var int: local } in local = value;
constraint choose(choices[1]) /\\ choose(choices[2]);
solve satisfy;
"""
    result = sp.translate(source=source, language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]
    script = result.to_smt2()
    from _public_relation import private_witness_names, public_relation
    assert len(private_witness_names(result)) == 2
    # Independent calls permit different choices; a shared witness would fail.
    choices = z3.Array("choices", z3.IntSort(), z3.IntSort())
    solver = z3.Solver()
    solver.add(z3.Xor(public_relation(result), z3.BoolVal(True)))
    assert solver.check() == z3.unsat
    solver = z3.Solver()
    solver.add(*z3.parse_smt2_string(script), choices[1] == 3, choices[2] == 7)
    assert solver.check() == z3.sat


def test_scalar_function_body_constrains_its_call_value():
    source = """
function int: add_one(int: value) = value + 1;
constraint add_one(4) = 6;
solve satisfy;
"""
    result = sp.translate(source=source, language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.add(z3.And(*z3.parse_smt2_string(result.to_smt2())))
    assert solver.check() == z3.unsat


def test_function_record_arguments_use_structural_record_types(tmp_path):
    source = """
type Left = record(int: id);
type Right = record(int: id);
list of Right: values;
function int: get_id(Left: value) = value.id;
constraint get_id(values[1]) = 1;
solve satisfy;
"""
    data = tmp_path / "wrong-record-function-type.json"
    data.write_text(json.dumps({"values": [{"id": 1}]}), encoding="utf-8")
    result = sp.translate(source=source, language="minizinc", data=[str(data)])
    assert result.ok, [d.message for d in result.diagnostic_items]

    # Record aliases with a changed field name or field type are not
    # structurally compatible, even when their tuple carrier sorts coincide.
    incompatible_cases = [
        (source.replace("type Right = record(int: id);",
                        "type Right = record(int: key);"),
         {"values": [{"key": 1}]}),
        (source.replace("type Right = record(int: id);",
                        "type Right = record(string: id);"),
         {"values": [{"id": "one"}]}),
    ]
    for index, (incompatible, data_value) in enumerate(incompatible_cases):
        bad_data = tmp_path / f"incompatible-record-{index}.json"
        bad_data.write_text(json.dumps(data_value), encoding="utf-8")
        rejected = sp.translate(source=incompatible, language="minizinc",
                                data=[str(bad_data)])
        assert not rejected.ok
        assert any("structurally compatible" in d.message
                   or "incompatible structural types" in d.message
                   for d in rejected.diagnostic_items)


def test_empty_bool_string_and_float_lists_keep_declared_scalar_types(tmp_path):
    source = """
list of bool: empty_flags;
list of string: empty_names;
list of float: empty_values;
constraint length(empty_flags) = 0 /\\ length(empty_names) = 0 /\\ length(empty_values) = 1;
solve satisfy;
"""
    data = tmp_path / "empty-scalar-lists.json"
    data.write_text(json.dumps({
        "empty_flags": [], "empty_names": [], "empty_values": []
    }), encoding="utf-8")
    result = sp.translate(source=source, language="minizinc", data=[str(data)])
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.add(z3.And(*z3.parse_smt2_string(result.to_smt2())))
    assert solver.check() == z3.unsat


def test_mixed_untyped_float_predicate_array_promotes_integer_cells_exactly():
    source = """
predicate first_is_one(array[int] of float: values) = values[1] == 1.0;
constraint not first_is_one([1, 2.5]);
solve satisfy;
"""
    result = sp.translate(source=source, language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.add(z3.And(*z3.parse_smt2_string(result.to_smt2())))
    assert solver.check() == z3.unsat


def test_list_returning_functions_are_refused(tmp_path):
    list_return = """
function list of int: values(int: n) = [n];
constraint length(values(1)) = 1;
solve satisfy;
"""
    result = sp.translate(source=list_return, language="minizinc")
    assert not result.ok
    assert any("return type" in d.message for d in result.diagnostic_items)


def test_function_free_names_use_definition_scope_when_caller_let_shadows_name():
    source = """
int: g = 1;
function int: add_global(int: x) = g + x;
constraint let { int: g = 9 } in add_global(2) = 3;
solve satisfy;
"""
    result = sp.translate(source=source, language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.add(z3.And(*z3.parse_smt2_string(result.to_smt2())))
    assert solver.check() == z3.sat


def test_function_free_names_use_definition_scope_when_caller_generator_shadows_name():
    source = """
int: g = 1;
function int: add_global(int: x) = g + x;
constraint sum(g in [9])(add_global(2)) = 3;
solve satisfy;
"""
    result = sp.translate(source=source, language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.add(z3.And(*z3.parse_smt2_string(result.to_smt2())))
    assert solver.check() == z3.sat


def test_fixed_function_return_cannot_depend_on_var_formal():
    source = """
function int: identity(var int: x) = x;
var 0..9: decision;
constraint identity(decision) = decision;
solve satisfy;
"""
    result = sp.translate(source=source, language="minizinc")
    assert not result.ok
    assert any("fixed-return function" in d.message for d in result.diagnostic_items)


def test_fixed_function_return_may_ignore_var_formal():
    source = """
function int: constant(var int: x) = 7;
var 0..9: decision;
constraint constant(decision) = 7;
solve satisfy;
"""
    result = sp.translate(source=source, language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.add(z3.And(*z3.parse_smt2_string(result.to_smt2())))
    assert solver.check() == z3.sat


def test_var_function_return_may_depend_on_var_formal():
    source = """
function var int: identity(var int: x) = x;
var 0..9: decision;
constraint identity(decision) = decision;
solve satisfy;
"""
    result = sp.translate(source=source, language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]


def test_fixed_function_return_cannot_depend_on_global_decision_variable():
    source = """
var 0..9: decision;
function int: read_decision() = decision;
constraint read_decision() = decision;
solve satisfy;
"""
    result = sp.translate(source=source, language="minizinc")
    assert not result.ok
    assert any("depends on a decision variable" in d.message
               for d in result.diagnostic_items)


def test_nested_function_free_name_keeps_definition_environment_under_caller_let():
    source = """
int: g = 1;
function int: inner(int: x) = g + x;
function int: outer(int: x) = inner(x);
constraint let { int: g = 9 } in outer(2) = 3;
solve satisfy;
"""
    result = sp.translate(source=source, language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.add(z3.And(*z3.parse_smt2_string(result.to_smt2())))
    assert solver.check() == z3.sat


def test_fixed_return_var_formal_is_rejected_even_with_fixed_actual():
    source = """
function int: identity(var int: x) = x;
constraint identity(3) = 3;
solve satisfy;
"""
    result = sp.translate(source=source, language="minizinc")
    assert not result.ok
    assert any("fixed-return function" in d.message for d in result.diagnostic_items)
