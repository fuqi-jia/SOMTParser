"""Fixed optional cells and finite regexp acceptance preserve source semantics."""
import itertools
import pytest
z3 = pytest.importorskip("z3")
import somtparser as sp


def _translate(source, data=()):
    return sp.translate(source=source, language="minizinc", data=list(data))


def _solver(source, data=()):
    result = _translate(source, data)
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.add(*z3.parse_smt2_string(result.to_smt2(sp.OmtDialect.Z3)))
    return solver


def test_fixed_optional_cells_distinguish_absence_from_zero():
    source = r"""
      array[1..3] of opt int: a = [<>,0,9];
      constraint absent(a[1]) /\ not occurs(a[1]);
      constraint occurs(a[2]) /\ deopt(a[2]) = 0;
      constraint deopt(a[3]) = 9;
      solve satisfy;
    """
    assert _solver(source).check() == z3.sat
    assert _solver(source.replace("deopt(a[2]) = 0", "deopt(a[2]) = 1")).check() == z3.unsat


def test_optional_dynamic_index_keeps_presence_and_deopt_definedness():
    source = r"""
      array[1..3] of opt int: a = [<>,0,9];
      var 1..3: i;
      constraint occurs(a[i]) /\ deopt(a[i]) = 0;
      solve satisfy;
    """
    solver = _solver(source)
    solver.add(z3.Int("i") != 2)
    assert solver.check() == z3.unsat
    solver = _solver(source.replace(r"occurs(a[i]) /\ deopt(a[i]) = 0", "absent(a[i])"))
    solver.add(z3.Int("i") != 1)
    assert solver.check() == z3.unsat


def test_absent_deopt_uses_partial_value_semantics():
    source = "array[1..1] of opt int: a = [<>]; constraint deopt(a[1]) = 0; solve satisfy;"
    assert _solver(source).check() == z3.unsat
    assert _solver(source.replace("deopt(a[1]) = 0", "(deopt(a[1]) default 8) = 8")).check() == z3.sat


def test_optional_enum_data_and_label_reordering(tmp_path):
    data = tmp_path / "values.dzn"
    data.write_text("a = [| second: <>, blue | first: red, <> |];\n")
    source = r"""
      enum Row = {first,second}; enum E = {red,blue};
      array[Row,1..2] of opt E: a;
      constraint deopt(a[first,1]) = red /\ absent(a[first,2]);
      constraint absent(a[second,1]) /\ deopt(a[second,2]) = blue;
      solve satisfy;
    """
    assert _solver(source, [str(data)]).check() == z3.sat


@pytest.mark.parametrize("declaration", ["int", "var int"])
def test_absence_cannot_initialize_nonoptional_array(tmp_path, declaration):
    data = tmp_path / "invalid.dzn"
    data.write_text("a = [<>];")
    result = _translate(f"array[1..1] of {declaration}: a; solve satisfy;", [str(data)])
    assert not result.ok


def test_optional_array_cannot_silently_erase_presence():
    result = _translate("array[1..2] of opt int: a = [<>,4]; constraint sum(a) = 4; solve satisfy;")
    assert not result.ok


@pytest.mark.parametrize("pattern, expected", [
    ("1* [^1]* 1*", lambda xs: not any(xs[a] != 1 and xs[b] == 1 and xs[c] != 1
                                    for a in range(4) for b in range(a + 1, 4) for c in range(b + 1, 4))),
    ("(1|2){2} 3? .", lambda xs: xs[0] in (1,2) and xs[1] in (1,2) and xs[2] == 3),
    ("[1-2]+ 3{1,}", lambda xs: any(all(x in (1,2) for x in xs[:k]) and all(x == 3 for x in xs[k:])
                                  for k in range(1,4))),
])
def test_regular_regexp_matches_exhaustive_finite_language(pattern, expected):
    source = 'array[1..4] of var 1..3: x; constraint regular(x,"' + pattern + '"); solve satisfy;'
    solver = _solver(source)
    array = z3.Array("x", z3.IntSort(), z3.IntSort())
    for values in itertools.product(range(1,4), repeat=4):
        solver.push()
        solver.add(*(z3.Select(array, i + 1) == value for i, value in enumerate(values)))
        assert (solver.check() == z3.sat) == expected(values), values
        solver.pop()


def test_regular_enum_names_and_empty_word():
    source = r'enum E = {None,A,B}; array[1..3] of var E: x; constraint regular(x,"None* [^None]* None*"); constraint x[1]=A /\ x[2]=None /\ x[3]=B; solve satisfy;'
    assert _solver(source).check() == z3.unsat
    assert _solver(source.replace("x[2]=None", "x[2]=A")).check() == z3.sat
    assert not _translate('array[1..0] of var int: x; constraint regular(x,"1*"); solve satisfy;').ok
    assert not _translate('array[1..0] of var int: x; constraint regular(x,"1+"); solve satisfy;').ok


@pytest.mark.parametrize("pattern", ["", "[]", "[^]", "()", "1|", "|1", "1{4,2}"])
def test_regular_rejects_malformed_source_regexps(pattern):
    assert not _translate('array[1..1] of var 1..3:x; constraint regular(x,"' + pattern + '"); solve satisfy;').ok


def test_regular_closes_undefined_cells_before_negation():
    source = 'array[1..1] of opt int: a=[<>]; constraint regular([deopt(a[1])],"0"); solve satisfy;'
    assert _solver(source).check() == z3.unsat
    assert _solver(source.replace('constraint regular', 'constraint not regular')).check() == z3.sat


@pytest.mark.parametrize("consumer", ["sum(a)", "product(a)", "min(a)", "max(a)", "sum(array1d(a))", "sum([a[i] | i in 1..2])"])
def test_optional_presence_is_not_discarded_by_other_array_consumers(consumer):
    assert not _translate('array[1..2] of opt int:a=[<>,4]; constraint ' + consumer + ' = 4; solve satisfy;').ok
