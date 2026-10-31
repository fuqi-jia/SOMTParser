"""Large repeated parameter tables retain their exact finite relation."""
import itertools
import pytest
import z3
import somtparser as sp


def _model(rows, *, boolean=False, negate=False, columns=None, call=None, extra=""):
    typ = "bool" if boolean else "int"
    width = len(rows[0])
    entries = rows * (1 + 128 // len(rows))
    first = 1 if columns is None else columns
    values = ",".join(str(value).lower() for row in entries for value in row)
    source = f"""
      array[{first}..{first + width - 1}] of var {typ}: x;
      array[-3..{len(entries) - 4},{first}..{first + width - 1}] of {typ}: t =
        array2d(-3..{len(entries) - 4},{first}..{first + width - 1},[{values}]);
      constraint {'not ' if negate else ''}{call or 'table(x,t)'};
      {extra}
      solve satisfy;
    """
    result = sp.translate(source=source, language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]
    assert any(choice in result.report.to_json() for choice in (
        "table-shared-characteristic-array", "table-shared-functional-array"))
    solver = z3.Solver()
    solver.add(*z3.parse_smt2_string(result.to_smt2(sp.OmtDialect.Z3)))
    return solver


@pytest.mark.parametrize("negate", [False, True])
@pytest.mark.parametrize("boolean", [False, True])
def test_repeated_rows_match_every_finite_assignment(boolean, negate):
    rows = [(False, True), (True, False), (False, True)] if boolean else [(-2, 4), (3, -2), (-2, 4)]
    solver = _model(rows, boolean=boolean, negate=negate, columns=-2)
    domain = [False, True] if boolean else [-3, -2, 0, 3, 4, 5]
    array = z3.Array("x", z3.IntSort(), z3.BoolSort() if boolean else z3.IntSort())
    for values in itertools.product(domain, repeat=2):
        solver.push()
        solver.add(array[-2] == values[0], array[-1] == values[1])
        assert (solver.check() == z3.sat) == ((values in rows) != negate), values
        solver.pop()


def test_shared_suffixes_do_not_mix_different_prefixes():
    rows = [(1, 2, 7), (1, 3, 8), (2, 2, 7), (2, 3, 8), (3, 2, 8)]
    solver = _model(rows)
    array = z3.Array("x", z3.IntSort(), z3.IntSort())
    for values in itertools.product([0, 1, 2, 3, 7, 8], repeat=3):
        solver.push()
        solver.add(*(array[i + 1] == value for i, value in enumerate(values)))
        assert (solver.check() == z3.sat) == (values in rows), values
        solver.pop()


@pytest.mark.parametrize("negate", [False, True])
def test_partial_tuple_cells_close_before_negation(negate):
    solver = _model([(0, 7)], negate=negate, call="table([1 div 0,7],t)")
    assert solver.check() == (z3.sat if negate else z3.unsat)


def test_content_cache_distinguishes_let_shadowed_tables():
    rows = [(1, 2), (3, 4)]
    nested = ",".join(["5,6"] * 128)
    extra = f"constraint let {{ array[1..128,1..2] of int: t = array2d(1..128,1..2,[{nested}]) }} in not table(x,t);"
    solver = _model(rows, extra=extra)
    array = z3.Array("x", z3.IntSort(), z3.IntSort())
    solver.add(array[1] == 1, array[2] == 2)
    assert solver.check() == z3.sat


def test_table_reads_cannot_widen_the_declared_tuple_indices():
    values = ",".join(["1,2"] * 128)
    source = f"array[1..128,2..3] of int:t=array2d(1..128,2..3,[{values}]); constraint table([1,2],t); solve satisfy;"
    assert not sp.translate(source=source, language="minizinc").ok


def test_repeated_calls_emit_one_total_table_definition():
    def emit(repetitions):
        source = f"""
          array[1..{repetitions},1..2] of var int:x;
          array[1..256,1..2] of int:t=array2d(1..256,1..2,[i | i in 1..512]);
          constraint forall(i in 1..{repetitions})(table([x[i,1],x[i,2]],t));
          solve satisfy;
        """
        result = sp.translate(source=source, language="minizinc")
        assert result.ok, [d.message for d in result.diagnostic_items]
        target = result.to_smt2(sp.OmtDialect.Z3)
        assert "define-fun" in target and "__mzn_table@" in target
        solver = z3.Solver(); solver.add(*z3.parse_smt2_string(target))
        return target
    single = emit(1)
    repeated = emit(16)
    assert repeated.count("define-fun") == single.count("define-fun")
    assert len(repeated) < 2 * len(single)


def test_large_dzn_matrix_cells_keep_their_own_expression_boundaries(tmp_path):
    rows, columns = 64, 512
    data = tmp_path / "matrix.dzn"
    matrix = [",".join(str((row * columns + col) % 17 - 8) for col in range(columns))
              for row in range(rows)]
    data.write_text("a = [|" + "|".join(matrix) + "|];\n")
    last = ((rows * columns - 1) % 17) - 8
    source = f"array[1..{rows},1..{columns}] of int:a; constraint a[1,1]=-8 /\\ a[{rows},{columns}]={last}; solve satisfy;"
    result = sp.translate(source=source, language="minizinc", data=[str(data)])
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver(); solver.add(*z3.parse_smt2_string(result.to_smt2(sp.OmtDialect.Z3)))
    assert solver.check() == z3.sat


def test_numeric_range_probe_keeps_nested_argument_commas_and_matrix_rows():
    source = r"""
      array[1..2,1..2] of int:a=[| -(1+2), max(1,2) | 4, 5 |];
      constraint (1 + max(1,2)..4) subset (1..5);
      constraint a[1,1] = -3 /\ a[1,2] = 2 /\ a[2,1] = 4 /\ a[2,2] = 5;
      solve satisfy;
    """
    result = sp.translate(source=source, language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver(); solver.add(*z3.parse_smt2_string(result.to_smt2(sp.OmtDialect.Z3)))
    assert solver.check() == z3.sat


@pytest.mark.parametrize("tail", [
    "array[1..256] of int: a=[i | i in 1..256];",
    "array[1..256] of int: a=array1d(2..257,[i | i in 1..256]);",
    "array[1..256] of 0..255: a=[i | i in 1..256];",
])
def test_cached_initializer_retains_declaration_errors(tail):
    prefix = "array[1..256] of int:a=[i | i in 1..256];" if tail.startswith("array[1..256] of int: a=[") else ""
    assert not sp.translate(source=prefix + tail + "solve satisfy;", language="minizinc").ok


def test_cached_initializer_resolves_forward_dependencies_and_keeps_column_origins():
    source = """
      array[2..257,3..4] of int:a=array2d(2..257,3..4,[if k=3 then i else b[i] endif | i in 2..257,k in 3..4]);
      array[2..257] of int:b=array1d(2..257,[2*i | i in 2..257]);
      constraint a[2,3]=2 /\\ a[257,4]=514;
      solve satisfy;
    """
    result = sp.translate(source=source, language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver(); solver.add(*z3.parse_smt2_string(result.to_smt2(sp.OmtDialect.Z3)))
    assert solver.check() == z3.sat


def test_initializer_with_let_bindings_keeps_ordinary_evaluation():
    source = """
      array[1..256] of int:a=[let {int:j=2*i;} in j+1 | i in 1..256];
      constraint a[1]=3 /\\ a[256]=513;
      solve satisfy;
    """
    result = sp.translate(source=source, language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver(); solver.add(*z3.parse_smt2_string(result.to_smt2(sp.OmtDialect.Z3)))
    assert solver.check() == z3.sat


def test_initializer_cache_positions_belong_to_each_include(tmp_path):
    left = tmp_path / "left.mzn"
    right = tmp_path / "right.mzn"
    left.write_text("array[2..129] of int:a=array1d(2..129,[i+3 | i in 2..129]);\n")
    right.write_text("array[2..129] of int:b=array1d(2..129,[i+7 | i in 2..129]);\n")
    source = f'include "{left}"; include "{right}"; constraint a[2]=5 /\\ b[129]=136; solve satisfy;'
    result = sp.translate(source=source, language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver(); solver.add(*z3.parse_smt2_string(result.to_smt2(sp.OmtDialect.Z3)))
    assert solver.check() == z3.sat


def test_initializer_reuse_waits_for_all_deferred_data(tmp_path):
    data = tmp_path / "late.dzn"
    data.write_text("input=[3,4]; delayed=other;")
    source = """
      array[1..2] of int:input;
      array[1..2] of int:a=[input[i]+1 | i in 1..2];
      int:other=2; int:delayed;
      constraint a[1]=4 /\\ a[2]=5 /\\ delayed=2;
      solve satisfy;
    """
    result = sp.translate(source=source, language="minizinc", data=[str(data)])
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver(); solver.add(*z3.parse_smt2_string(result.to_smt2(sp.OmtDialect.Z3)))
    assert solver.check() == z3.sat
