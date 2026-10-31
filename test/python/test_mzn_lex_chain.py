"""Check column order independently, including reification and partial cells."""
import itertools
import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


def translated(source):
    result = sp.translate(source=source, language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]
    return z3.And(*z3.parse_smt2_string(result.to_smt2()))


@pytest.mark.parametrize("strict", [False, True])
@pytest.mark.parametrize("boolean", [False, True])
def test_lex_chain_reification_matches_every_small_matrix(strict, boolean):
    rows, cols = (2, 3) if boolean else (2, 2)
    count = rows * cols
    fn = "lex_chain_less" if strict else "lex_chain_lesseq"
    sort = "bool" if boolean else "0..2"
    declarations = "".join(f"var {sort}: x{i};" for i in range(count))
    cells = ",".join(f"x{i}" for i in range(count))
    formula = translated(
        f'include "{fn}.mzn";' + declarations
        + f"var bool: b; constraint b = {fn}(array2d(3..4,-2..{cols-3},[{cells}]));"
        + "solve satisfy;"
    )
    symbols = [(z3.Bool if boolean else z3.Int)(f"x{i}") for i in range(count)]
    solver = z3.Solver()
    solver.add(formula)
    for assignment in itertools.product([False, True] if boolean else range(3), repeat=count):
        columns = [tuple(assignment[r * cols + c] for r in range(rows)) for c in range(cols)]
        expected = all(a < b if strict else a <= b for a, b in zip(columns, columns[1:]))
        solver.push()
        solver.add(*[v == x for v, x in zip(symbols, assignment)])
        solver.push()
        solver.add(z3.Bool("b") == expected)
        assert solver.check() == z3.sat, assignment
        solver.pop()
        solver.add(z3.Bool("b") != expected)
        assert solver.check() == z3.unsat, assignment
        solver.pop()


@pytest.mark.parametrize("rows,columns", [(0, 0), (0, 2), (2, 0), (2, 1)])
@pytest.mark.parametrize("strict", [False, True])
def test_empty_shapes_and_single_column(rows, columns, strict):
    fn = "lex_chain_less" if strict else "lex_chain_lesseq"
    values = ",".join("0" for _ in range(rows * columns))
    formula = translated(
        f"constraint {fn}(array2d(1..{rows},1..{columns},[{values}])); solve satisfy;"
    )
    solver = z3.Solver()
    solver.add(formula)
    assert solver.check() == (z3.unsat if strict and rows == 0 and columns > 1 else z3.sat)


@pytest.mark.parametrize("columns", [1, 2])
@pytest.mark.parametrize("negated", [False, True])
def test_undefined_cell_is_false_before_predicate_negation(columns, negated):
    cells = "1 div d" + (",1" if columns == 2 else "")
    call = f"lex_chain_lesseq(array2d(1..1,1..{columns},[{cells}]))"
    formula = translated(
        "var 0..1: d; constraint d=0; constraint "
        + ("not " if negated else "") + call + "; solve satisfy;"
    )
    solver = z3.Solver()
    solver.add(formula)
    assert solver.check() == (z3.sat if negated else z3.unsat)


def test_lex_chain_alias_and_wrong_rank():
    solver = z3.Solver()
    solver.add(translated("constraint lex_chain([|1,0|2,3|]); solve satisfy;"))
    assert solver.check() == z3.unsat
    result = sp.translate(source="constraint lex_chain_lesseq([1,2]); solve satisfy;",
                          language="minizinc")
    assert not result.ok
    assert any("two-dimensional" in d.message for d in result.diagnostic_items)
