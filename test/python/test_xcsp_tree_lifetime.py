"""XCSP source-tree consumption preserves relations, aliases and diagnostics."""
import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


def _check_equivalent(result, expected):
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.add(z3.Xor(z3.And(*z3.parse_smt2_string(result.to_smt2())), expected))
    assert solver.check() == z3.unsat


def test_array_aliases_keep_prior_declarations_until_variable_pass_finishes():
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              '<array id="rows" size="[4]">1 3 5</array>'
              '<array id="copy" size="[2]" as="rows"/>'
              '</variables><constraints><intension>eq(copy[0],copy[1])</intension>'
              '</constraints></instance>')
    result = sp.translate(source=source, language="xcsp3")
    rows = [z3.Int(f"rows[{i}]") for i in range(4)]
    copies = [z3.Int(f"copy[{i}]") for i in range(2)]
    expected = z3.And(*[z3.Or(v == 1, v == 3, v == 5) for v in rows + copies],
                      copies[0] == copies[1])
    _check_equivalent(result, expected)


def test_nested_block_group_expansion_survives_prompt_child_erasure():
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              '<var id="x">0..2</var><var id="y">0..2</var>'
              '<var id="z">0..2</var></variables><constraints><block>'
              '<intension>eq(x,0)</intension><group>'
              '<intension>eq(add(%0,1),%1)</intension>'
              '<args>x y</args><args>y z</args></group></block>'
              '</constraints></instance>')
    result = sp.translate(source=source, language="xcsp3")
    x, y, z = z3.Ints("x y z")
    expected = z3.And(x >= 0, x <= 2, y >= 0, y <= 2, z >= 0, z <= 2,
                      x == 0, x + 1 == y, y + 1 == z)
    _check_equivalent(result, expected)


def test_file_backed_borrowed_table_survives_group_argument_erasure(tmp_path):
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              '<var id="x">0..2</var><var id="y">0..2</var>'
              '<var id="z">0..2</var></variables><constraints><group>'
              '<extension><list>%0 %1</list><supports>(0,1)(2,*)</supports></extension>'
              '<args>x y</args><args>y z</args></group></constraints></instance>')
    path = tmp_path / "borrowed-table.xml"
    path.write_text(source)
    result = sp.translate(path=str(path), language="xcsp3")
    x, y, z = z3.Ints("x y z")
    relation = lambda a, b: z3.Or(z3.And(a == 0, b == 1), a == 2)
    expected = z3.And(*[z3.And(v >= 0, v <= 2) for v in (x, y, z)],
                      relation(x, y), relation(y, z))
    _check_equivalent(result, expected)


def test_later_error_location_is_stable_after_prior_constraint_erased():
    source = ('<instance format="XCSP3" type="CSP">\n<variables>\n'
              '<var id="x">0..1</var>\n</variables>\n<constraints>\n'
              '<intension>eq(x,0)</intension>\n<unknown/>\n'
              '</constraints>\n</instance>')
    result = sp.translate(source=source, language="xcsp3")
    assert not result.ok
    diagnostic = next(d for d in result.diagnostic_items if "not implemented" in d.message)
    assert diagnostic.line == 7


def test_group_arity_diagnostic_keeps_later_argument_location_after_erasure():
    source = ('<instance format="XCSP3" type="CSP">\n<variables>\n'
              '<var id="x">0..1</var>\n<var id="y">0..1</var>\n</variables>\n'
              '<constraints>\n<group><intension>eq(%0,%1)</intension>\n'
              '<args>x y</args>\n<args>x</args></group>\n</constraints>\n</instance>')
    result = sp.translate(source=source, language="xcsp3")
    assert not result.ok
    diagnostic = next(d for d in result.diagnostic_items if "only 1 argument" in d.message)
    assert diagnostic.line == 9
