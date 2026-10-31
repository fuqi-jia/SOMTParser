"""Large uniform arrays keep every scalar identity, domain, and group call."""
import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")

SOURCE = '''<instance format="XCSP3" type="CSP">
<variables>
 <array id="pos" size="[256][256]" startIndex="5">-2..5</array>
 <array id="ticket" size="[2]">0..1</array>
 <var id="alias" as="pos[5][5]"/>
</variables>
<constraints>
 <instantiation><list>ticket[]</list><values>1 0</values></instantiation>
 <group><element><list>ticket[]</list><index>%0</index><value>%1</value></element>
  <args>pos[5][5] pos[5][6]</args><args>pos[5][6] pos[5][5]</args>
 </group>
 <group><intension>ne(%0,%1)</intension>
  <args>pos[5][5] pos[5][6]</args><args>pos[5][6] pos[5][5]</args>
 </group>
 <intension>eq(alias,0)</intension>
</constraints></instance>'''


@pytest.mark.parametrize("file_input", [False, True])
def test_full_array_relation_including_unused_coordinates(tmp_path, file_input):
    if file_input:
        path = tmp_path / "compact.xml"
        path.write_text(SOURCE)
        translated = sp.translate(path=str(path), language="xcsp3")
    else:
        translated = sp.translate(source=SOURCE, language="xcsp3")
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    assert translated.uses_packed_smt_stream
    assert translated.report.stats.num_vars == 65539
    script = translated.to_smt2()
    actual = z3.parse_smt2_string(script)
    bounds = []
    for row in range(5, 261):
        for column in range(5, 261):
            coordinate = z3.Int(f"pos[{row}][{column}]")
            bounds.append(z3.And(coordinate >= -2, coordinate <= 5))
    a, b = z3.Ints("pos[5][5] pos[5][6]")
    expected = z3.And(*bounds, z3.Int("ticket[0]") == 1, z3.Int("ticket[1]") == 0,
                      z3.Int("alias") == 0,
                      z3.Or(z3.And(a == 0, b == 1), z3.And(a == 1, b == 0)))
    solver = z3.Solver()
    solver.add(z3.Xor(z3.And(*actual), expected))
    assert solver.check() == z3.unsat
    assert "pos[260][260]" in script
    solver = z3.Solver()
    solver.add(*actual, z3.Int("pos[260][260]") == 6)
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("file_input", [False, True])
@pytest.mark.parametrize("change", ["outside", "duplicate_before", "duplicate_after", "order", "unclosed"])
def test_compact_names_and_streamed_document_are_checked(tmp_path, file_input, change):
    if change == "outside":
        source = SOURCE.replace("<args>pos[5][5]", "<args>pos[4][5]", 1)
    elif change == "duplicate_before":
        source = SOURCE.replace("<variables>", '<variables><var id="pos[5][5]">-2..5</var>')
    elif change == "duplicate_after":
        source = SOURCE.replace("</variables>", '<var id="pos[5][5]">-2..5</var></variables>')
    elif change == "order":
        source = SOURCE.replace("</constraints>", "</constraints><variables/>")
    else:
        source = SOURCE.replace("</instance>", "</not-instance>")
    if file_input:
        path = tmp_path / "bad.xml"
        path.write_text(source)
        translated = sp.translate(path=str(path), language="xcsp3")
    else:
        translated = sp.translate(source=source, language="xcsp3")
    assert not translated.ok
    assert translated.diagnostic_items
