"""File input retains table bytes across chunk boundaries and unknown-size streams."""
import os
from pathlib import Path

import pytest
import somtparser as sp

z3 = pytest.importorskip('z3')

SOURCE = ('<instance format="XCSP3" type="CSP"><variables>'
          '<var id="x">0..2</var><var id="y">0..2</var>'
          '</variables><constraints><extension><list>x y</list>'
          '<supports>(0,1)(2,*)</supports></extension>'
          '</constraints></instance>')


def assert_relation(result):
    assert result.ok, [d.message for d in result.diagnostic_items]
    x, y = z3.Ints('x y')
    expected = z3.And(x >= 0, x <= 2, y >= 0, y <= 2,
                      z3.Or(z3.And(x == 0, y == 1), x == 2))
    check = z3.Solver()
    check.add(z3.Xor(z3.And(*z3.parse_smt2_string(result.to_smt2())), expected))
    assert check.check() == z3.unsat


def test_file_source_preserves_table_crossing_read_boundaries(tmp_path):
    # The numeric/wildcard table, not just XML whitespace, spans several reads.
    source = SOURCE.replace('(0,1)(2,*)', '(0,1)' * 14000 + '(2,*)')
    path = tmp_path / 'large-table.xml'
    path.write_bytes(source.encode())
    assert_relation(sp.translate(path=str(path), language='xcsp3'))


@pytest.mark.skipif(not Path('/proc/self/fd').is_dir(), reason='requires procfs')
def test_file_source_does_not_require_a_regular_file_size():
    reader, writer = os.pipe()
    try:
        data = SOURCE.encode()
        assert os.write(writer, data) == len(data)
        os.close(writer)
        writer = None
        assert_relation(sp.translate(path=f'/proc/self/fd/{reader}', language='xcsp3'))
    finally:
        os.close(reader)
        if writer is not None:
            os.close(writer)


@pytest.mark.parametrize("polarity", ["supports", "conflicts"])
@pytest.mark.parametrize("in_table_formal", [False, True])
def test_file_table_backing_survives_template_copies_and_consumption(
        tmp_path, polarity, in_table_formal):
    # Distinct sibling tables are consumed before and after a reused template.
    # A parameter inside table text additionally exercises materialization of
    # one template copy without changing the relation held by the next copy.
    relation = "(%2,*)" if in_table_formal else "(0,1)(2,*)"
    args = ("<args>x y 1</args><args>y x 2</args>" if in_table_formal
            else "<args>x y</args><args>y x</args>")
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              '<var id="x">0..2</var><var id="y">0..2</var>'
              '</variables><constraints><extension><list>x y</list>'
              '<conflicts>(0,0)</conflicts></extension>'
              '<group><extension><list>%0 %1</list><' + polarity + '>'
              + relation + '</' + polarity + '></extension>' + args + '</group>'
              '<extension><list>x y</list><conflicts>(2,2)</conflicts></extension>'
              '</constraints></instance>')
    path = tmp_path / 'table-lifetimes.xml'
    path.write_text(source)
    result = sp.translate(path=str(path), language='xcsp3')
    assert result.ok, [d.message for d in result.diagnostic_items]
    x, y = z3.Ints('x y')
    relations = ([x == 1, y == 2] if in_table_formal else
                 [z3.Or(z3.And(x == 0, y == 1), x == 2),
                  z3.Or(z3.And(y == 0, x == 1), y == 2)])
    expected = z3.And(x >= 0, x <= 2, y >= 0, y <= 2,
                      z3.Not(z3.And(x == 0, y == 0)),
                      z3.Not(z3.And(x == 2, y == 2)),
                      *[r if polarity == 'supports' else z3.Not(r)
                        for r in relations])
    check = z3.Solver()
    check.add(z3.Xor(z3.And(*z3.parse_smt2_string(result.to_smt2())), expected))
    assert check.check() == z3.unsat


def test_file_table_backing_preserves_rejected_tuple_location(tmp_path):
    source = SOURCE.replace('<supports>(0,1)(2,*)</supports>',
                            '<supports>\n(0,1)(2,NaN)</supports>')
    path = tmp_path / 'bad-table.xml'
    path.write_text(source)
    result = sp.translate(path=str(path), language='xcsp3')
    assert not result.ok
    assert any('not an integer' in d.message and d.file == str(path)
               for d in result.diagnostic_items)


@pytest.mark.parametrize('token,split', [
    ('<instance', 4), ('format="XCSP3"', 10), ('</variables>', 1),
    ('<supports>', 5), ('(0,1)', 3), ('</supports>', 2),
    ('<!-- start -->', 2), ('<!-- start -->', 12),
    ('<!-- middle -->', 3), ('<!-- middle -->', 14),
    ('<?xml version="1.0"?>', 19), ('<block/>', 7),
])
def test_streaming_xml_tokens_cross_window_boundary(tmp_path, token, split):
    source = ('<?xml version="1.0"?><!-- start -->' + SOURCE)
    source = source.replace('(0,1)(2,*)', '(0,1)<!-- middle -->(2,*)')
    source = source.replace('<constraints>', '<constraints><block/>')
    # Place the selected token across the actual 64 KiB read boundary.
    source = ' ' * (65536 - (source.index(token) + split)) + source
    path = tmp_path / 'boundary.xml'
    path.write_text(source)
    result = sp.translate(path=str(path), language='xcsp3')
    assert_relation(result)
    inline = sp.translate(source=source, language='xcsp3')
    assert_relation(inline)


@pytest.mark.parametrize('split', [1, 2, 4])
def test_streaming_xml_entity_crosses_window_boundary(tmp_path, split):
    source = SOURCE.replace('<instance ', '<instance note="a&amp;b" ')
    source = ' ' * (65536 - (source.index('&amp;') + split)) + source
    path = tmp_path / 'entity.xml'
    path.write_text(source)
    assert_relation(sp.translate(path=str(path), language='xcsp3'))


def test_streaming_xml_long_attribute_and_comment(tmp_path):
    source = SOURCE.replace('<instance ', '<instance note="' + 'a' * 150000 + '" ')
    source = source.replace('(0,1)(2,*)', '(0,1)<!--' + 'b' * 150000 + '-->(2,*)')
    path = tmp_path / 'long-token.xml'
    path.write_text(source)
    assert_relation(sp.translate(path=str(path), language='xcsp3'))


def test_streaming_xml_preserves_line_at_mismatched_boundary_tag(tmp_path):
    source = SOURCE.replace('</supports>', '</conflicts>')
    source = '\n' * (65536 - source.index('</conflicts>') - 2) + source
    path = tmp_path / 'mismatched.xml'
    path.write_text(source)
    result = sp.translate(path=str(path), language='xcsp3')
    assert not result.ok
    assert any(d.file == str(path) and d.line == source.count('\n') + 1
               and 'conflicts' in d.message for d in result.diagnostic_items)


def test_shared_streamed_table_keeps_polarity_and_domains(tmp_path):
    # Identical bytes may share storage across differing constraint semantics.
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              '<var id="x">0..2</var><var id="y">0..1</var>'
              '<var id="z">0..2</var></variables><constraints>'
              '<extension><list>x y</list><supports>(0,1)(2,*)</supports></extension>'
              '<extension><list>y z</list><conflicts>(0,1)(2,*)</conflicts></extension>'
              '<extension><list>z x</list><supports>(0,1)(2,*)</supports></extension>'
              '</constraints></instance>')
    path = tmp_path / 'shared-bytes.xml'
    path.write_text(source)
    result = sp.translate(path=str(path), language='xcsp3')
    assert result.ok, [d.message for d in result.diagnostic_items]
    x, y, z = z3.Ints('x y z')
    expected = z3.And(x >= 0, x <= 2, y >= 0, y <= 1, z >= 0, z <= 2,
                      z3.Or(z3.And(x == 0, y == 1), x == 2),
                      z3.Not(z3.Or(z3.And(y == 0, z == 1), y == 2)),
                      z3.Or(z3.And(z == 0, x == 1), z == 2))
    solver = z3.Solver()
    solver.add(z3.Xor(z3.And(*z3.parse_smt2_string(result.to_smt2())), expected))
    assert solver.check() == z3.unsat
