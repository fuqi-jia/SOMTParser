"""Finite truth-table checks for compact XCSP table encodings."""
import itertools

import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


@pytest.mark.parametrize("first_polarity", ["supports", "conflicts"])
@pytest.mark.parametrize("second_polarity", ["supports", "conflicts"])
def test_shared_cells_preserve_overlapping_table_relations(first_polarity, second_polarity):
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              '<var id="x">-1..1</var><var id="y">-1 1</var><var id="z">-1..1</var>'
              '</variables><constraints><extension><list>x y</list><'
              + first_polarity + '>(-1,1)(0,-1)(1,1)</' + first_polarity
              + '></extension><extension><list>y z</list><'
              + second_polarity + '>(-1,*)(1,0)</' + second_polarity
              + '></extension></constraints></instance>')
    result = sp.translate(source=source, language="xcsp3")
    assert result.ok, [d.message for d in result.diagnostic_items]
    x, y, z = z3.Ints("x y z")
    first = z3.Or(z3.And(x == -1, y == 1), z3.And(x == 0, y == -1),
                  z3.And(x == 1, y == 1))
    second = z3.Or(y == -1, z3.And(y == 1, z == 0))
    expected = z3.And(x >= -1, x <= 1, z3.Or(y == -1, y == 1), z >= -1, z <= 1,
                      first if first_polarity == "supports" else z3.Not(first),
                      second if second_polarity == "supports" else z3.Not(second))
    solver = z3.Solver()
    solver.add(z3.Xor(z3.And(*z3.parse_smt2_string(result.to_smt2())), expected))
    assert solver.check() == z3.unsat


def table_formula(domains, rows, polarity="supports", scope="x y"):
    variables = ''.join(f'<var id="{name}">{domain}</var>'
                        for name, domain in zip(("x", "y", "z"), domains))
    tuples = ''.join('(' + ','.join(map(str, row)) + ')' for row in rows)
    result = sp.translate(
        source='<instance format="XCSP3" type="CSP"><variables>' + variables
        + '</variables><constraints><extension><list>' + scope + '</list><'
        + polarity + '>' + tuples + '</' + polarity
        + '></extension></constraints></instance>', language="xcsp3")
    assert result.ok, [d.message for d in result.diagnostic_items]
    text = result.to_smt2(sp.OmtDialect.Z3)
    return z3.And(*z3.parse_smt2_string(text)), text


@pytest.mark.parametrize("polarity", ["supports", "conflicts"])
@pytest.mark.parametrize("values,domain", [([0, 1, 2], "0..2"),
                                         ([-2, 1, 4], "-2 1 4")])
def test_all_binary_dense_tables(polarity, values, domain):
    x, y = z3.Ints("x y")
    universe = list(itertools.product([0, 1], values))
    bounds = z3.And(z3.Or(x == 0, x == 1), z3.Or(*[y == v for v in values]))
    for mask in range(1 << len(universe)):
        rows = [row for i, row in enumerate(universe) if mask & (1 << i)]
        target, _ = table_formula(["0..1", domain], rows, polarity)
        membership = z3.Or(*[z3.And(x == a, y == b) for a, b in rows])
        expected = z3.And(bounds, membership if polarity == "supports"
                          else z3.Not(membership))
        solver = z3.Solver()
        solver.add(z3.Xor(target, expected))
        assert solver.check() == z3.unsat, (polarity, values, mask)


@pytest.mark.parametrize("polarity", ["supports", "conflicts"])
def test_dense_table_duplicates_outside_domain_and_repeated_scope(polarity):
    rows = [(a, b) for a, b in itertools.product(range(3), repeat=2)
            if (a, b) != (1, 1)]
    rows += [(0, 0), (0, 0), (8, 8)]
    target, _ = table_formula(["0..2", "0..2"], rows, polarity, scope="x x")
    x, y = z3.Ints("x y")
    expected = z3.And(x >= 0, x <= 2, y >= 0, y <= 2,
                      x != 1 if polarity == "supports" else x == 1)
    solver = z3.Solver()
    solver.add(z3.Xor(target, expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("polarity", ["supports", "conflicts"])
def test_dense_table_wildcard_keeps_its_semantics(polarity):
    rows = [(a, b) for a, b in itertools.product(range(3), repeat=2)
            if a != b] + [("*", 1)]
    target, _ = table_formula(["0..2", "0..2"], rows, polarity)
    x, y = z3.Ints("x y")
    member = z3.Or(x != y, y == 1)
    expected = z3.And(x >= 0, x <= 2, y >= 0, y <= 2,
                      member if polarity == "supports" else z3.Not(member))
    solver = z3.Solver()
    solver.add(z3.Xor(target, expected))
    assert solver.check() == z3.unsat


def test_dense_table_emission_is_bounded_by_missing_tuples():
    rows = [(a, b) for a, b in itertools.product(range(20), repeat=2) if a != b]
    target, text = table_formula(["0..19", "0..19"], rows)
    x, y = z3.Ints("x y")
    solver = z3.Solver()
    solver.add(z3.Xor(target, z3.And(x >= 0, x < 20, y >= 0, y < 20, x != y)))
    assert solver.check() == z3.unsat
    assert len(text) < 10000


def test_huge_domain_falls_back_without_enumeration():
    target, _ = table_formula(["-9223372036854775808..9223372036854775807", "0..1"],
                              [(0, 0), (1, 1)])
    x, y = z3.Ints("x y")
    solver = z3.Solver()
    solver.add(z3.Xor(target, z3.Or(z3.And(x == 0, y == 0), z3.And(x == 1, y == 1))))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("polarity", ["supports", "conflicts"])
def test_functional_table_suffixes_preserve_relation(polarity):
    # Same shape as the repeated AlteredStates adjacency table: the third
    # column is determined by two finite coordinates, with many equal suffixes.
    rows = [(a, b, int(abs(a - b) <= 1))
            for a, b in itertools.product(range(8), repeat=2)]
    target, _ = table_formula(["0..7", "0..7", "0..1"], rows, polarity, "x y z")
    x, y, z = z3.Ints("x y z")
    relation = z == z3.If(z3.And(x - y <= 1, y - x <= 1), 1, 0)
    expected = z3.And(x >= 0, x < 8, y >= 0, y < 8, z >= 0, z <= 1,
                      relation if polarity == "supports" else z3.Not(relation))
    solver = z3.Solver()
    solver.add(z3.Xor(target, expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("polarity", ["supports", "conflicts"])
def test_overlapping_wildcard_suffixes_are_disjoined(polarity):
    target, _ = table_formula(["0..2"] * 3,
                              [(0, "*", 1), ("*", 1, 0), (2, 2, 2)],
                              polarity, "x y z")
    x, y, z = z3.Ints("x y z")
    relation = z3.Or(z3.And(x == 0, z == 1), z3.And(y == 1, z == 0),
                     z3.And(x == 2, y == 2, z == 2))
    expected = z3.And(*[z3.And(v >= 0, v <= 2) for v in (x, y, z)],
                      relation if polarity == "supports" else z3.Not(relation))
    solver = z3.Solver()
    solver.add(z3.Xor(target, expected))
    assert solver.check() == z3.unsat


def test_very_wide_tables_preserve_iterative_fallback():
    variables = ''.join(f'<var id="v{i}">0..1</var>' for i in range(65))
    names = ' '.join(f'v{i}' for i in range(65))
    rows = ''.join('(' + ','.join([str(v)] * 65) + ')' for v in [0, 1])
    result = sp.translate(source='<instance format="XCSP3" type="CSP"><variables>'
                          + variables + '</variables><constraints><extension><list>'
                          + names + '</list><supports>' + rows
                          + '</supports></extension></constraints></instance>',
                          language="xcsp3")
    assert result.ok, [d.message for d in result.diagnostic_items]
    values = [z3.Int(f'v{i}') for i in range(65)]
    expected = z3.Or(z3.And(*[v == 0 for v in values]),
                     z3.And(*[v == 1 for v in values]))
    solver = z3.Solver()
    solver.add(z3.Xor(z3.And(*z3.parse_smt2_string(result.to_smt2())), expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("polarity", ["supports", "conflicts"])
@pytest.mark.parametrize("width", [2, 65])
def test_numeric_table_storage_keeps_extreme_values_separate_from_wildcards(polarity, width):
    low, high = -(1 << 63), (1 << 63) - 1
    names = [f"v{i}" for i in range(width)]
    domain = f"{low}..{high}"
    variables = ''.join(f'<var id="{name}">{domain}</var>' for name in names)
    rows = [(str(low), str(high)), ("*", str(low)), (str(high), "0")]
    tuples = ''.join('(' + ','.join(list(row) + ["*"] * (width - 2)) + ')'
                     for row in rows)
    source = ('<instance format="XCSP3" type="CSP"><variables>' + variables
              + '</variables><constraints><extension><list>' + ' '.join(names)
              + '</list><' + polarity + '>' + tuples + '</' + polarity
              + '></extension></constraints></instance>')
    result = sp.translate(source=source, language="xcsp3")
    assert result.ok, [d.message for d in result.diagnostic_items]
    values = [z3.Int(name) for name in names]
    x, y = values[:2]
    relation = z3.Or(z3.And(x == low, y == high), y == low,
                     z3.And(x == high, y == 0))
    expected = z3.And(*[z3.And(v >= low, v <= high) for v in values],
                      relation if polarity == "supports" else z3.Not(relation))
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(z3.Xor(z3.And(*z3.parse_smt2_string(result.to_smt2())), expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("token", ["9223372036854775808", "-9223372036854775809", "NaN"])
def test_invalid_table_cell_is_rejected_before_dense_complement(token):
    result = sp.translate(source=(
        '<instance format="XCSP3" type="CSP"><variables>'
        '<var id="x">0..1</var><var id="y">0..1</var>'
        '</variables><constraints><extension><list>x y</list>'
        '<supports>(0,0)(0,1)(1,0)(1,1)(' + token + ',0)</supports>'
        '</extension></constraints></instance>'), language="xcsp3")
    assert not result.ok
    assert any("not an integer" in d.message for d in result.diagnostic_items)


@pytest.mark.parametrize("from_file", [False, True])
@pytest.mark.parametrize("polarity", ["supports", "conflicts"])
@pytest.mark.parametrize("shared", [False, True])
@pytest.mark.parametrize("table", ["(-1,0)(1,1)", "(-1,0)<!-- gap -->(1,1)"])
def test_table_source_lifetime_and_group_sharing(tmp_path, from_file, polarity, shared, table):
    variables = ''.join(f'<var id="{n}">-1..1</var>' for n in "xyz")
    extension = ('<extension><list>' + ('%0 %1' if shared else 'x y') + '</list><'
                 + polarity + '>' + table + '</' + polarity + '></extension>')
    constraints = ('<group>' + extension + '<args>x y</args><args>y z</args></group>'
                   if shared else extension)
    source = ('<instance format="XCSP3" type="CSP"><variables>' + variables
              + '</variables><constraints>' + constraints + '</constraints></instance>')
    if from_file:
        path = tmp_path / 'tables.xml'
        path.write_text(source)
        result = sp.translate(path=str(path), language="xcsp3")
    else:
        result = sp.translate(source=source, language="xcsp3")
    assert result.ok, [d.message for d in result.diagnostic_items]
    x, y, z = z3.Ints('x y z')
    def relation(a, b):
        allowed = z3.Or(z3.And(a == -1, b == 0), z3.And(a == 1, b == 1))
        return allowed if polarity == 'supports' else z3.Not(allowed)
    expected = z3.And(*[z3.And(v >= -1, v <= 1) for v in (x,y,z)],
                      relation(x,y), relation(y,z) if shared else z3.BoolVal(True))
    solver = z3.Solver()
    solver.add(z3.Xor(z3.And(*z3.parse_smt2_string(result.to_smt2())), expected))
    assert solver.check() == z3.unsat


def test_group_table_formals_are_materialized_before_substitution():
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              '<var id="x">0..2</var><var id="y">0..2</var></variables><constraints>'
              '<group><extension><list>%0 %1</list><supports>(%2,*)</supports>'
              '</extension><args>x y 1</args><args>y x 2</args></group>'
              '</constraints></instance>')
    result = sp.translate(source=source, language="xcsp3")
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.add(z3.Xor(z3.And(*z3.parse_smt2_string(result.to_smt2())),
                     z3.And(z3.Int('x') == 1, z3.Int('y') == 2)))
    assert solver.check() == z3.unsat
