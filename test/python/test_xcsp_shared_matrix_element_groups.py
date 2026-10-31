"""Fixed XCSP matrix groups retain one exact lookup over free model cells."""
import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


def translated(source, shared=True):
    result = sp.translate(source=source, language="xcsp3")
    assert result.ok, [item.message for item in result.diagnostic_items]
    report = result.report.to_json()
    assert ("captured-matrix-indexed-equality-helper" in report) == shared
    return result, result.to_smt2()


@pytest.mark.parametrize("offsets", [(0, 0), (-2, 4)])
@pytest.mark.parametrize("calls", [
    [("r", "c", "v"), ("r2", "c2", "w")],
    [("r", "r", "v"), ("r2", "c2", "r2")],
    [("m[0][0]", "c", "v"), ("r", "c", "m[0][0]")],
])
def test_matrix_group_matches_array_lookup_for_all_assignments(offsets, calls):
    row_start, col_start = offsets
    domains = {f"m[{r}][{c}]": (0, 2) for r in range(2) for c in range(3)}
    domains.update(r=(row_start - 1, row_start + 2),
                   c=(col_start - 1, col_start + 3), v=(0, 2),
                   r2=(row_start, row_start + 1), c2=(col_start, col_start + 2),
                   w=(-1, 3))
    variables = '<array id="m" size="[2][3]">0..2</array>' + ''.join(
        f'<var id="{name}">{lo}..{hi}</var>'
        for name, (lo, hi) in domains.items() if not name.startswith("m["))
    matrix = (f'<matrix startRowIndex="{row_start}" startColIndex="{col_start}">'
              'm[][]</matrix>')
    template = f'<element>{matrix}<index>%0 %1</index><value>%2</value></element>'
    group = '<group>' + template + ''.join(
        '<args>' + ' '.join(call) + '</args>' for call in calls) + '</group>'
    expanded = ''.join(f'<element>{matrix}<index>{r} {c}</index><value>{v}</value>'
                       '</element>' for r, c, v in calls)
    def source(constraints):
        return ('<instance format="XCSP3" type="CSP"><variables>' + variables
                + '</variables><constraints>' + constraints + '</constraints></instance>')

    context = z3.Context()
    symbols = {name: z3.Int(name, ctx=context) for name in domains}
    # The independent oracle uses a functional array read with index bounds;
    # it does not enumerate the lowering's disjunction of selected cells.
    array = z3.K(z3.IntSort(ctx=context), z3.IntVal(-1, ctx=context))
    for r in range(2):
        for c in range(3):
            array = z3.Store(array, 3 * r + c, symbols[f"m[{r}][{c}]"])
    expected = z3.And(*[z3.And(symbols[name] >= lo, symbols[name] <= hi)
                           for name, (lo, hi) in domains.items()], *[
        z3.And(symbols[r] >= row_start, symbols[r] < row_start + 2,
               symbols[c] >= col_start, symbols[c] < col_start + 3,
               z3.Select(array, 3 * (symbols[r] - row_start) + symbols[c] - col_start)
               == symbols[v]) for r, c, v in calls])
    for constraints, shared in [(group, True), (expanded, False)]:
        _, script = translated(source(constraints), shared)
        actual = z3.And(*z3.parse_smt2_string(script, ctx=context))
        solver = z3.Solver(ctx=context)
        solver.set(timeout=10000)
        solver.add(z3.Xor(actual, expected))
        assert solver.check() == z3.unsat, solver.reason_unknown()


def test_literal_matrix_and_colliding_generated_names_remain_exact():
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              '<var id="__somt_xcsp_group_0">0..1</var>'
              '<var id="__somt_xcsp_group_1_p0">0..1</var>'
              '<var id="c">0..1</var><var id="v">1..4</var>'
              '</variables><constraints><group><element>'
              '<matrix>(1,2)(3,4)</matrix><index>%0 %1</index><value>%2</value>'
              '</element><args>__somt_xcsp_group_0 c v</args>'
              '<args>__somt_xcsp_group_1_p0 c v</args></group></constraints></instance>')
    _, script = translated(source)
    context = z3.Context()
    a, b, c, v = z3.Ints('__somt_xcsp_group_0 __somt_xcsp_group_1_p0 c v', ctx=context)
    expected = z3.And(a >= 0, a <= 1, b >= 0, b <= 1, c >= 0, c <= 1,
                      v >= 1, v <= 4, v == 1 + 2 * a + c, v == 1 + 2 * b + c)
    solver = z3.Solver(ctx=context)
    solver.add(z3.Xor(z3.And(*z3.parse_smt2_string(script, ctx=context)), expected))
    assert solver.check() == z3.unsat


def test_large_matrix_group_does_not_expand_cells_per_call():
    # IHTC has 845 lookups into a 40-by-15 matrix. Independent operands
    # exercise the case the list-only helper did not cover.
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              '<array id="m" size="[40][15]">0..1</array>'
              '<array id="r" size="[850]">0..39</array>'
              '<array id="c" size="[850]">0..14</array>'
              '<array id="v" size="[850]">0..1</array>'
              '</variables><constraints><group><element><matrix>m[][]</matrix>'
              '<index>%0 %1</index><value>%2</value></element>'
              + ''.join(f'<args>r[{i}] c[{i}] v[{i}]</args>' for i in range(850))
              + '</group></constraints></instance>')
    _, script = translated(source)
    assert len(script) < 1000000
    assert '(define-fun-rec __somt_xcsp_group_' in script
    context = z3.Context()
    actual = z3.And(*z3.parse_smt2_string(script, ctx=context))
    # Fix all lookup arguments before solving the full exported relation.
    # This checks the large translation without asking the solver to search
    # across 850 independent symbolic matrix accesses.
    assignments = [(z3.Int(f'{name}[{i}]', ctx=context), z3.IntVal(0, ctx=context))
                   for name in ('r', 'c', 'v') for i in range(850)]
    actual = z3.simplify(z3.substitute(actual, *assignments))
    solver = z3.Solver(ctx=context)
    solver.set(timeout=10000)
    solver.add(actual)
    cell = z3.Int('m[0][0]', ctx=context)
    for value, expected in [(1, z3.unsat), (0, z3.sat)]:
        solver.push()
        solver.add(cell == value)
        assert solver.check() == expected, solver.reason_unknown()
        solver.pop()


@pytest.mark.parametrize("row", ['r c', 'r c missing', 'r missing v'])
def test_malformed_matrix_group_rows_are_not_hidden_by_sharing(row):
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              '<array id="m" size="[2][2]">0..1</array>'
              '<var id="r">0..1</var><var id="c">0..1</var><var id="v">0..1</var>'
              '</variables><constraints><group><element><matrix>m[][]</matrix>'
              '<index>%0 %1</index><value>%2</value></element><args>r c v</args>'
              f'<args>{row}</args></group></constraints></instance>')
    result = sp.translate(source=source, language="xcsp3")
    assert not result.ok
