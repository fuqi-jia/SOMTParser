"""The linear circuit encoding preserves projections and cyclic witnesses."""
import itertools
import pytest
import somtparser as sp
z3 = pytest.importorskip("z3")


def _translate(size, start=0, required=None):
    last = start + size - 1
    count = f"<size>{required}</size>" if required is not None else ""
    source = f'''<instance format="XCSP3" type="CSP"><variables>
      <array id="x" size="[{size}]">{start}..{last}</array></variables>
      <constraints><circuit><list startIndex="{start}">x[]</list>{count}</circuit></constraints></instance>'''
    result = sp.translate(source=source, language="xcsp3")
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.add(*z3.parse_smt2_string(result.to_smt2(sp.OmtDialect.Z3)))
    return result, solver


def _one_cycle(successors, start, required=None):
    n = len(successors)
    if len(set(successors)) != n:
        return False
    active = {i for i, nxt in enumerate(successors) if nxt != start + i}
    if len(active) < 2 or required is not None and len(active) != required:
        return False
    first = min(active)
    seen, node = set(), first
    while node not in seen:
        seen.add(node)
        node = successors[node] - start
    return node == first and seen == active


@pytest.mark.parametrize("start,required", [(0,None), (-3,None), (7,3)])
def test_circuit_projection_matches_all_successor_assignments(start, required):
    _, solver = _translate(4, start, required)
    for assignment in itertools.product(range(start,start+4), repeat=4):
        solver.push()
        solver.add(*(z3.Int(f"x[{i}]") == nxt for i,nxt in enumerate(assignment)))
        assert (solver.check() == z3.sat) == _one_cycle(assignment,start,required), assignment
        solver.pop()


def test_circuit_has_one_witness_per_cycle_rotation():
    _, solver = _translate(3)
    # The unchanged source model has three 2-cycles and two 3-cycles.
    # Their rank rotations yield 3*2 + 2*3 = 12 complete target models.
    count = 0
    while solver.check() == z3.sat:
        model = solver.model()
        constants = [symbol() for symbol in model.decls() if symbol.arity() == 0]
        solver.add(z3.Or(*(symbol != model.eval(symbol, model_completion=True) for symbol in constants)))
        count += 1
        assert count <= 12
    assert count == 12
