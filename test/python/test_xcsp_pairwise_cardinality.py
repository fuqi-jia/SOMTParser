"""Complete pair compression checked against the original edge relation."""
import itertools

import pytest
import somtparser as sp
import z3


STRATEGY = 'complete-pairwise-or-cardinality'
NAMES = [f'x{i}' for i in range(6)]
EDGES = list(itertools.combinations(NAMES, 2))


def compile_pairs(expression, rows, names=NAMES, extra=None):
    domains = {name: '-3..3' for name in names}
    domains.update(extra or {})
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              + ''.join(f'<var id="{name}">{domain}</var>' for name, domain in domains.items())
              + '</variables><constraints><group><intension>' + expression
              + '</intension>' + ''.join('<args>' + row + '</args>' for row in rows)
              + '</group></constraints></instance>')
    result = sp.translate(source=source, language='xcsp3')
    assert result.ok, [d.message for d in result.diagnostic_items]
    ctx = z3.Context()
    solver = z3.Solver(ctx=ctx)
    solver.set(timeout=3000)
    solver.add(z3.parse_smt2_string(result.to_smt2(), ctx=ctx))
    return solver, STRATEGY in result.report.to_json()


def assignments(solver, domains, expected):
    for values in itertools.product(*domains.values()):
        assignment = dict(zip(domains, values))
        solver.push()
        solver.add(*(z3.Int(name, ctx=solver.ctx) == value for name, value in assignment.items()))
        assert solver.check() == (z3.sat if expected(assignment) else z3.unsat), assignment
        solver.pop()


@pytest.mark.parametrize('divisor', [-2, 2])
@pytest.mark.parametrize('reverse_body', [False, True])
def test_complete_pairs_match_all_source_assignments(divisor, reverse_body):
    parts = ['ne(mod(%0,%1),0)', 'ne(mod(%2,%1),0)']
    if reverse_body:
        parts.reverse()
    solver, compressed = compile_pairs('or(' + ','.join(parts) + ')',
                                      [f'{a} {divisor} {b}' for a, b in EDGES])
    assert compressed
    assignments(solver, {name: [-2, 1] for name in NAMES},
                lambda v: all(v[a] % divisor != 0 or v[b] % divisor != 0 for a, b in EDGES))


def test_duplicate_and_reversed_edges_do_not_change_coverage():
    edges = EDGES + [(b, a) for a, b in EDGES] + EDGES[:3]
    solver, compressed = compile_pairs('or(ne(mod(%0,2),0),ne(mod(%1,2),0))',
                                      [f'{a} {b}' for a, b in edges])
    assert compressed
    assignments(solver, {name: [0, 1] for name in NAMES},
                lambda v: all(v[a] % 2 or v[b] % 2 for a, b in edges))


@pytest.mark.parametrize('kind', ['missing-edge', 'self-edge', 'asymmetric'])
def test_ineligible_pair_relations_keep_their_source_semantics(kind):
    edges = EDGES[1:] * 2 if kind == 'missing-edge' else EDGES[:]
    if kind == 'self-edge':
        edges.append(('x0', 'x0'))
    rhs_divisor = 3 if kind == 'asymmetric' else 2
    solver, compressed = compile_pairs(f'or(ne(mod(%0,2),0),ne(mod(%1,{rhs_divisor}),0))',
                                      [f'{a} {b}' for a, b in edges])
    assert not compressed
    assignments(solver, {name: [0, 1] for name in NAMES},
                lambda v: all(v[a] % 2 or v[b] % rhs_divisor for a, b in edges))
    if kind == 'asymmetric':
        assignments(solver, {name: [2, 3] for name in NAMES},
                    lambda v: all(v[a] % 2 or v[b] % 3 for a, b in edges))


def test_literal_classes_can_mix_complete_and_incomplete_graphs():
    rows = [f'{a} 2 {b}' for a, b in EDGES] + [f'{a} 3 {b}' for a, b in EDGES[1:]] * 2
    solver, compressed = compile_pairs('or(ne(mod(%0,%1),0),ne(mod(%2,%1),0))', rows)
    assert compressed
    assignments(solver, {name: [2, 3] for name in NAMES},
                lambda v: (all(v[a] % 2 or v[b] % 2 for a, b in EDGES)
                           and all(v[a] % 3 or v[b] % 3 for a, b in EDGES[1:])))


@pytest.mark.parametrize('guarded', [False, True])
def test_global_divisor_definedness_survives_pair_optimization(guarded):
    def predicate(slot):
        term = f'mod(%{slot},d)'
        if guarded:
            term = 'if(eq(d,0),1,' + term + ')'
        return 'ne(' + term + ',0)'
    solver, _ = compile_pairs('or(' + predicate(0) + ',' + predicate(1) + ')',
                              [f'{a} {b}' for a, b in EDGES], extra={'d': '-2..2'})
    assignments(solver, dict({name: [-2, 1] for name in NAMES}, d=[-2, 0, 2]),
                lambda v: guarded if v['d'] == 0 else all(
                    v[a] % v['d'] or v[b] % v['d'] for a, b in EDGES))


@pytest.mark.parametrize('size', [64, 65])
def test_recognizer_boundary_retains_exact_fallback(size):
    names = [f'v{i}' for i in range(size)]
    edges = list(itertools.combinations(names, 2))
    solver, compressed = compile_pairs('or(ne(mod(%0,2),0),ne(mod(%1,2),0))',
                                      [f'{a} {b}' for a, b in edges], names)
    assert compressed == (size == 64)
    assignments(solver, {name: [0, 1] if i < 2 else [1] for i, name in enumerate(names)},
                lambda v: all(v[a] % 2 or v[b] % 2 for a, b in edges))
