"""Original-index and polarity checks for MiniZinc graph-global adaptation."""
import itertools
import pytest
import z3
import somtparser as sp


def connected(from_, to, nodes, edges, directed):
    selected = {i for i, b in enumerate(nodes) if b}
    if not selected or any(b and (u not in selected or v not in selected)
                           for u, v, b in zip(from_, to, edges)):
        return False
    for root in selected:
        seen = {root}
        while True:
            next_seen = seen | {v for u, v, b in zip(from_, to, edges) if b and u in seen}
            if not directed:
                next_seen |= {u for u, v, b in zip(from_, to, edges) if b and v in seen}
            if next_seen == seen:
                break
            seen = next_seen
        if selected <= seen:
            return True
    return False


@pytest.mark.parametrize('directed', [False, True])
@pytest.mark.parametrize('negated', [False, True])
@pytest.mark.parametrize('from_,to', [([0,1], [1,2]), ([0,2], [1,1]), ([0,0], [0,1])])
def test_original_nonzero_axes_against_exhaustive_graph_search(directed, negated, from_, to):
    name = 'dconnected' if directed else 'connected'
    decl = ('array[3..4]of -1..1:f=array1d(3..4,[' + ','.join(str(i-1) for i in from_) + ']);'
            'array[3..4]of -1..1:t=array1d(3..4,[' + ','.join(str(i-1) for i in to) + ']);'
            'array[-1..1]of var bool:ns;array[3..4]of var bool:es;')
    result = sp.translate(source=decl+'constraint '+('not ' if negated else '')
                          +name+'(f,t,ns,es);solve satisfy;', language='minizinc')
    assert result.ok, [d.message for d in result.diagnostic_items]
    formula = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    ns = z3.Array('ns', z3.IntSort(), z3.BoolSort())
    es = z3.Array('es', z3.IntSort(), z3.BoolSort())
    solver = z3.Solver(); solver.set(timeout=5000)
    solver.add(formula)
    for bits in itertools.product([False, True], repeat=5):
        expected = connected(from_, to, bits[:3], bits[3:], directed) != negated
        solver.push()
        solver.add(*[ns[i-1] == bits[i] for i in range(3)],
                   *[es[i+3] == bits[i+3] for i in range(2)])
        assert solver.check() == (z3.sat if expected else z3.unsat), bits
        solver.pop()


@pytest.mark.parametrize('name', ['connected', 'dconnected'])
def test_empty_graph_is_false_and_negation_is_true(name):
    for prefix, expected in [('',z3.unsat), ('not ',z3.sat)]:
        r=sp.translate(source='constraint '+prefix+name+'([],[],[],[]);solve satisfy;',language='minizinc')
        assert r.ok,[d.message for d in r.diagnostic_items]
        s=z3.Solver();s.add(z3.parse_smt2_string(r.to_smt2()));assert s.check()==expected


@pytest.mark.parametrize('decl,args', [
    ('array[0..0]of int:f=array1d(0..0,[1]);array[1..1]of int:t=array1d(1..1,[1]);', 'f,t,[true],[true]'),
    ('', '[2],[1],[true],[true]'),
    ('var int:x;', '[x],[1],[true],[true]'),
    ('', '[1],[1],[1],[true]'),
    ('', '[1],[1],[true],[1]'),
    ('array[1..0]of bool:f=[];', 'f,[],[],[]'),
])
def test_malformed_graph_shapes_and_types_are_rejected(decl,args):
    r=sp.translate(source=decl+'constraint connected('+args+');solve satisfy;',language='minizinc')
    assert not r.ok


def test_nominal_enum_node_and_edge_indices_are_preserved():
    source = '''
        enum Node = {a, b, c}; enum Edge = {ab, bc};
        array[Edge] of Node: from = [a, b];
        array[Edge] of Node: to = [b, c];
        array[Node] of var bool: ns;
        array[Edge] of var bool: es;
        constraint connected(from, to, ns, es);
        constraint forall(i in Node)(ns[i]);
        constraint forall(i in Edge)(es[i]);
        solve satisfy;
    '''
    translated = sp.translate(source=source, language='minizinc')
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    solver = z3.Solver()
    solver.add(z3.parse_smt2_string(translated.to_smt2()))
    assert solver.check() == z3.sat

    # Equal underlying ordinal values do not make different enum types equal.
    mismatched = source.replace('array[Edge] of Node: from = [a, b];',
                                'array[Edge] of Edge: from = [ab, bc];')
    assert not sp.translate(source=mismatched, language='minizinc').ok


@pytest.mark.parametrize('name', ['connected', 'dconnected', 'fzn_connected', 'fzn_dconnected'])
@pytest.mark.parametrize('definition', ['test', 'function bool:'])
def test_explicit_graph_definition_keeps_its_own_semantics(name, definition):
    source = f'''
        {definition} {name}(array[int] of int: f, array[int] of int: t,
                            array[int] of bool: ns, array[int] of bool: es,) = false;
        constraint {name}([1], [1], [true], [true]);
        solve satisfy;
    '''
    translated = sp.translate(source=source, language='minizinc')
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    solver = z3.Solver()
    solver.add(z3.parse_smt2_string(translated.to_smt2()))
    assert solver.check() == z3.unsat


def test_predicate_and_function_definition_trailing_commas():
    source = '''
        predicate positive(var int: x,) = x > 0;
        function int: next(int: x,) = x + 1;
        constraint positive(next(2));
        solve satisfy;
    '''
    translated = sp.translate(source=source, language='minizinc')
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    solver = z3.Solver()
    solver.add(z3.parse_smt2_string(translated.to_smt2()))
    assert solver.check() == z3.sat
