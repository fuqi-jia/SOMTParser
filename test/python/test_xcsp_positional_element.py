"""Independent relations for shared positional indexed-element helpers."""
import pytest
import somtparser as sp

z3 = pytest.importorskip('z3')


def _translate(body, declarations):
    source = ('<instance format="XCSP3" type="CSP"><variables>' + declarations
              + '</variables><constraints>' + body + '</constraints></instance>')
    result = sp.translate(source=source, language='xcsp3')
    assert result.ok, [d.message for d in result.diagnostic_items]
    script = result.to_smt2()
    return script, z3.And(*z3.parse_smt2_string(script))


@pytest.mark.parametrize('start', [-2, 0, 5])
@pytest.mark.parametrize('alias', [False, True])
def test_positional_helper_keeps_cells_aliases_and_index_boundaries(start, alias):
    a, b, i, j, v, w = z3.Ints('a b i j v w')
    declarations = ('<var id="a">-2..2</var><var id="b">-2..2</var>'
                    f'<var id="i">{start-1}..{start+3}</var>'
                    f'<var id="j">{start-1}..{start+3}</var>'
                    '<var id="v">-2..2</var><var id="w">-2..2</var>')
    index, value = ('a', 'a') if alias else ('i', 'v')
    body = (f'<element><list startIndex="{start}">a b a</list><index>{index}</index>'
            f'<value>{value}</value></element>'
            f'<element><list startIndex="{start}">b a -1</list><index>j</index>'
            '<value>w</value></element>')
    script, actual = _translate(body, declarations)
    assert script.count('(define-fun ') == 1
    ix, val = (a, a) if alias else (i, v)
    expected = z3.And(*[z3.And(x >= -2, x <= 2) for x in (a, b, v, w)],
                      i >= start-1, i <= start+3, j >= start-1, j <= start+3,
                      z3.Or(*[z3.And(ix == start+k, val == x)
                              for k, x in enumerate((a, b, a))]),
                      z3.Or(*[z3.And(j == start+k, w == x)
                              for k, x in enumerate((b, a, -1))]))
    solver = z3.Solver()
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


def test_different_start_indexes_and_arities_get_different_helpers():
    declarations = ''.join(f'<var id="{n}">-2..4</var>' for n in 'abiv')
    body = ('<element><list>a b</list><index>i</index><value>v</value></element>'
            '<element><list startIndex="-1">a b</list><index>i</index><value>v</value></element>'
            '<element><list>a b a</list><index>i</index><value>v</value></element>')
    script, actual = _translate(body, declarations)
    assert script.count('(define-fun ') == 3
    a, b, i, v = z3.Ints('a b i v')
    expected = z3.And(*[z3.And(x >= -2, x <= 4) for x in (a,b,i,v)],
                      z3.Or(z3.And(i==0,v==a),z3.And(i==1,v==b)),
                      z3.Or(z3.And(i==-1,v==a),z3.And(i==0,v==b)),
                      z3.Or(z3.And(i==0,v==a),z3.And(i==1,v==b),z3.And(i==2,v==a)))
    solver = z3.Solver()
    solver.add(z3.Xor(actual,expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('rank', ['first', 'last'])
def test_rank_is_not_erased_by_equality_helper(rank):
    declarations = ''.join(f'<var id="{n}">0..2</var>' for n in 'abiv')
    body = (f'<element><list>a b a</list><index rank="{rank}">i</index>'
            '<value>v</value></element>')
    _, actual = _translate(body, declarations)
    a,b,i,v = z3.Ints('a b i v')
    entries = (a,b,a)
    expected = z3.And(*[z3.And(x>=0,x<=2) for x in (a,b,i,v)], z3.Or(*[
        z3.And(i==k,entry==v,*[entries[j]!=v for j in
               (range(k) if rank=='first' else range(k+1,3))])
        for k,entry in enumerate(entries)]))
    solver = z3.Solver()
    solver.add(z3.Xor(actual,expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('index', ['div(i,0)', 'mod(i,0)', '0'])
def test_nonvariable_index_is_rejected_before_positional_helper(index):
    source = ('<instance format="XCSP3" type="CSP"><variables>'
              '<var id="i">0..1</var><var id="v">0..1</var></variables>'
              '<constraints><element><list>0 1</list><index>' + index
              + '</index><value>v</value></element></constraints></instance>')
    result = sp.translate(source=source, language='xcsp3')
    assert not result.ok
    assert any('declared' in d.message for d in result.diagnostic_items)
