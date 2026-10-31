"""Tuple allDifferent stays injective across heterogeneous integer domains."""
import itertools

import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


def _translate(domains, rows, exceptions=()):
    declarations = ''.join(f'<var id="{name}">{domain}</var>'
                           for name, domain in domains.items())
    lists = ''.join('<list>' + ' '.join(row) + '</list>' for row in rows)
    excluded = ('<except>' + ''.join('(' + ','.join(map(str, row)) + ')'
                                    for row in exceptions) + '</except>') if exceptions else ''
    source = ('<instance format="XCSP3" type="CSP"><variables>' + declarations
              + '</variables><constraints><allDifferent>' + lists + excluded
              + '</allDifferent></constraints></instance>')
    result = sp.translate(source=source, language='xcsp3')
    assert result.ok, [d.message for d in result.diagnostic_items]
    script = result.to_smt2()
    return script, z3.And(*z3.parse_smt2_string(script))


@pytest.mark.parametrize('rows', [
    [('a', 'b'), ('c', 'd'), ('e', 'f')],
    [('a', 'a'), ('c', 'd'), ('e', 'f')],
    [('a', 'b'), ('c', 'd'), ('a', 'b')],
    [('a', 'b'), ('b', 'a'), ('e', 'f')],
    [('a', 'b', 'c'), ('d', 'e', 'f')],
])
@pytest.mark.parametrize('sparse', [False, True])
def test_tuple_encoding_equals_componentwise_relation(rows, sparse):
    values = {'a': [-2, 1], 'b': [0, 1], 'c': [-1, 1],
              'd': [-2, 0], 'e': [0, 2], 'f': [-1, 0]}
    domains = {name: ' '.join(map(str, vs)) if sparse else f'{vs[0]}..{vs[-1]}'
               for name, vs in values.items()}
    script, actual = _translate(domains, rows)
    # The shared lowerer alpha-renames the builtin spelling e. Keep the
    # source fixture and independent componentwise oracle, aligning only
    # this known source/target symbol correspondence.
    assert '(declare-fun e!0 () Int)' in script or '(declare-const e!0 Int)' in script
    symbols = {name: z3.Int('e!0' if name == 'e' else name) for name in domains}
    domain_formula = [z3.Or(*[symbols[name] == v for v in vs]) if sparse
                      else z3.And(symbols[name] >= vs[0], symbols[name] <= vs[-1])
                      for name, vs in values.items()]
    distinct = [z3.Or(*[symbols[a] != symbols[b] for a, b in zip(left, right)])
                for left, right in itertools.combinations(rows, 2)]
    solver = z3.Solver()
    solver.set(timeout=10000)
    solver.add(z3.Xor(actual, z3.And(*domain_formula, *distinct)))
    assert solver.check() == z3.unsat


def test_full_signed_range_radix_does_not_overflow_or_collapse_endpoints():
    lo, hi = -(2**63), 2**63 - 1
    domains = {'a': f'{lo}..{hi}', 'b': f'{lo}..{hi}',
               'c': f'{lo}..{hi}', 'd': f'{lo}..{hi}'}
    script, actual = _translate(domains, [('a', 'b'), ('c', 'd')])
    assert '18446744073709551616' in script
    a, b, c, d = z3.Ints('a b c d')
    expected = z3.And(*[z3.And(v >= lo, v <= hi) for v in (a, b, c, d)],
                      z3.Or(a != c, b != d))
    solver = z3.Solver()
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


def test_constant_columns_and_repeated_tuple_exceptions_preserve_semantics():
    domains = {'a': '0..1', 'b': '3', 'c': '0..1', 'd': '3'}
    _, actual = _translate(domains, [('a', 'b'), ('c', 'd')], [(0, 3)])
    a, b, c, d = z3.Ints('a b c d')
    expected = z3.And(a >= 0, a <= 1, c >= 0, c <= 1, b == 3, d == 3,
                      z3.Or(a != c, a == 0, c == 0))
    solver = z3.Solver()
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


def test_many_tuples_emit_one_linear_size_distinct_expression():
    domains = {f'x{i}': '0..31' for i in range(6000)}
    rows = [tuple(f'x{i * 6 + j}' for j in range(6)) for i in range(1000)]
    script, _ = _translate(domains, rows)
    assert script.count('(distinct ') == 1
    assert len(script) < 1500000
