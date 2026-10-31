"""Bin packing keeps exact weighted/reified semantics without a bins × items graph."""
import pytest
import z3
import somtparser as sp


def translated(source):
    result = sp.translate(source=source, language='minizinc', dialect=sp.OmtDialect.Z3)
    assert result.ok, [d.message for d in result.diagnostic_items]
    return result.to_smt2(sp.OmtDialect.Z3)


@pytest.mark.parametrize('lower, weights', [(-1, [2, 0, 3]), (3, [1, 1, 1]),
                                           (0, []), (-2, [0, 0]), (1, [7])])
def test_weighted_histogram_is_equivalent_in_both_boolean_polarities(lower, weights):
    upper = lower + 2
    total = sum(weights)
    n = len(weights)
    source = f'''
include "bin_packing_load.mzn";
array[{lower}..{upper}] of var 0..{total}: load;
array[2..{n + 1}] of var {lower - 1}..{upper + 1}: bin;
array[2..{n + 1}] of int: weight = array1d(2..{n + 1}, {weights});
var bool: accepted;
constraint accepted = bin_packing_load(load, bin, weight);
solve satisfy;
'''
    actual = z3.And(*z3.parse_smt2_string(translated(source)))
    load = z3.Array('load', z3.IntSort(), z3.IntSort())
    bins = z3.Array('bin', z3.IntSort(), z3.IntSort())
    accepted = z3.Bool('accepted')
    declarations = [z3.And(load[b] >= 0, load[b] <= total)
                    for b in range(lower, upper + 1)]
    declarations += [z3.And(bins[i + 2] >= lower - 1, bins[i + 2] <= upper + 1)
                     for i in range(n)]
    relation = [z3.And(bins[i + 2] >= lower, bins[i + 2] <= upper)
                for i in range(n)]
    relation += [load[b] == z3.Sum([z3.If(bins[i + 2] == b, w, 0)
                                  for i, w in enumerate(weights)])
                 for b in range(lower, upper + 1)]
    expected = z3.And(*declarations, accepted == z3.And(*relation))
    solver = z3.Solver()
    solver.set(timeout=10000)
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


def test_large_bin_item_product_exports_as_a_shared_linear_dag():
    source = '''
include "bin_packing_load.mzn";
array[1..128] of var 0..256: load;
array[1..256] of var 1..128: bin;
constraint bin_packing_load(load, bin, [1 | i in 1..256]);
solve satisfy;
'''
    script = translated(source)
    # This size bound catches reintroducing an item-by-bin expansion while
    # allowing normal changes in naming and SMT formatting.
    assert len(script.encode()) < 400000
    solver = z3.Solver()
    solver.set(timeout=10000)
    solver.add(*z3.parse_smt2_string(script))
    bins = z3.Array('bin', z3.IntSort(), z3.IntSort())
    load = z3.Array('load', z3.IntSort(), z3.IntSort())
    solver.add(*[bins[i] == (i - 1) % 128 + 1 for i in range(1, 257)])
    solver.add(z3.Or(*[load[i] != 2 for i in range(1, 129)]))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('weights', ['[-1]', '[1, 2]'])
def test_invalid_weight_arguments_remain_errors(weights):
    result = sp.translate(source=f'''
include "bin_packing_load.mzn";
array[1..2] of var 0..5: load;
array[1..1] of var 1..2: bin;
constraint bin_packing_load(load, bin, {weights});
solve satisfy;
''', language='minizinc')
    assert not result.ok
    assert any('weights' in d.message or 'index sets' in d.message
               for d in result.diagnostic_items)
