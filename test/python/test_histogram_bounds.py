import pytest
import z3
from tools.semantic_checks.histogram_bounds import prove


def extrema(values, maximum):
    result = values[0]
    for value in values[1:]:
        result = z3.If(result >= value if maximum else result <= value, result, value)
    return result


def instance(size=3, colors=(1, 2), domain=(1, 2), duplicate=False):
    cells = [z3.Int('x' + str(i)) for i in range(size)]
    if duplicate:
        cells[-1] = cells[0]
    counts = [z3.Sum([z3.If(cell == color, 1, 0) for cell in cells]) for color in colors]
    output = z3.Int('spread')
    domains = [bound for cell in cells for bound in (cell >= domain[0], cell <= domain[1])]
    equality = output == extrema(counts, True) - extrema(counts, False)
    return cells, counts, output, domains, equality


def get(assertions):
    records = []
    lemmas = prove(assertions, lambda *args: records.append(args))
    return lemmas, records


@pytest.mark.parametrize('size', [2, 3, 4, 5])
@pytest.mark.parametrize('colors', [(1, 2), (-1, 0, 1)])
@pytest.mark.parametrize('duplicate', [False, True])
def test_derived_bound_follows_from_full_relation(size, colors, duplicate):
    _, _, output, domains, equality = instance(size, colors, (colors[0], colors[-1]), duplicate)
    assertions = [*domains, equality]
    lemmas, records = get(assertions)
    assert len(lemmas) == 1
    assert len([r for r in records if r[0] == 'derived-target-bound']) == 1
    solver = z3.Solver()
    solver.add(*assertions, z3.Not(lemmas[0]))
    assert solver.check() == z3.unsat
    expected = 1 if size % len(colors) else 0
    solver = z3.Solver()
    solver.add(z3.Xor(lemmas[0], output >= expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('fault', ['missing-domain', 'open-cover', 'hidden-domain', 'negated-equality', 'missing-equality'])
def test_no_bounds_from_missing_or_nonpositive_assumptions(fault):
    _, _, _, domains, equality = instance(domain=(1, 3) if fault == 'open-cover' else (1, 2))
    assertions = [*domains, equality]
    if fault == 'missing-domain':
        assertions = [equality]
    elif fault == 'hidden-domain':
        assertions = [z3.Or(z3.Bool('flag'), z3.And(*domains)), equality]
    elif fault == 'negated-equality':
        assertions = [*domains, z3.Not(equality)]
    elif fault == 'missing-equality':
        assertions = domains
    assert get(assertions)[0] == []


@pytest.mark.parametrize('fault', ['duplicate-color', 'unequal-cells', 'weighted-indicator'])
def test_non_histogram_patterns_not_accepted(fault):
    cells, counts, output, domains, equality = instance()
    if fault == 'duplicate-color':
        # Same color at a second, distinct expression with changed multiplicity.
        counts[1] = z3.Sum([z3.If(cell == 1, 1, 0) for cell in cells[::-1]])
    elif fault == 'unequal-cells':
        counts[1] = z3.Sum([z3.If(cell == 2, 1, 0) for cell in cells[:-1]])
    else:
        counts[1] = z3.Sum([z3.If(cell == 2, 2, 0) for cell in cells])
    equality = output == extrema(counts, True) - extrema(counts, False)
    assert get([*domains, equality])[0] == []


def test_arbitrary_expression_needs_its_own_arithmetic_proof():
    _, counts, output, domains, _ = instance()
    assert get([*domains, output == counts[0] - counts[1]])[0] == []


def test_returned_lemma_does_not_omit_other_hard_constraints():
    cells, _, _, domains, equality = instance()
    assertions = [*domains, equality, cells[0] == 3]
    lemmas, _ = get(assertions)
    solver = z3.Solver()
    solver.add(*assertions, *lemmas)
    assert solver.check() == z3.unsat



def test_array_select_coordinates_and_output_preserve_full_relation():
    array = z3.Array('histogram_input', z3.IntSort(), z3.IntSort())
    outputs = z3.Array('histogram_output', z3.IntSort(), z3.IntSort())
    index = z3.Int('histogram_index')
    # The symbolic coordinate can alias a constant coordinate. The proof must
    # preserve multiplicity and remain valid for every such assignment.
    cells = [z3.Select(array, -2), z3.Select(array, 1), z3.Select(array, index)]
    counts = [z3.Sum([z3.If(cell == color, 1, 0) for cell in cells]) for color in (0, 1)]
    output = z3.Select(outputs, 7)
    assertions = [bound for cell in cells for bound in (cell >= 0, cell <= 1)]
    assertions += [index >= -2, index <= 1,
                   output == extrema(counts, True) - extrema(counts, False)]
    lemmas, _ = get(assertions)
    assert len(lemmas) == 1
    source = z3.Solver()
    source.add(*assertions, output == 1)
    assert source.check() == z3.sat
    source = z3.Solver()
    source.add(*assertions, z3.Not(lemmas[0]))
    assert source.check() == z3.unsat


def test_reversed_domain_indicator_and_defining_equality_operands():
    cells = [z3.Int('reverse_cell_' + str(i)) for i in range(3)]
    counts = [z3.Sum([z3.If(z3.IntVal(color) == cell, 1, 0) for cell in cells])
              for color in (1, 2)]
    output = z3.Int('reverse_spread')
    assertions = [bound for cell in cells
                  for bound in (z3.IntVal(1) <= cell, z3.IntVal(3) > cell)]
    assertions.append(extrema(counts, True) - extrema(counts, False) == output)
    lemmas, _ = get(assertions)
    assert len(lemmas) == 1
    source = z3.Solver()
    source.add(*assertions, output == 1)
    assert source.check() == z3.sat
    source = z3.Solver()
    source.add(*assertions, z3.Not(lemmas[0]))
    assert source.check() == z3.unsat
