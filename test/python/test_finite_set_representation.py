import pytest
import z3

from tools.semantic_checks.finite_set_representation import prove_finite_set_representations


def carrier(entries):
    result = z3.K(z3.IntSort(), z3.BoolVal(False))
    for index, value in entries:
        result = z3.Store(result, index, value)
    return result


def domain(value, support, swap=False):
    p, q = z3.Bools('p q')
    intersection = z3.Map(z3.And(p, q).decl(), support, value)
    return value == intersection if swap else intersection == value


def derive(assertions):
    records = []
    lemmas = prove_finite_set_representations(assertions, lambda *args: records.append(args))
    for premise, lemma, answer, query in records:
        checker = z3.Solver(); checker.from_string(query)
        assert str(checker.check()) == answer
        if answer == 'unsat':
            checker = z3.Solver(); checker.add(premise, z3.Not(lemma))
            assert checker.check() == z3.unsat
    return lemmas, records


@pytest.mark.parametrize('swap', [False, True])
def test_hard_finite_carrier_yields_proved_whole_array_equality(swap):
    value = z3.Array('s', z3.IntSort(), z3.BoolSort())
    lemmas, records = derive([domain(value, carrier([(-3, True), (4, True)]), swap)])
    assert len(lemmas) == len(records) == 1
    checker = z3.Solver(); checker.add(lemmas[0], z3.Select(value, 100))
    assert checker.check() == z3.unsat
    checker = z3.Solver(); checker.add(lemmas[0], z3.Select(value, -3), z3.Not(z3.Select(value, 4)))
    assert checker.check() == z3.sat


@pytest.mark.parametrize('entries', [[], [(2, True), (2, False)], [(-7, True), (0, True), (8, True)]])
def test_empty_overwritten_and_sparse_support(entries):
    value = z3.Array('s', z3.IntSort(), z3.BoolSort())
    lemmas, _ = derive([domain(value, carrier(entries))])
    assert len(lemmas) == 1


@pytest.mark.parametrize('wrapper', ['not', 'or', 'implies'])
def test_nonasserted_domains_cannot_supply_global_lemmas(wrapper):
    value = z3.Array('s', z3.IntSort(), z3.BoolSort()); p = z3.Bool('p')
    equality = domain(value, carrier([(1, True)]))
    wrapped = {'not': z3.Not(equality), 'or': z3.Or(p, equality), 'implies': z3.Implies(p, equality)}[wrapper]
    assert derive([wrapped]) == ([], [])


def test_binder_local_domain_is_not_promoted():
    value = z3.Array('s', z3.IntSort(), z3.BoolSort()); i = z3.Int('i')
    assert derive([z3.Exists([i], z3.And(domain(value, carrier([(1, True)])), i > 0))]) == ([], [])


@pytest.mark.parametrize('kind', ['symbolic', 'cofinite'])
def test_unknown_or_infinite_carriers_are_not_truncated(kind):
    value = z3.Array('s', z3.IntSort(), z3.BoolSort())
    support = z3.Array('D', z3.IntSort(), z3.BoolSort()) if kind == 'symbolic' else z3.K(z3.IntSort(), z3.BoolVal(True))
    assert derive([domain(value, support)]) == ([], [])


def test_unknown_proof_cannot_return_a_lemma(monkeypatch):
    value = z3.Array('s', z3.IntSort(), z3.BoolSort()); records = []
    monkeypatch.setattr(type(z3.Solver()), 'check', lambda self: z3.unknown)
    assert prove_finite_set_representations([domain(value, carrier([(1, True)]))], lambda *r: records.append(r)) == []
    assert records[0][2] == 'unknown'


def test_distinct_array_cells_keep_distinct_carriers():
    array = z3.Array('a', z3.IntSort(), z3.ArraySort(z3.IntSort(), z3.BoolSort()))
    first, second = domain(array[0], carrier([(-1, True)])), domain(array[2], carrier([(5, True)]))
    lemmas, _ = derive([z3.And(first, second)])
    assert len(lemmas) == 2
    solver = z3.Solver(); solver.add(*lemmas, array[0][-1], array[2][5])
    assert solver.check() == z3.sat
    solver = z3.Solver(); solver.add(*lemmas, array[0][5])
    assert solver.check() == z3.unsat


def test_missing_one_support_element_has_real_counterexample():
    value = z3.Array('s', z3.IntSort(), z3.BoolSort())
    original = domain(value, carrier([(1, True), (9, True)]))
    wrong = value == z3.Store(z3.K(z3.IntSort(), z3.BoolVal(False)), 1, value[1])
    solver = z3.Solver(); solver.add(original, z3.Not(wrong))
    assert solver.check() == z3.sat
    lemmas, _ = derive([original]); solver = z3.Solver(); solver.add(original, z3.Not(lemmas[0]))
    assert solver.check() == z3.unsat
