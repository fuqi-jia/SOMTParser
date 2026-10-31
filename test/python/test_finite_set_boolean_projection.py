import itertools

import pytest
import z3

from tools.semantic_checks.finite_set_boolean_projection import project_finite_sets_to_booleans


def finite(values):
    result = z3.EmptySet(z3.IntSort())
    for value in values:
        result = z3.SetAdd(result, value)
    return result


def domain(value, carrier):
    a, b = z3.Bools('map_operand_a map_operand_b')
    return value == z3.Map(z3.And(a, b).decl(), value, finite(carrier))


def checked(assertions, allow_index_declines=False):
    proofs = []
    result = project_finite_sets_to_booleans(assertions, lambda *row: proofs.append(row))
    assert all(row[2] == 'unsat' or (allow_index_declines and row[2] == 'sat') for row in proofs)
    for premise, lemma, answer, query in proofs:
        replay = z3.Solver()
        replay.from_string(query)
        assert str(replay.check()) == answer
    return result


def close(result, assertions):
    # The carrier implications are independently proved by checked().  Verify
    # the second step pointwise over ALL fresh memberships, without quantifying
    # arrays (Z3 returns unknown for that unrelated quantified-array oracle).
    original = z3.And(*assertions)
    rewritten = z3.substitute(original, *result.substitutions) if result.substitutions else original
    solver = z3.Solver()
    solver.add(z3.Xor(rewritten, result.formula))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('carrier', [[], [-2], [-2, 3], [0, 1, 2]])
def test_exact_all_subsets_and_outside_exclusion(carrier):
    s = z3.Const('s', z3.SetSort(z3.IntSort()))
    public = z3.Int('cost')
    assertions = [domain(s, carrier), public == z3.Sum([z3.If(z3.IsMember(i, s), 1, 0) for i in carrier])]
    result = checked(assertions)
    assert len(result.eliminated_variables) == 1
    assert len(result.boolean_witnesses) == len(carrier)
    close(result, assertions)
    representation = result.substitutions[0][1]
    for bits in itertools.product([False, True], repeat=len(carrier)):
        actual = finite([value for value, bit in zip(carrier, bits) if bit])
        a = z3.Solver(); a.add(*assertions, s == actual)
        b = z3.Solver(); b.add(result.formula, representation == actual)
        assert a.check() == b.check() == z3.sat
        assert a.model().eval(public).as_long() == b.model().eval(public).as_long() == sum(bits)
    outside = min(carrier, default=0) - 1
    rejected = z3.Solver(); rejected.add(result.formula, z3.IsMember(outside, representation))
    assert rejected.check() == z3.unsat


@pytest.mark.parametrize('operation', ['union', 'intersection', 'difference', 'complement', 'conditional'])
def test_symbolic_map_defaults_and_support(operation):
    s, t = z3.Consts('s t', z3.SetSort(z3.IntSort()))
    flag = z3.Bool('flag')
    operations = {'union':z3.SetUnion(s,t), 'intersection':z3.SetIntersect(s,t),
                  'difference':z3.SetDifference(s,t), 'complement':z3.SetComplement(s),
                  'conditional':z3.If(flag,s,t)}
    value = operations[operation]
    expected = z3.SetComplement(finite([-2])) if operation=='complement' else finite([3])
    assertions = [domain(s, [-2, 3]), domain(t, [3, 7]), flag == (value == expected)]
    result = checked(assertions)
    close(result, assertions)
    representations = {str(left): right for left, right in result.substitutions}
    # Exhaust every admissible source set and both public flag values.  Python
    # set algebra is independent of both Z3's array solver and the rewrite.
    for sbits, tbits, flag_value in itertools.product(
            itertools.product([False, True], repeat=2),
            itertools.product([False, True], repeat=2), [False, True]):
        sv = {i for i, bit in zip([-2, 3], sbits) if bit}
        tv = {i for i, bit in zip([3, 7], tbits) if bit}
        if operation == 'complement':
            equal = sv == {-2}
        else:
            output = {'union': sv | tv, 'intersection': sv & tv,
                      'difference': sv - tv,
                      'conditional': sv if flag_value else tv}[operation]
            equal = output == {3}
        expected_answer = z3.sat if flag_value == equal else z3.unsat
        source = z3.Solver()
        source.add(*assertions, s == finite(sorted(sv)), t == finite(sorted(tv)), flag == flag_value)
        projected = z3.Solver()
        projected.add(result.formula, representations['s'] == finite(sorted(sv)),
                      representations['t'] == finite(sorted(tv)), flag == flag_value)
        assert source.check() == projected.check() == expected_answer
    todo = [result.formula]; seen=set()
    while todo:
        term=todo.pop()
        if term.get_id()in seen:continue
        seen.add(term.get_id())
        assert term.sort().kind()!=z3.Z3_ARRAY_SORT
        todo.extend(term.children())


def test_last_store_wins_and_default_true_is_checked():
    s=z3.Const('s',z3.SetSort(z3.IntSort()));b=z3.Bool('b')
    rewritten=z3.Store(z3.Store(z3.SetComplement(s),3,b),3,z3.Not(b))
    assertions=[domain(s,[3]), rewritten==finite([])]
    result=checked(assertions);close(result,assertions)
    solver=z3.Solver();solver.add(result.formula);assert solver.check()==z3.unsat


def test_distinct_cells_and_literal_aliases_keep_independent_memberships():
    a=z3.Array('a',z3.IntSort(),z3.SetSort(z3.IntSort()));p=z3.Int('public')
    cell0=z3.Select(a,z3.IntVal(1)-1);cell1=z3.Select(a,1)
    assertions=[domain(cell0,[-3,7]),domain(cell1,[2]),z3.Select(a,0)==finite([7]),cell1==finite([2]),p==z3.If(z3.IsMember(7,cell0),4,5)]
    result=checked(assertions);assert len(result.eliminated_variables)==1
    assert len(result.boolean_witnesses)==3
    close(result,assertions)
    solver=z3.Solver();solver.add(result.formula,p!=4);assert solver.check()==z3.unsat


@pytest.mark.parametrize('extra', ['dynamic', 'missing_cell', 'whole_array', 'store_base'])
def test_nonlocal_array_uses_decline_entire_array(extra):
    a=z3.Array('a',z3.IntSort(),z3.SetSort(z3.IntSort()));i=z3.Int('i')
    assertions=[domain(a[0],[1]),domain(a[1],[2])]
    additions={'dynamic':a[i]==finite([1]),'missing_cell':a[2]==finite([]),
               'whole_array':a==z3.K(z3.IntSort(),finite([])),
               'store_base':z3.Store(a,2,finite([]))==a}
    assertions.append(additions[extra]);result=checked(assertions, allow_index_declines=True)
    assert not result.eliminated_variables and not result.boolean_witnesses
    assert result.formula.eq(z3.And(*assertions))


@pytest.mark.parametrize('context', ['not','or','implies','reified'])
def test_conditional_carriers_are_not_hard_domains(context):
    s=z3.Const('s',z3.SetSort(z3.IntSort()));flag=z3.Bool('flag');d=domain(s,[1])
    bodies={'not':z3.Not(d),'or':z3.Or(flag,d),'implies':z3.Implies(flag,d),'reified':flag==d}
    result=checked([bodies[context],z3.IsMember(99,s)])
    assert not result.eliminated_variables
    solver=z3.Solver();solver.add(result.formula);assert solver.check()==z3.sat


def test_multiple_domains_still_retain_tightest_constraint():
    s=z3.Const('s',z3.SetSort(z3.IntSort()));assertions=[domain(s,[1,2]),domain(s,[2,3]),z3.IsMember(1,s)]
    result=checked(assertions);close(result,assertions)
    solver=z3.Solver();solver.add(result.formula);assert solver.check()==z3.unsat


def test_objective_query_has_no_candidate_fixing():
    s=z3.Const('s',z3.SetSort(z3.IntSort()));cost=z3.Int('cost')
    original=[domain(s,[0,1]),cost==z3.If(z3.IsMember(0,s),1,0)+z3.If(z3.IsMember(1,s),1,0)]
    for bound, expected in [(0,z3.unsat),(1,z3.sat),(2,z3.sat)]:
        result=checked([*original,cost<bound]);close(result,[*original,cost<bound])
        solver=z3.Solver();solver.add(result.formula);assert solver.check()==expected


def test_unknown_domain_proof_does_not_authorize_parameterization(monkeypatch):
    import tools.semantic_checks.finite_set_boolean_projection as module
    monkeypatch.setattr(module,'prove_finite_set_representations',lambda assertions, record: [])
    s=z3.Const('s',z3.SetSort(z3.IntSort()));body=domain(s,[1]);result=checked([body])
    assert not result.eliminated_variables and result.formula.eq(z3.And(body))


def test_quantified_input_is_refused():
    s=z3.Const('s',z3.SetSort(z3.IntSort()));x=z3.Int('x')
    with pytest.raises(ValueError,match='quantifier-free'):
        checked([domain(s,[1]),z3.ForAll([x],z3.IsMember(x,s))])


def test_unlowered_carrier_syntax_is_not_guessed():
    s=z3.Const('s',z3.SetSort(z3.IntSort()))
    body=s==z3.SetIntersect(s,finite([1,2]))
    result=checked([body])
    assert not result.eliminated_variables and result.formula.eq(z3.And(body))


def test_fresh_membership_name_collision_is_avoided(monkeypatch):
    original = z3.FreshConst
    collision = z3.Bool('existing_member')
    calls = []
    def supplied(sort, prefix='c'):
        calls.append(True)
        return collision if len(calls) == 1 else original(sort, prefix)
    monkeypatch.setattr(z3, 'FreshConst', supplied)
    value = z3.Const('s', z3.SetSort(z3.IntSort()))
    assertions = [domain(value, [1]), z3.Not(collision), z3.IsMember(1, value)]
    result = checked(assertions)
    assert len(calls) == 2
    assert all(not b.eq(collision) for b in result.boolean_witnesses)
    close(result, assertions)
    solver = z3.Solver(); solver.add(result.formula)
    assert solver.check() == z3.sat


@pytest.mark.parametrize('carrier_indices', [[0, 1], [-2, 3]])
def test_proved_dynamic_index_covers_exact_finite_cells(carrier_indices):
    a = z3.Array('a', z3.IntSort(), z3.SetSort(z3.IntSort()))
    i, cost = z3.Ints('i cost')
    left, right = carrier_indices
    assertions = [domain(a[left], [-2, 5]), domain(a[right], [7]),
                  z3.Or(i == left, i == right),
                  cost == z3.If(z3.IsMember(7, a[i]), 1, 0)]
    result = checked(assertions)
    assert len(result.eliminated_variables) == 1
    assert len(result.boolean_witnesses) == 3
    assert result.index_domains and result.index_domains[0][1] == tuple(carrier_indices)
    # Coverage is already independently proved. Check rewriting under all exact
    # index choices, and every admissible pair of sets including empty sets.
    for index, bits in itertools.product(carrier_indices, itertools.product([False, True], repeat=3)):
        sv = finite([v for v, bit in zip([-2, 5], bits[:2]) if bit])
        tv = finite([7] if bits[2] else [])
        source = z3.Solver(); source.add(*assertions, i == index, a[left] == sv, a[right] == tv)
        substitutions = {str(k): v for k, v in result.substitutions}
        target = z3.Solver(); target.add(result.formula, i == index,
            substitutions[str(a[left])] == sv, substitutions[str(a[right])] == tv)
        assert source.check() == target.check() == z3.sat
        expected = int(index == right and bits[2])
        assert source.model().eval(cost).as_long() == target.model().eval(cost).as_long() == expected


def test_affine_dynamic_index_is_proved_from_hard_integer_bounds():
    a = z3.Array('a', z3.IntSort(), z3.SetSort(z3.IntSort()))
    y = z3.Array('y', z3.IntSort(), z3.IntSort())
    i = z3.Select(y, 0)
    assertions = [domain(a[7], [1]), domain(a[8], [2]), i >= 1, i <= 2,
                  z3.IsMember(1, a[6+i])]
    result = checked(assertions)
    assert len(result.eliminated_variables) == 1
    assert len(result.index_domains) == 1
    solver = z3.Solver(); solver.add(result.formula, i == 2)
    assert solver.check() == z3.unsat
    solver = z3.Solver(); solver.add(result.formula, i == 1)
    assert solver.check() == z3.sat


@pytest.mark.parametrize('missing', ['hole', 'outside', 'conditional'])
def test_dynamic_index_without_complete_carrier_coverage_declines(missing):
    a = z3.Array('a', z3.IntSort(), z3.SetSort(z3.IntSort()))
    i = z3.Int('i'); flag = z3.Bool('flag')
    assertions = [domain(a[0], [1]), domain(a[2], [2]), z3.IsMember(99, a[i])]
    additions = {'hole': [i >= 0, i <= 2], 'outside': [i >= 0, i <= 3],
                 'conditional': [z3.Implies(flag, z3.Or(i == 0, i == 2))]}
    # SAT is a deliberate negative control, so a failed coverage query must be
    # recorded but does not authorize either rejecting or rewriting the model.
    proofs = []
    result = project_finite_sets_to_booleans(assertions + additions[missing], lambda *row: proofs.append(row))
    assert any(row[2] == 'sat' for row in proofs)
    assert not result.eliminated_variables and not result.index_domains
    solver = z3.Solver(); solver.add(result.formula)
    assert solver.check() == z3.sat


def test_unknown_index_coverage_keeps_the_original_array(monkeypatch):
    import tools.semantic_checks.finite_set_boolean_projection as module
    original = z3.Solver
    class UnknownCoverage:
        def __init__(self, *args, **kwargs): self.inner = original(*args, **kwargs)
        def add(self, *args): self.inner.add(*args)
        def sexpr(self): return self.inner.sexpr()
        def check(self): return z3.unknown
    # Keep independent carrier proofs real, change only the coverage checker.
    real_prover = module.prove_finite_set_representations
    def carrier_prover(assertions, record):
        with monkeypatch.context() as context:
            context.setattr(z3, 'Solver', original)
            return real_prover(assertions, record)
    monkeypatch.setattr(module, 'prove_finite_set_representations', carrier_prover)
    monkeypatch.setattr(z3, 'Solver', UnknownCoverage)
    a = z3.Array('a', z3.IntSort(), z3.SetSort(z3.IntSort())); i = z3.Int('i')
    assertions = [domain(a[0], [1]), i == 0, z3.IsMember(1, a[i])]
    rows = []
    result = project_finite_sets_to_booleans(assertions, lambda *row: rows.append(row))
    assert any(row[2] == 'unknown' for row in rows)
    assert not result.eliminated_variables and result.formula.eq(z3.And(*assertions))


@pytest.mark.parametrize('operation', ['indicator_product', 'sum', 'subtraction', 'negative'])
def test_finite_symbolic_store_index_preserves_all_boolean_assignments(operation):
    s = z3.Const('s', z3.SetSort(z3.IntSort())); a, b, value, flag = z3.Bools('a b value flag')
    indices = {'indicator_product': z3.If(a, 1, 0) * z3.If(b, 1, 0) * 7,
               'sum': z3.If(a, -2, 0) + z3.If(b, 3, 0),
               'subtraction': z3.If(a, 5, 0) - z3.If(b, 2, 0),
               'negative': -z3.If(a, 3, -2)}
    index = indices[operation]
    output = z3.Store(z3.Store(s, index, value), 0, z3.Not(value))
    assertions = [domain(s, [-2, 0, 3, 7]), flag == (output == finite([0, 7]))]
    result = checked(assertions)
    close(result, assertions)
    todo = [result.formula]; seen = set()
    while todo:
        term = todo.pop()
        if term.get_id() in seen: continue
        seen.add(term.get_id()); assert term.sort().kind() != z3.Z3_ARRAY_SORT
        todo.extend(term.children())
    representation = result.substitutions[0][1]
    for bits in itertools.product([False, True], repeat=8):
        av, bv, vv, fv = bits[:4]
        members = {x for x, bit in zip([-2, 0, 3, 7], bits[4:]) if bit}
        iv = {'indicator_product': int(av)*int(bv)*7,
              'sum': (-2 if av else 0)+(3 if bv else 0),
              'subtraction': (5 if av else 0)-(2 if bv else 0),
              'negative': -(3 if av else -2)}[operation]
        actual = set(members)
        if vv: actual.add(iv)
        else: actual.discard(iv)
        if not vv: actual.add(0)
        else: actual.discard(0)
        expected = z3.sat if fv == (actual == {0, 7}) else z3.unsat
        bindings = [a == av, b == bv, value == vv, flag == fv]
        source = z3.Solver(); source.add(*assertions, *bindings, s == finite(sorted(members)))
        target = z3.Solver(); target.add(result.formula, *bindings, representation == finite(sorted(members)))
        assert source.check() == target.check() == expected


def test_symbolic_store_preserves_default_true_and_last_write():
    s = z3.Const('s', z3.SetSort(z3.IntSort())); b = z3.Bool('b')
    index = z3.If(b, -2, 3)
    output = z3.Store(z3.Store(z3.SetComplement(s), index, False), index, True)
    assertions = [domain(s, [-2, 3]), output == finite([])]
    result = checked(assertions); close(result, assertions)
    solver = z3.Solver(); solver.add(result.formula)
    assert solver.check() == z3.unsat


def test_unbounded_store_index_remains_exact_and_opaque():
    s = z3.Const('s', z3.SetSort(z3.IntSort())); i = z3.Int('i')
    assertions = [domain(s, [1]), z3.Store(s, i, True) == finite([99])]
    result = checked(assertions); close(result, assertions)
    solver = z3.Solver(); solver.add(result.formula)
    assert solver.check() == z3.sat
    assert solver.model().eval(i).as_long() == 99
