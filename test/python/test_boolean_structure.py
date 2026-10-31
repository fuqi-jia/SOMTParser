"""Soundness controls for proof by Boolean DAG correspondence."""
import importlib.util
from pathlib import Path

import pytest
import z3

spec = importlib.util.spec_from_file_location(
    'boolean_structure', Path(__file__).resolve().parents[2] /
    'tools/semantic_checks/boolean_structure.py')
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)


@pytest.mark.parametrize('left,right,expected', [
    ('(and x (and y x) true)', '(and y x)', True),
    ('(or x (or y x) false)', '(or y x)', True),
    ('(not (not x))', 'x', True),
    ('(and x false)', 'false', True),
    ('(or x true)', 'true', True),
    ('(and)', 'true', True),
    ('(or)', 'false', True),
    ('(forall ((a Bool)) (or a x))', '(forall ((b Bool)) (or x b))', True),
    ('(exists ((a Bool)) (forall ((a Bool)) a))',
     '(exists ((b Bool)) (forall ((c Bool)) c))', True),
    ('(forall ((a Bool) (b Bool)) (or a b))',
     '(forall ((c Bool) (d Bool)) (or d c))', True),
    ('x', 'y', False),
    ('(and x y)', '(or x y)', False),
    ('x', '(not x)', False),
    ('(ite x y z)', '(ite x z y)', False),
    ('(exists ((a Bool)) (forall ((b Bool)) b))',
     '(exists ((a Bool)) (forall ((b Bool)) a))', False),
    ('(forall ((a Bool)) a)', '(exists ((a Bool)) a)', False),
    ('(forall ((a Bool)) (exists ((b Bool)) (= a b)))',
     '(exists ((b Bool)) (forall ((a Bool)) (= a b)))', False),
    ('(forall ((a Bool)) (or a x))', '(forall ((a Bool)) (or a y))', False),
])
def test_complete_structure_and_mutants(left, right, expected):
    prelude = '(declare-const x Bool)(declare-const y Bool)(declare-const z Bool)'
    # The SMT-LIB parser rejects parenthesized zero-argument applications;
    # the structural checker also accepts native API-created Boolean nodes.
    if left in ('(and)', '(or)'):
        empty = z3.And() if left == '(and)' else z3.Or()
        assert empty.num_args() == 0
        expressions = (empty, z3.parse_smt2_string(prelude + f'(assert {right})')[0])
    else:
        expressions = z3.parse_smt2_string(prelude + f'(assert {left})(assert {right})')
    proof = checker.structural_equivalence(*expressions)
    assert proof['equivalent'] == expected
    # An independent solver verifies every accepted identity, not just its
    # representation. Negative structural results are only inconclusive.
    if expected:
        solver = z3.Solver()
        solver.add(z3.Xor(*expressions))
        assert solver.check() == z3.unsat


@pytest.mark.parametrize('constructor,value', [(z3.And, True), (z3.Or, False)])
def test_empty_boolean_dag_identity(constructor, value):
    # These zero-arity DAGs are supported by the Z3 API even when its SMT-LIB
    # parser rejects the non-standard textual applications `(and)` and `(or)`.
    expression = constructor()
    identity = z3.BoolVal(value)
    assert checker.structural_equivalence(expression, identity)['equivalent']
    assert not checker.structural_equivalence(expression, z3.BoolVal(not value))['equivalent']
    solver = z3.Solver()
    solver.add(z3.Xor(expression, identity))
    assert solver.check() == z3.unsat


def test_deep_dag_uses_iterative_traversal():
    left = right = z3.Bool('leaf')
    for i in range(1600):
        v = z3.Bool(f'p{i}')
        left = z3.And(v, left) if i % 2 else z3.Or(v, left)
        right = z3.And(right, v) if i % 2 else z3.Or(right, v)
    assert checker.structural_equivalence(left, right)['equivalent']


@pytest.mark.parametrize('left,right,expected', [
    ('(<= x y)', '(>= y x)', True),
    ('(< x y)', '(> y x)', True),
    ('(<= r s)', '(>= s r)', True),
    ('(< r s)', '(> s r)', True),
    ('(<= (to_real x) r)', '(>= r (to_real x))', True),
    ('(not (< x y))', '(not (> y x))', True),
    ('(forall ((i Int)) (=> (and (< i 25600) (<= 0 i)) (>= (select a i) 0)))',
     '(forall ((j Int)) (=> (and (>= j 0) (< j 25600)) (>= (select a j) 0)))', True),
    ('(forall ((i Real)) (exists ((j Real)) (< i j)))',
     '(forall ((u Real)) (exists ((v Real)) (> v u)))', True),
    ('(<= x y)', '(<= y x)', False),
    ('(< x y)', '(< y x)', False),
    ('(<= x y)', '(> y x)', False),
    ('(>= r s)', '(> r s)', False),
    ('(bvule b c)', '(bvsle b c)', False),
    ('(bvult b c)', '(bvule b c)', False),
    ('(fp.leq f f)', 'true', False),
    ('(fp.leq f g)', '(fp.lt f g)', False),
])
def test_exact_order_reversal_and_mutants(left, right, expected):
    prelude = '''
        (declare-const x Int) (declare-const y Int)
        (declare-const r Real) (declare-const s Real)
        (declare-const a (Array Int Int))
        (declare-const b (_ BitVec 8)) (declare-const c (_ BitVec 8))
        (declare-const f (_ FloatingPoint 8 24))
        (declare-const g (_ FloatingPoint 8 24))
    '''
    expressions = z3.parse_smt2_string(prelude + f'(assert {left})(assert {right})')
    # Check both raw and simplified formulas: simplify retains some dual
    # inequality spellings, as in the complete 25,600-task source relation.
    for pair in (expressions, [z3.simplify(expr) for expr in expressions]):
        assert checker.structural_equivalence(*pair)['equivalent'] == expected
    solver = z3.Solver()
    solver.add(z3.Xor(*expressions))
    assert solver.check() == (z3.unsat if expected else z3.sat)


@pytest.mark.parametrize('sort', [z3.IntSort, z3.RealSort])
def test_arithmetic_sum_order_and_equality_preserve_complete_relation(sort):
    x, y, cost = z3.Consts('sum_x sum_y sum_cost', sort())
    left = z3.And(z3.Sum(x, y, x) <= cost, cost == x + y)
    right = z3.And(x + y == cost, z3.Sum(x, x, y) <= cost)
    assert checker.structural_equivalence(left, right)['equivalent']
    solver = z3.Solver()
    solver.add(z3.Xor(left, right))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('sort', [z3.IntSort, z3.RealSort])
def test_arithmetic_duplicate_is_not_dropped(sort):
    x, y = z3.Consts('duplicate_x duplicate_y', sort())
    left = z3.Sum(x, x, y) == 3
    right = z3.Sum(x, y) == 3
    assert not checker.structural_equivalence(left, right)['equivalent']
    solver = z3.Solver()
    solver.add(z3.Xor(left, right))
    assert solver.check() == z3.sat


def test_quantified_scheduling_sum_and_exact_cost_order():
    starts = z3.Array('schedule_starts', z3.IntSort(), z3.IntSort())
    cost, i, j, t, u = z3.Ints('cost source_i target_i source_t target_t')
    durations, heights = [2, 3, 1], [1, 2, 1]
    left_loads = [z3.If(z3.And(starts[k] <= t, t < starts[k] + durations[k]),
                       heights[k], 0) for k in range(3)]
    right_loads = [z3.If(z3.And(u < durations[k] + starts[k], starts[k] <= u),
                        heights[k], 0) for k in (2, 0, 1)]
    left = z3.And(z3.ForAll(t, z3.Sum(*left_loads) <= 2),
                  z3.Exists(i, z3.And(0 <= i, i < 3, cost == starts[i] + 2)))
    right = z3.And(z3.Exists(j, z3.And(j < 3, 0 <= j, 2 + starts[j] == cost)),
                   z3.ForAll(u, z3.Sum(*right_loads) <= 2))
    assert checker.structural_equivalence(left, right)['equivalent']
    # This identity uses the whole guarded formula, including the cost.
    solver = z3.Solver()
    solver.add(z3.Xor(left, right))
    assert solver.check() == z3.unsat


def test_wide_sum_keeps_every_operand():
    values = [z3.Int(f'wide_sum_{i}') for i in range(4096)]
    left = z3.Sum(*values) >= 0
    right = z3.Sum(*reversed(values)) >= 0
    assert checker.structural_equivalence(left, right)['equivalent']
    assert not checker.structural_equivalence(left, z3.Sum(*values[:-1]) >= 0)['equivalent']


def test_shared_arithmetic_recurrence_is_not_expanded():
    x, y = z3.Ints('shared_sum_x shared_sum_y')
    left, right = x + y, y + x
    for _ in range(128):
        left, right = left + left, right + right
    proof = checker.structural_equivalence(left == 0, right == 0)
    assert proof['equivalent']
    assert proof['visited_nodes'] < 600


def test_subtraction_and_ite_branches_remain_ordered():
    x, y = z3.Ints('ordered_x ordered_y')
    condition = z3.Bool('ordered_condition')
    for left, right in ((x - y == 1, y - x == 1),
                        (z3.If(condition, x, y) == 0, z3.If(condition, y, x) == 0)):
        assert not checker.structural_equivalence(left, right)['equivalent']
        solver = z3.Solver()
        solver.add(z3.Xor(left, right))
        assert solver.check() == z3.sat


def test_arithmetic_commutation_does_not_rewrite_bitvectors_or_floats():
    a, b = z3.BitVecs('bv_sum_a bv_sum_b', 8)
    assert not checker.structural_equivalence(a + b == 0, b + a == 0)['equivalent']
    x, y = z3.FPs('fp_sum_x fp_sum_y', z3.Float32())
    zero = z3.FPVal(0, z3.Float32())
    left = z3.fpAdd(z3.RNE(), x, y) == zero
    right = z3.fpAdd(z3.RNE(), y, x) == zero
    assert not checker.structural_equivalence(left, right)['equivalent']


def test_equality_symmetry_keeps_array_and_symbol_identities():
    a, b, c = [z3.Array(name, z3.IntSort(), z3.IntSort())
               for name in ('eq_array_a', 'eq_array_b', 'eq_array_c')]
    assert checker.structural_equivalence(a == b, b == a)['equivalent']
    assert not checker.structural_equivalence(a == b, a == c)['equivalent']
