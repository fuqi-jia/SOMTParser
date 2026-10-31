"""Printed function DAGs retain sharing without capturing lexical names."""
import pytest
import z3

from somtparser import _somtparser as native


INT = native.HirSort.integer()
BOOL = native.HirSort.boolean()


def literal(value):
    return native._hir_literal(INT, str(value))


def op(name, *arguments):
    return native._hir_op(name, list(arguments))


def script_for(model):
    translated = model.translate()
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    script = translated.to_smt2()
    # Re-emission must not mutate the DAG or its canonical ordering hashes.
    assert translated.to_smt2() == script
    return script


@pytest.mark.parametrize('global_name', ['__somt_dag_0', '|__somt_dag_0|'])
def test_nested_let_dependencies_do_not_capture_free_quoted_or_bare_names(global_name):
    model = native.HirModel()
    global_value = model.declare(global_name, INT)
    argument = model.declare('x', INT)
    formal = native._hir_ident('n', INT, True)
    first = op('add', op('mul', formal, formal), global_value)
    second = op('add', op('mul', first, first), literal(2))
    conditions = [op('ge', first, literal(i)) for i in range(32)]
    conditions += [op('ge', second, literal(i)) for i in range(32, 64)]
    conditions += [op('le', second, literal(10000))]
    model.declare_function('in_band', [INT], BOOL)
    model.define_function('in_band', [('n', INT)], op('and', *conditions))
    model.constrain(native._hir_apply('in_band', BOOL, [argument]))
    script = script_for(model)
    assert script.count('(let (') >= 2
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(*z3.parse_smt2_string(script))
    for g in [-5, 0, 7]:
        for x in [0, 3, 5, 8, 12]:
            p = x * x + g
            q = p * p + 2
            expected = p >= 31 and q >= 63 and q <= 10000
            solver.push()
            solver.add(z3.Int('__somt_dag_0') == g, z3.Int('x') == x)
            assert solver.check() == (z3.sat if expected else z3.unsat), (g, x)
            solver.pop()


def test_shared_diamond_body_stays_compact_and_matches_its_recurrence():
    model = native.HirModel()
    x = model.declare('x', INT)
    formal = native._hir_ident('n', INT, True)
    value = op('eq', formal, literal(3))
    for step in range(16):
        value = op('ite', op('ge', formal, literal(step)), value, op('not', value))
    model.declare_function('diamond', [INT], BOOL)
    model.define_function('diamond', [('n', INT)], value)
    model.constrain(native._hir_apply('diamond', BOOL, [x]))
    script = script_for(model)
    assert '(let (' in script
    assert len(script) < 10000
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(*z3.parse_smt2_string(script))
    for number in [-1, 0, 1, 3, 7, 18]:
        expected = number == 3
        for step in range(16):
            expected = expected if number >= step else not expected
        solver.push()
        solver.add(z3.Int('x') == number)
        assert solver.check() == (z3.sat if expected else z3.unsat), number
        solver.pop()


def test_nested_quantifier_body_keeps_its_original_scope():
    model = native.HirModel()
    x = model.declare('x', INT)
    formal = native._hir_ident('n', INT, True)
    local = native._hir_ident('q', INT, True)
    body = native._hir_quantifier(False, [('q', INT)], op('eq', local, formal))
    model.declare_function('has_equal', [INT], BOOL)
    model.define_function('has_equal', [('n', INT)], body)
    model.constrain(native._hir_apply('has_equal', BOOL, [x]))
    script = script_for(model)
    assert '(exists ' in script
    assert '(let (' not in script
    solver = z3.Solver()
    solver.add(z3.Not(z3.And(*z3.parse_smt2_string(script))))
    assert solver.check() == z3.unsat
