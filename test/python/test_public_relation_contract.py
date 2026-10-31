"""Projection tests distinguish original coordinates from reported auxiliaries."""
import json
from types import SimpleNamespace

import pytest
import z3
import somtparser as sp
from somtparser.hir import HirBuilder
from _public_relation import private_witness_names, public_relation


def lit(n):
    return {'literal': n, 'sort': 'Int'}


def op(name, *args):
    return {'op': name, 'args': list(args)}


def make_result(name='x'):
    if name.startswith('!'):
        # SMT-LIB permits this source name; the HIR JSON identifier grammar does not.
        result = sp.translate(language='smtlib2', source=f"""
            (declare-const |{name}| Int)
            (assert (exists ((w Int)) (and (= |{name}| w) (or (= w 0) (= w 2)))))
        """)
        assert result.ok, [d.message for d in result.diagnostic_items]
        return result
    builder = HirBuilder()
    builder.declare(name, 'Int')
    builder.constrain({'quantifier': 'exists', 'binders': [{'name': 'w', 'sort': 'Int'}],
        'body': op('and', op('eq', {'var': name}, {'var': 'w'}),
            op('or', op('eq', {'var': 'w'}, lit(0)), op('eq', {'var': 'w'}, lit(2))))})
    result = builder.translate()
    assert result.ok, [d.message for d in result.diagnostic_items]
    return result


@pytest.mark.parametrize('custom_context', [False, True])
@pytest.mark.parametrize('name', ['x', '!somt_exists_0'])
def test_all_source_assignments_remain_observable(name, custom_context):
    result = make_result(name)
    assert name not in private_witness_names(result)
    ctx = z3.Context() if custom_context else None
    x = z3.Int(name, ctx=ctx)
    relation = public_relation(result, ctx=ctx)
    solver = z3.Solver(ctx=ctx)
    solver.add(z3.Xor(relation, z3.Or(x == 0, x == 2)))
    assert solver.check() == z3.unsat
    solver = z3.Solver(ctx=ctx)
    solver.add(z3.Xor(relation, x == 0))
    assert solver.check() == z3.sat  # Dropping a permitted source value is detected.


def test_generated_spelling_alone_does_not_authorize_hiding_source_symbol():
    report = SimpleNamespace(to_json=lambda: json.dumps({'choices': []}))
    result = SimpleNamespace(report=report)
    relation = public_relation(result,
        '(declare-const !somt_exists_0 Int) (assert (= !somt_exists_0 2))')
    solver = z3.Solver()
    solver.add(z3.Xor(relation, z3.BoolVal(True)))
    assert solver.check() == z3.sat


def test_missing_auxiliary_name_in_report_is_rejected():
    report = SimpleNamespace(to_json=lambda: json.dumps({'choices': [dict(
        unified_op='positive-exists', strategy='fresh-private-constant', rationale='missing')]}))
    with pytest.raises(AssertionError):
        private_witness_names(SimpleNamespace(report=report))


def test_corrupted_export_is_not_repaired_by_closing_its_witness():
    result = make_result()
    script = result.to_smt2()
    # Add an invalid original-coordinate restriction to an otherwise valid export.
    script = script[:script.index('(check-sat)')] + '(assert (= x 0))\n'
    relation = public_relation(result, script)
    x = z3.Int('x')
    solver = z3.Solver()
    solver.add(z3.Xor(relation, z3.Or(x == 0, x == 2)))
    assert solver.check() == z3.sat
