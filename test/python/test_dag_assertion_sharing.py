"""The SMT module writer preserves shared maxima and their full relation."""
import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


@pytest.mark.parametrize("count", [5, 40])
@pytest.mark.parametrize("array", [False, True])
def test_shared_maximum_matches_independent_relation(count, array):
    parser = sp.parse("(set-logic ALL)")
    names = ["__somt_dag_0"] + [f"x{i}" for i in range(1, count)]
    if array:
        values = parser.var_array("__somt_dag_0", parser.int_sort(), parser.int_sort())
        variables = [parser.select(values, parser.const_int(i)) for i in range(count)]
    else:
        variables = [parser.var_int(name) for name in names]
    maximum = variables[0]
    for item in variables[1:]:
        maximum = parser.ite(parser.ge(maximum, item), maximum, item)
    result = parser.var_int("result")
    parser.assert_(parser.eq(maximum, result))
    output = parser.dump_smt2()
    assert len(output) < 20000
    assert "(let (" in output

    context = z3.Context()
    actual = z3.And(*z3.parse_smt2_string(output, ctx=context))
    if array:
        values = z3.Array("__somt_dag_0", z3.IntSort(ctx=context), z3.IntSort(ctx=context))
        xs = [z3.Select(values, i) for i in range(count)]
    else:
        xs = [z3.Int(name, ctx=context) for name in names]
    value = z3.Int("result", ctx=context)
    reference = z3.And(*[value >= x for x in xs],
                       z3.Or(*[value == x for x in xs]))
    solver = z3.Solver(ctx=context)
    solver.set(timeout=0)
    solver.add(z3.Xor(actual, reference))
    assert solver.check() == z3.unsat, solver.reason_unknown()


def test_minizinc_shared_maximum_objective_is_compact_and_correct():
    translated = sp.translate(
        source="array[1..32] of var 0..7:x;constraint x[32]=7;solve minimize max(x);",
        language="minizinc", dialect=sp.OmtDialect.Z3)
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    output = translated.to_smt2(sp.OmtDialect.Z3)
    assert len(output) < 30000
    context = z3.Context()
    solver = z3.Optimize(ctx=context)
    solver.set(timeout=0)
    solver.from_string(output)
    assert solver.check() == z3.sat, solver.reason_unknown()
    assert len(solver.objectives()) == 1
    assert solver.model().eval(solver.objectives()[0]).as_long() == 7
