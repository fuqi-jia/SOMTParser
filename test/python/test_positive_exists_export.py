"""Public HIR export: private existential witnesses preserve projection and cost."""
import pytest
import z3
import somtparser as sp
from z3.z3util import get_vars
from somtparser.hir import HirBuilder


def lit(value, sort="Int"):
    return {"literal": value, "sort": sort}


def var(name):
    return {"var": name}


def op(name, *args):
    return {"op": name, "args": list(args)}


def quant(kind, name, body):
    return {"quantifier": kind, "binders": [{"name": name, "sort": "Int"}], "body": body}


def exported(builder):
    result = builder.translate()
    assert result.ok, [d.message for d in result.diagnostic_items]
    return result, result.to_smt2(sp.OmtDialect.Z3)


def projection(text):
    actual = z3.And(*z3.parse_smt2_string(text))
    witnesses = [value for value in get_vars(actual) if str(value.decl().name()).startswith("!somt_exists_")]
    return z3.Exists(witnesses, actual) if witnesses else actual, witnesses


@pytest.mark.parametrize("maximize, optimum", [(False, 0), (True, 4)])
def test_public_optimization_preserves_projected_assignments_and_exact_optimum(maximize, optimum):
    builder = HirBuilder(); builder.declare("x", "Int", lower=0, upper=5)
    relation = quant("exists", "rank", op("and", op("ge", var("rank"), lit(0)),
        op("le", var("rank"), lit(2)), op("eq", var("x"), op("mul", lit(2), var("rank")))))
    builder.constrain(relation)
    builder.model.objective(maximize, builder.expr(var("x")))
    result, text = exported(builder)
    assert "(exists " not in text
    assert "fresh-private-constant" in result.report.to_json()
    optimizer = z3.Optimize(); optimizer.from_string(text)
    assert len(optimizer.objectives()) == 1
    assert optimizer.check() == z3.sat
    assert optimizer.model().eval(z3.Int("x")).as_long() == optimum
    # Check all source coordinates, not a single favorable witness.
    plain = "\n".join(line for line in text.splitlines()
                       if not line.lstrip().startswith(("(minimize", "(maximize")))
    actual, witnesses = projection(plain); assert len(witnesses) == 1
    feasible = z3.Solver(); feasible.add(*z3.parse_smt2_string(plain), z3.Int("x") == optimum)
    assert feasible.check() == z3.sat
    better = z3.Solver(); better.add(*z3.parse_smt2_string(plain), z3.Int("x") > optimum if maximize else z3.Int("x") < optimum)
    assert better.check() == z3.unsat
    x = z3.Int("x"); expected = z3.Or(x == 0, x == 2, x == 4)
    solver = z3.Solver(); solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("context", ["not", "reified", "disjunction", "universal"])
def test_scoped_quantifiers_are_not_lifted(context):
    builder = HirBuilder(); builder.declare("x", "Int", lower=0, upper=2)
    builder.declare("flag", "Bool")
    exists = quant("exists", "rank", op("eq", var("rank"), var("x")))
    if context == "not":
        body, expected = op("not", exists), z3.BoolVal(False)
    elif context == "reified":
        body, expected = op("eq", var("flag"), exists), z3.Bool("flag")
    elif context == "disjunction":
        body, expected = op("or", var("flag"), exists), z3.BoolVal(True)
    else:
        body = quant("forall", "outer", quant("exists", "rank",
            op("eq", var("rank"), op("add", var("outer"), var("x")))))
        expected = z3.BoolVal(True)
    builder.constrain(body)
    result, text = exported(builder)
    assert "fresh-private-constant" not in result.report.to_json()
    actual, witnesses = projection(text); assert not witnesses
    solver = z3.Solver(); x = z3.Int("x")
    solver.add(x >= 0, x <= 2, z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


def test_independent_positive_conjuncts_get_distinct_witnesses():
    builder = HirBuilder(); builder.declare("x", "Int", lower=0, upper=2)
    builder.constrain(op("and",
        quant("exists", "rank", op("eq", var("rank"), var("x"))),
        quant("exists", "rank", op("eq", var("rank"), op("add", var("x"), lit(1))))))
    _, text = exported(builder); actual, witnesses = projection(text)
    assert len(witnesses) == 2
    x = z3.Int("x"); solver = z3.Solver()
    solver.add(z3.Xor(actual, z3.And(x >= 0, x <= 2)))
    assert solver.check() == z3.unsat


def test_nested_witness_dependency_preserves_outer_value():
    builder = HirBuilder(); builder.declare("x", "Int", lower=0, upper=2)
    builder.constrain(quant("exists", "a", op("and",
        op("eq", var("a"), op("add", var("x"), lit(1))),
        quant("exists", "b", op("and",
            op("eq", var("b"), op("add", var("a"), lit(2))),
            op("eq", var("b"), lit(4)))))))
    _, text = exported(builder); actual, witnesses = projection(text)
    assert len(witnesses) == 2
    solver = z3.Solver(); solver.add(z3.Xor(actual, z3.Int("x") == 1))
    assert solver.check() == z3.unsat
