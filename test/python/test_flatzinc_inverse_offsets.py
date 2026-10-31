"""Full finite inverse relation, including offsets and reification."""
from itertools import permutations

import pytest
import somtparser as sp
import z3


def translate(source):
    translated = sp.translate(source=source + "\nsolve satisfy;", language="flatzinc")
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    solver = z3.Solver()
    solver.from_string(translated.to_smt2())
    return z3.And(*solver.assertions())


@pytest.mark.parametrize("name", ["inverse_offsets", "gecode_inverse_offsets"])
@pytest.mark.parametrize("origins", [(1, 1), (-2, 5), (7, -4)])
@pytest.mark.parametrize("mode", ["", "_reif", "_imp"])
def test_complete_inverse_relation_with_value_offsets(name, origins, mode):
    left_start, right_start = origins
    n = 3
    names = [f"x{i}" for i in range(n)] + [f"y{i}" for i in range(n)]
    x, y = [z3.Int(s) for s in names[:n]], [z3.Int(s) for s in names[n:]]
    source = "\n".join(f"var int: {s};" for s in names)
    source += "\nvar bool: b;" if mode else ""
    source += (f"\nconstraint {name}{mode}([{','.join(names[:n])}],"
               f"{right_start},[{','.join(names[n:])}],{left_start}"
               + (",b" if mode else "") + ");")
    actual = translate(source)
    alternatives = []
    for p in permutations(range(n)):
        alternatives.append(z3.And(
            *[x[i] == right_start + p[i] for i in range(n)],
            *[y[p[i]] == left_start + i for i in range(n)]))
    expected = z3.Or(*alternatives)
    if mode == "_reif":
        expected = z3.Bool("b") == expected
    elif mode == "_imp":
        expected = z3.Implies(z3.Bool("b"), expected)
    solver = z3.Solver()
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("left,right,expected", [
    ("[]", "[]", True), ("[]", "[1]", False),
    ("[1]", "[]", False), ("[1,1]", "[1,2]", False),
    ("[2,1]", "[2,1]", True), ("[0,2]", "[1,2]", False),
])
def test_empty_unequal_duplicate_and_out_of_range_vectors(left, right, expected):
    actual = translate(f"constraint inverse_offsets({left},1,{right},1);")
    solver = z3.Solver()
    solver.add(actual != expected)
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("source", [
    "constraint inverse_offsets([1],1,[1]);",
    "var int: o; constraint inverse_offsets([1],o,[1],1);",
    "constraint inverse_offsets([true],1,[1],1);",
    "constraint inverse_offsets([1],1,[true],1);",
    "constraint inverse_offsets([1],true,[1],1);",
])
def test_invalid_argument_shapes_are_diagnosed(source):
    translated = sp.translate(source=source + "\nsolve satisfy;", language="flatzinc")
    assert not translated.ok


def test_named_arrays_and_parameter_offsets():
    actual = translate("""
      int: foff=5; int: invfoff=-2;
      array [1..2] of int: f=[6,5];
      array [1..2] of int: invf=[-1,-2];
      constraint inverse_offsets(f,foff,invf,invfoff);
    """)
    solver = z3.Solver()
    solver.add(z3.Not(actual))
    assert solver.check() == z3.unsat
