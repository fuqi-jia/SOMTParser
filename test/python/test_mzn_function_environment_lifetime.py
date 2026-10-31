"""Recursive and forward calls retain immutable lexical environment snapshots."""
import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


def _formula(source):
    result = sp.translate(source=source, language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]
    return z3.And(*z3.parse_smt2_string(result.to_smt2(sp.OmtDialect.Z3)))


@pytest.mark.parametrize("call_position", ["before", "between", "after"])
@pytest.mark.parametrize("depth", [3, 9])
def test_nested_let_and_mutual_recursion_keep_global_snapshot(call_position, depth):
    prefix = "int: base=3; var int: result;\n"
    first = """
      function int: f(int: n) = let {int: base=101;} in g(n)+1;
    """
    second = """
      function int: g(int: n) =
        if n=0 then base
        else let {int: ignored=17;} in f(n-1)+base endif;
    """
    call = f"constraint let {{int: base=999;}} in result=f({depth});\n"
    body = {"before": call+first+second, "between": first+call+second,
            "after": first+second+call}[call_position]
    formula = _formula(prefix + body + "solve satisfy;")
    solver = z3.Solver()
    solver.add(z3.Xor(formula, z3.Int("result") == 4 * (depth + 1)))
    assert solver.check() == z3.unsat


def test_array_formals_do_not_mutate_a_later_call_snapshot():
    formula = _formula("""
      enum E={a,b,c};
      array[E] of int: values=[7,11,13];
      function int: global_value(E: index) = values[index];
      function int: caller(array[int] of int: values) =
        let {int: index=1;} in values[index]+global_value(b);
      var int: result;
      constraint result=caller([1,2])+caller([20,30])+global_value(a);
      solve satisfy;
    """)
    solver = z3.Solver()
    solver.add(z3.Xor(formula, z3.Int("result") == 50))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("forward", [False, True])
def test_fixed_return_cannot_hide_decision_read_in_snapshot(forward):
    declaration = "function int: f(int:n)=if n=0 then x else f(n-1) endif;"
    call = "constraint let {int:x=3;} in f(4)=3;"
    source = "var int:x;" + (call+declaration if forward else declaration+call) + "solve satisfy;"
    result = sp.translate(source=source, language="minizinc")
    assert not result.ok
    assert any("depends on a decision variable" in d.message for d in result.diagnostic_items)
