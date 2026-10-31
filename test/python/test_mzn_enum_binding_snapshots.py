"""Function and let snapshots retain enum bindings across real mutations."""
import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


def _check(source, expected):
    result = sp.translate(source=source, language="minizinc")
    assert result.ok, [diagnostic.message for diagnostic in result.diagnostic_items]
    solver = z3.Solver()
    solver.add(*z3.parse_smt2_string(result.to_smt2(sp.OmtDialect.Z3)))
    assert solver.check() == expected


@pytest.mark.parametrize("forward", [False, True])
@pytest.mark.parametrize("op, expected", [("=", z3.sat), ("!=", z3.unsat)])
def test_enum_binding_shadow_is_local_to_each_function_call(forward, op, expected):
    function = "function int: f(E: x) = let {int: a = 12;} in a + enum2int(x);"
    constraint = f"constraint f(a) + f(b) {op} 27;"
    ordered = constraint + function if forward else function + constraint
    _check(f"""
        enum E = {{a, b}};
        {ordered}
        constraint enum2int(a) = 1 /\\ enum2int(b) = 2;
        solve satisfy;
    """, expected)


@pytest.mark.parametrize("op, expected", [("=", z3.sat), ("!=", z3.unsat)])
def test_nested_let_restores_shadowed_constructor_before_later_calls(op, expected):
    _check(f"""
        enum E = {{a,b}};
        function int: inner(E:x) = enum2int(x);
        function int: outer(E:x) =
          let {{int:a = 20;}} in
            (let {{int:a = 30;}} in a) + a + inner(x);
        constraint outer(b) + inner(a) {op} 53;
        solve satisfy;
    """, expected)


@pytest.mark.parametrize("op, expected", [("=", z3.sat), ("!=", z3.unsat)])
def test_later_enum_insertions_do_not_replace_earlier_function_snapshot(op, expected):
    _check(f"""
        enum E = {{a,b}};
        function int: first(E:x) = enum2int(x) + enum2int(b);
        enum F = {{c,d}};
        function int: second(F:x) = enum2int(x) + first(a);
        constraint first(b) + second(d) {op} 9;
        solve satisfy;
    """, expected)


def test_dense_constructor_snapshots_with_function_calls_and_let_names():
    names = ",".join(f"tag{i}" for i in range(256))
    _check(f"""
        enum E = {{{names}}};
        function int: ordinal(E:x) = let {{int:unrelated=3;}} in enum2int(x)+unrelated;
        constraint sum(x in E)(ordinal(x)) = {256 * 257 // 2 + 256 * 3};
        constraint ordinal(tag0) = 4 /\\ ordinal(tag255) = 259;
        solve satisfy;
    """, z3.sat)
