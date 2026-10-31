"""Independent extensional relations, including reification and helper reuse."""
import pytest
import somtparser as sp
import z3


def translate(source, profile="default"):
    result = sp.translate(source=source, language="flatzinc", profile=profile,
                          dialect=sp.OmtDialect.Z3)
    assert result.ok, [d.message for d in result.diagnostic_items]
    parsed = z3.Optimize()
    script = result.to_smt2(sp.OmtDialect.Z3)
    parsed.from_string(script)
    return parsed, script


def equivalent(source, expected, profile="default"):
    parsed, script = translate(source + "solve satisfy;", profile)
    solver = z3.Solver()
    solver.add(z3.Xor(z3.And(*parsed.assertions()), expected))
    assert solver.check() == z3.unsat
    return script


@pytest.mark.parametrize("profile", ["default", "ground", "quantified"])
def test_repeated_content_different_arguments_and_aliased_coordinates(profile):
    x, y, z = z3.Ints("x y z")
    b = z3.Bool("b")
    rows = [(0, 1), (2, 2), (-3, 1)]

    def member(a, c):
        return z3.Or(*[z3.And(a == first, c == second) for first, second in rows])

    script = equivalent("""
        int: two = 2;
        var int: x; var int: y; var int: z; var bool: b;
        array [1..6] of int: a = [0,1,two,2,-3,1];
        array [1..6] of int: alias = [0,+1,2,2,-3,1];
        constraint gecode_table_int([x,y],a);
        constraint gecode_table_int_reif([z,y],alias,b);
        constraint gecode_table_int_imp([x,x],a,b);
    """, z3.And(member(x, y), b == member(z, y), z3.Implies(b, member(x, x))), profile)
    assert script.count("(define-fun ") == 1


def test_cache_separates_same_values_at_different_tuple_widths():
    x, y = z3.Ints("x y")
    a, b = z3.Bools("a b")
    script = equivalent("""
        var int: x; var int: y; var bool: a; var bool: b;
        array [1..4] of int: t = [0,1,2,3];
        constraint gecode_table_int_reif([x],t,a);
        constraint gecode_table_int_reif([x,y],t,b);
    """, z3.And(a == z3.Or(x == 0, x == 1, x == 2, x == 3),
                 b == z3.Or(z3.And(x == 0, y == 1), z3.And(x == 2, y == 3))))
    assert script.count("(define-fun ") == 2


def test_big_integer_singleton_and_duplicate_rows_preserve_signed_objective():
    big = 10 ** 70 + 123
    x, y = z3.Ints("x y")
    parsed, _ = translate(f"""
        var int: x; var int: y;
        constraint gecode_table_int([x,y],[{big},-7,{big},-7]);
        solve maximize y;
    """)
    assert len(parsed.objectives()) == 1
    cost = z3.Real("independent_cost")
    actual = z3.And(*parsed.assertions(), cost == parsed.objectives()[0])
    expected = z3.And(x == big, y == -7, cost == 7)
    solver = z3.Solver()
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("table", ["[]", "[1]", "[2,2]"])
def test_empty_and_constant_calls_under_negation(table):
    values = {"[]": [], "[1]": [1], "[2,2]": [2, 2]}[table]
    equivalent("var bool: b; constraint bool_eq(b,false);"
               f"constraint gecode_table_int_reif([2],{table},b);",
               z3.And(z3.Not(z3.Bool("b")), z3.Bool("b") == (2 in values)))


@pytest.mark.parametrize("source", [
    "constraint gecode_table_int([true],[]);",
    "constraint gecode_table_int([1.0],[]);",
    "constraint gecode_table_int([missing],[]);",
    "constraint gecode_table_int([],[]);",
    "constraint gecode_table_int([0,1],[0,1,2]);",
    "constraint gecode_table_int([0],[true]);",
    "constraint gecode_table_int([0],[0.0]);",
    "var int: v; constraint gecode_table_int([0],[v]);",
    "array [1..0] of bool: t = []; constraint gecode_table_int([0],t);",
    "array [1..1] of var int: t = [0]; constraint gecode_table_int([0],t);",
])
def test_malformed_or_nonparameter_operands_are_rejected(source):
    result = sp.translate(source=source + "solve satisfy;", language="flatzinc")
    assert not result.ok


def test_helper_name_cannot_collide_with_later_source_declaration():
    name = "__somt_fzn_table_0"
    equivalent("var int: x; constraint gecode_table_int([x],[1,2]);"
               f"var int: {name}; constraint int_eq({name},9);",
               z3.And(z3.Or(z3.Int("x") == 1, z3.Int("x") == 2), z3.Int(name) == 9))
