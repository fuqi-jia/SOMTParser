"""Array iteration binds source expressions, not their positions or fresh choices."""
import pytest
import somtparser as sp
import z3


def check(source, expected):
    result = sp.translate(source=source+' solve satisfy;', language='minizinc')
    assert result.ok, [d.message for d in result.diagnostic_items]
    actual = z3.And(*z3.parse_smt2_string(result.to_smt2(sp.OmtDialect.Z3)))
    solver = z3.Solver()
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


def test_decision_array_elements_are_bound_by_value():
    a=z3.Array('a',z3.IntSort(),z3.IntSort())
    x=z3.Int('x')
    check('array[-1..0] of var int: a; var int: x; '
          'constraint x = sum(v in a)(v*v);', x==a[-1]*a[-1]+a[0]*a[0])


def test_array_iteration_keeps_duplicates_order_and_nested_shadowing():
    x=z3.Int('x')
    check('int: v = 19; array[1..3] of int: a = [2,2,3]; '
          'array[int] of int: b = [v*10 | v in a]; var int: x; '
          'constraint x = b[1]+b[2]+b[3]+sum(v in a)(sum(v in 1..2)(v)+v)+v;', x==105)


def test_inferred_alias_is_expression_sharing_not_free_variables():
    a=z3.Array('a',z3.IntSort(),z3.IntSort())
    check('array[1..2] of var int: a; any: b = a ++ [a[1]+1]; '
          'constraint alldifferent(b);', z3.Distinct(a[1],a[2],a[1]+1))


def test_any_alias_is_visible_as_a_generator_source():
    x=z3.Int('x')
    check('any: a = [2,2,5]; var int: x; constraint x = sum(v in a)(v);',x==9)


@pytest.mark.parametrize('fold,expected', [('sum',9),('product',18)])
def test_array_comprehension_where_uses_decision_guard(fold,expected):
    b=z3.Bool('b'); x=z3.Int('x')
    unit=0 if fold=='sum' else 1
    check(f'var bool: b; var int: x; constraint x = {fold}([i*3 | i in 1..2 where b]);',
          x==z3.If(b,expected,unit))


def test_guarded_comprehension_preserves_partiality_and_unselected_terms():
    b=z3.Bool('b'); x=z3.Int('x')
    check('var bool: b; var int: x; constraint not (sum([1 div x | i in 1..1 where b])=0);',
          z3.And(b,z3.Or(x==0,x==1,x==-1)))


def test_empty_bool_array_has_vacuous_quantifier():
    check('array[1..0] of bool: a = []; constraint forall(b in a)(b);',z3.BoolVal(True))


def test_comprehension_alias_rebinds_per_row_and_restores_outer_name():
    check('int: p = 99; var int: x; '
          'constraint x = sum([j | i in 1..3, p = 2*i where p >= 4, j in 1..p]) + p;',
          z3.Int('x') == 130)


def test_comprehension_alias_keeps_decision_expression_and_empty_bool_type():
    check('var int: v; var int: x; '
          'array[1..0] of bool: a = []; '
          'constraint x = sum([p | i in 1..3, p = v+i]); '
          'constraint sum([if p then 1 else 0 endif | b in a, p = b]) = 0;',
          z3.Int('x') == 3*z3.Int('v') + 6)


def test_indexed_comprehension_alias_retains_computed_index_domain():
    check('any: a = [p: i | i in 1..3, p = i+2]; var int: x; '
          'constraint x = a[3] + a[4] + a[5];', z3.Int('x') == 6)
