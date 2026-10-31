"""Exact sparse integer domains encountered in the official Challenge export."""
import pytest
import z3
import somtparser as sp


def equivalent(source, expected):
    result = sp.translate(source=source + '\nsolve satisfy;', language='flatzinc')
    assert result.ok, [diagnostic.message for diagnostic in result.diagnostic_items]
    actual = z3.And(*z3.parse_smt2_string(result.to_smt2()))
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(actual != expected)
    assert solver.check() == z3.unsat


@pytest.mark.parametrize('values', [(1, 3), (-5, 0, 7), (4,), (1, 1, 3), (),
    (1000000000000000000000000000001, 1000000000000000000000000000003)])
def test_declared_domain_is_exact_even_with_holes_and_large_values(values):
    x = z3.Int('x')
    spelling = '{' + ','.join(str(value) for value in values) + '}'
    equivalent('var ' + spelling + ': x;', z3.Or(*[x == value for value in values]))


def test_initializer_preserves_both_alias_equality_and_sparse_membership():
    x, y = z3.Ints('x y')
    equivalent('var int: y; var {1,3}: x = y;', z3.And(x == y, z3.Or(x == 1, x == 3)))


def test_array_restricts_existing_elements_and_keeps_literal_cells():
    x, y = z3.Ints('x y')
    equivalent('var int: x; var int: y; array[1..3] of var {1,3}: a = [x,3,y];',
        z3.And(z3.Or(x == 1, x == 3), z3.Or(y == 1, y == 3)))


def test_array_literal_outside_sparse_domain_is_inconsistent():
    equivalent('array[1..1] of var {1,3}: a = [2];', z3.BoolVal(False))


def test_new_array_elements_receive_the_enumerated_domain():
    x, y = z3.Ints('x y')
    equivalent('array[1..2] of var {-2,4}: a = [x,y];',
        z3.And(z3.Or(x == -2, x == 4), z3.Or(y == -2, y == 4)))


def test_repeated_aliases_keep_intersection_of_declaration_domains():
    equivalent('var {1,3}: x; array[1..2] of var {2,3}: a = [x,x];', z3.Int('x') == 3)


@pytest.mark.parametrize('domain', ['{1.5,3}', '{true,3}', '{a,3}', '{1,,3}', '{1,}'])
def test_noninteger_or_malformed_domain_is_rejected(domain):
    result = sp.translate(source='var ' + domain + ': x; solve satisfy;', language='flatzinc')
    assert not result.ok


def test_sparse_integer_array_cannot_retype_a_boolean_alias():
    result = sp.translate(source='var bool: b; array[1..1] of var {1,3}: a = [b]; solve satisfy;',
        language='flatzinc')
    assert not result.ok


def test_actual_challenge_sparse_declarations_keep_all_three_domains():
    a, b, c = z3.Ints('X_INTRODUCED_43_ X_INTRODUCED_44_ X_INTRODUCED_51_')
    # Verbatim declaration fragment from retained Challenge2025 derived 0015.
    equivalent('var {1,3}: X_INTRODUCED_43_;\nvar {1,3}: X_INTRODUCED_44_;\n'
        'var {1,4}: X_INTRODUCED_51_;', z3.And(z3.Or(a == 1, a == 3),
        z3.Or(b == 1, b == 3), z3.Or(c == 1, c == 4)))
