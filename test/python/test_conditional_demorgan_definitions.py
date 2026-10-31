"""Paired conjunction/disjunction guards define witnesses without solver guesses."""
import pytest
import z3
from tools.semantic_checks import existential_definitions as module


def equivalent(left, right):
    solver = z3.Solver()
    solver.add(z3.Xor(left, right))
    assert solver.check() == z3.unsat


def unequal(left, right):
    solver = z3.Solver()
    solver.add(z3.Xor(left, right))
    assert solver.check() == z3.sat


@pytest.mark.parametrize('width', [2, 3, 5])
@pytest.mark.parametrize('reverse', [False, True])
def test_conjunction_and_flattened_complement_define_scalar(width, reverse):
    w, x, y = z3.Ints('w x y')
    atoms = [z3.Bool(f'a{i}') for i in range(width)]
    ordered = list(reversed(atoms)) if reverse else atoms
    guard = z3.And(*atoms)
    clauses = [z3.Or(w + x == 7, *[z3.Not(a) for a in ordered]),
               z3.Or(w == 0, guard), y == w*w]
    if reverse:
        clauses.reverse()
    original = z3.Exists([w], z3.And(*clauses))
    actual = module.eliminate_existential_definitions(original)
    assert actual.conditional_definitions == 1
    assert not z3.is_quantifier(actual.formula)
    value = z3.If(guard, 7-x, 0)
    equivalent(original, actual.formula)
    equivalent(actual.formula, y == value*value)


@pytest.mark.parametrize('sign', [-1, 1])
def test_complete_domains_aliases_and_ordered_signed_costs_survive(sign):
    a, b = z3.Bools('a b')
    w, x, y, alias, c0, c1 = z3.Ints('w x y alias c0 c1')
    guard = z3.And(a, b)
    original = z3.Exists([w], z3.And(
        z3.Or(w+x == 7, z3.Not(a), z3.Not(b)), z3.Or(w == 0, guard),
        w >= 1, w <= 4, y == w*w, alias == w*w,
        c0 == sign*(w*w+1), c1 == -2*w*w))
    actual = module.eliminate_existential_definitions(original)
    assert actual.conditional_definitions == 1
    value = z3.If(guard, 7-x, 0)
    correct = z3.And(value >= 1, value <= 4, y == value*value,
                     alias == value*value, c0 == sign*(value*value+1), c1 == -2*value*value)
    equivalent(original, actual.formula)
    equivalent(actual.formula, correct)
    unequal(actual.formula, z3.And(y == value*value, alias == value*value,
                                   c0 == sign*(value*value+1), c1 == -2*value*value))
    unequal(actual.formula, z3.And(value >= 1, value <= 4, y == value*value,
        alias == value*value, c1 == sign*(value*value+1), c0 == -2*value*value))


@pytest.mark.parametrize('mode', ['missing', 'wrong-atom', 'same-polarity', 'self-guard'])
def test_incomplete_or_self_referential_guard_keeps_original_binder(mode):
    a,b,c = z3.Bools('a b c'); w,x,y = z3.Ints('w x y')
    first = z3.Or(w+x == 7, z3.Not(a), z3.Not(b))
    clauses = [first, w >= 0, w <= 20, y == w*w]
    if mode == 'wrong-atom':
        clauses.append(z3.Or(w == 0, z3.And(a,c)))
    elif mode == 'same-polarity':
        clauses.append(z3.Or(w == 0, z3.Not(a), z3.Not(b)))
    elif mode == 'self-guard':
        clauses[0] = z3.Or(w+x == 7, z3.Not(a), z3.Not(w > 0))
        clauses.append(z3.Or(w == 0, z3.And(a,w > 0)))
    original = z3.Exists([w], z3.And(*clauses))
    actual = module.eliminate_existential_definitions(original)
    assert actual.conditional_definitions == actual.direct_definitions == 0
    assert actual.formula.eq(original)


def test_competing_values_and_other_constraints_are_not_erased():
    a,b = z3.Bools('a b'); w,x,y = z3.Ints('w x y')
    original = z3.Exists([w], z3.And(z3.Or(w+x == 7,z3.Not(a),z3.Not(b)),
        z3.Or(w+x == 8,z3.Not(a),z3.Not(b)),z3.Or(w == 0,z3.And(a,b)),y == w*w))
    actual = module.eliminate_existential_definitions(original)
    assert actual.conditional_definitions == 1
    equivalent(original, actual.formula)
    equivalent(actual.formula, z3.And(z3.Not(z3.And(a,b)), y == 0))


def test_real_coefficients_keep_exact_rational_values():
    a,b=z3.Bools('a b');w,x,y=z3.Reals('w x y')
    original=z3.Exists([w],z3.And(z3.Or(w+x==z3.RealVal('2/7'),z3.Not(a),z3.Not(b)),
        z3.Or(w==z3.RealVal('-1/3'),z3.And(a,b)),y==w*w))
    actual=module.eliminate_existential_definitions(original)
    assert actual.conditional_definitions==1
    value=z3.If(z3.And(a,b),z3.RealVal('2/7')-x,z3.RealVal('-1/3'))
    equivalent(original,actual.formula)
    equivalent(actual.formula,y==value*value)


def test_acyclic_piecewise_witnesses_can_define_aggregate_in_same_relation():
    a,b,c,d=z3.Bools('a b c d');w,v,total,x,y=z3.Ints('w v total x y')
    original=z3.Exists([w,v,total],z3.And(
        z3.Or(w+x==7,z3.Not(a),z3.Not(b)),z3.Or(w==0,z3.And(a,b)),
        z3.Or(v-x==2,z3.Not(c),z3.Not(d)),z3.Or(v==0,z3.And(c,d)),
        z3.Or(total-w-v==5,z3.Not(a),z3.Not(b)),z3.Or(total-w-v==0,z3.And(a,b)),
        total>=0,y>=total))
    actual=module.eliminate_existential_definitions(original)
    assert actual.conditional_definitions==3 and not z3.is_quantifier(actual.formula)
    value=z3.If(z3.And(a,b),7-x,0)+z3.If(z3.And(c,d),2+x,0)+z3.If(z3.And(a,b),5,0)
    equivalent(original,actual.formula)
    equivalent(actual.formula,z3.And(value>=0,y>=value))


def test_outer_demorgan_does_not_walk_shared_arithmetic_ite_tree(monkeypatch):
    w,x,y=z3.Ints('w x y');a,b=z3.Bools('a b');term=x
    for i in range(600):
        term=z3.If(x>=i,term+1,term-1)
    clauses=[z3.Or(w+term==7,z3.Not(a),z3.Not(b)),z3.Or(w==0,z3.And(a,b))]
    original_simplify=z3.simplify
    def checked(expression,*args,**kwargs):
        assert not kwargs.get('elim_and',False)
        return original_simplify(expression,*args,**kwargs)
    monkeypatch.setattr(module.z3,'simplify',checked)
    definitions=module._conditional(clauses,{w.get_id():w},all_definitions=True)
    assert w.get_id() in definitions
