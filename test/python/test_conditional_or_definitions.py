"""Flattened OR implications keep complete domains and signed-cost relations."""
import pytest
import z3
from tools.semantic_checks import existential_definitions as module


def equivalent(left, right):
    solver = z3.Solver();solver.add(z3.Xor(left, right))
    assert solver.check() == z3.unsat


def unequal(left, right):
    solver = z3.Solver();solver.add(z3.Xor(left, right))
    assert solver.check() == z3.sat


@pytest.mark.parametrize('width', [2, 3, 5])
@pytest.mark.parametrize('reverse', [False, True])
def test_flattened_or_complement_is_found_independent_of_literal_order(width, reverse):
    p, witness, observable = z3.Ints('p witness observable')
    literals = [z3.Bool(f'g{i}') for i in range(width)]
    guard = z3.Or(*literals)
    first = z3.Or(p - witness == -4, z3.Not(guard))
    second = z3.Or(*(list(reversed(literals)) if reverse else literals), p - witness == -1)
    original = z3.Exists([witness], z3.And(first, second, observable == witness*witness))
    result = module.eliminate_existential_definitions(original)
    assert result.conditional_definitions == 1 and not z3.is_quantifier(result.formula)
    term = p + z3.If(guard, 4, 1)
    equivalent(result.formula, observable == term*term)
    equivalent(original, result.formula)


@pytest.mark.parametrize('reverse', [False, True])
def test_flattened_clause_may_precede_its_binary_complement(reverse):
    a, b, c = z3.Bools('a b c');w, x, out = z3.Ints('w x out')
    guard = z3.Or(a, b, c)
    arms = [z3.Or(a, b, c, w == x - 2), z3.Or(z3.Not(guard), w == x + 3)]
    if reverse: arms.reverse()
    source = z3.Exists([w], z3.And(*arms, out == w*w))
    actual = module.eliminate_existential_definitions(source)
    assert actual.conditional_definitions == 1
    equivalent(source, actual.formula)
    equivalent(actual.formula, out == z3.If(guard, (x+3)*(x+3), (x-2)*(x-2)))


def test_nontrivial_domain_still_restricts_the_public_relation():
    a, b = z3.Bools('a b');w, x, out = z3.Ints('w x out');guard = z3.Or(a,b)
    source = z3.Exists([w], z3.And(z3.Or(z3.Not(guard), w == x+4),
        z3.Or(a,b,w == x+1), w >= 0, w <= 3, out == w*w))
    actual = module.eliminate_existential_definitions(source)
    term = x + z3.If(guard,4,1)
    correct = z3.And(term >= 0, term <= 3, out == term*term)
    equivalent(actual.formula, source);equivalent(actual.formula, correct)
    unequal(actual.formula, out == term*term)


@pytest.mark.parametrize('sign', [1, -1])
def test_complete_ordered_signed_cost_coordinates_are_retained(sign):
    a,b = z3.Bools('a b');w,x,y,c0,c1 = z3.Ints('w x y c0 c1');guard=z3.Or(a,b)
    source=z3.Exists([w],z3.And(z3.Or(z3.Not(guard),w==x+4),z3.Or(a,b,w==x+1),
        w>=0,y==w*w,c0==sign*(w*w+1),c1==-2*w*w))
    actual=module.eliminate_existential_definitions(source);term=x+z3.If(guard,4,1)
    correct=z3.And(term>=0,y==term*term,c0==sign*(term*term+1),c1==-2*term*term)
    equivalent(source,actual.formula);equivalent(actual.formula,correct)
    unequal(actual.formula,z3.And(term>=0,y==term*term,c1==sign*(term*term+1),c0==-2*term*term))


@pytest.mark.parametrize('mode', ['missing', 'noncomplementary', 'same-polarity'])
def test_incomplete_cover_cannot_define_the_witness(mode):
    a,b,c = z3.Bools('a b c');w,x,out = z3.Ints('w x out');guard=z3.Or(a,b)
    clauses=[z3.Or(a,b,w==x+1),w>=0,w<=9,out==w*w]
    if mode=='noncomplementary':clauses.append(z3.Or(z3.Not(z3.Or(a,c)),w==x+4))
    if mode=='same-polarity':clauses.append(z3.Or(a,b,w==x+4))
    source=z3.Exists([w],z3.And(*clauses))
    actual=module.eliminate_existential_definitions(source)
    assert actual.conditional_definitions==actual.direct_definitions==0
    assert actual.formula.eq(source)


def test_competing_definitions_remain_constraints_after_choosing_one():
    a,b = z3.Bools('a b');w,x,out = z3.Ints('w x out');guard=z3.Or(a,b)
    source=z3.Exists([w],z3.And(z3.Or(z3.Not(guard),w==x+4),
        z3.Or(z3.Not(guard),w==x+5),z3.Or(a,b,w==x+1),out==w*w))
    actual=module.eliminate_existential_definitions(source)
    equivalent(source,actual.formula)
    equivalent(actual.formula,z3.And(z3.Not(guard),out==(x+1)*(x+1)))


def test_guard_occurrence_of_witness_blocks_self_referential_choice():
    b=z3.Bool('b');w,x,out=z3.Ints('w x out');guard=z3.Or(w>0,b)
    source=z3.Exists([w],z3.And(z3.Or(z3.Not(guard),w==x+4),
        z3.Or(w>0,b,w==x+1),out==w*w))
    actual=module.eliminate_existential_definitions(source)
    assert actual.conditional_definitions==0 and actual.formula.eq(source)


def test_real_unit_coefficient_is_isolated_without_rounding():
    a,b=z3.Bools('a b');w,x,out=z3.Reals('w x out');guard=z3.Or(a,b)
    source=z3.Exists([w],z3.And(z3.Or(z3.Not(guard),x-w==z3.RealVal('-1/3')),
        z3.Or(a,b,x-w==z3.RealVal('-2/7')),out==w*w))
    actual=module.eliminate_existential_definitions(source)
    assert actual.conditional_definitions==1
    equivalent(source,actual.formula)
    term=x+z3.If(guard,z3.RealVal('1/3'),z3.RealVal('2/7'))
    equivalent(actual.formula,out==term*term)


def test_large_domain_or_does_not_construct_quadratic_guard_arguments(monkeypatch):
    w,x=z3.Ints('w x');a,b=z3.Bools('a b');guard=z3.Or(a,b)
    domain=z3.Or(*[w==i for i in range(2000)])
    clauses=[z3.Or(z3.Not(guard),w==x),domain]
    original_or=z3.Or;argument_count=0
    def counted(*args,**kwargs):
        nonlocal argument_count
        argument_count+=len(args)
        return original_or(*args,**kwargs)
    monkeypatch.setattr(module.z3,'Or',counted)
    result=module._conditional(clauses,{w.get_id():w},all_definitions=True)
    assert result=={} and argument_count<100
