"""Local scalar domains stay scoped; free locals are existential witnesses."""
from _public_relation import public_relation
import pytest
import z3
import somtparser as sp


def translate(source):
    result = sp.translate(source=source + ' solve satisfy;', language='minizinc')
    assert result.ok, [d.message for d in result.diagnostic_items]
    script = result.to_smt2(sp.OmtDialect.Z3)
    return script, public_relation(result, script)


def equivalent(source, expected):
    script, actual = translate(source)
    solver = z3.Solver()
    solver.set(timeout=10000)
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat
    return script


def test_original_groupsplitter_count_form_keeps_independent_witnesses():
    a = z3.Array('a', z3.IntSort(), z3.IntSort())
    counts = [z3.Sum(*[z3.If(a[i] == g, 1, 0) for i in range(1, 4)]) for g in (1, 2)]
    expected = z3.And(*[z3.And(a[i] >= 1, a[i] <= 2) for i in range(1, 4)],
                      *[z3.And(c >= 1, c <= 3) for c in counts])
    script = equivalent('array[1..3] of var 1..2: a; '
                        'constraint forall(g in 1..2) '
                        '(let {var 1..3: c} in count(a,g,c));', expected)
    assert '(declare-fun !somt_exists_' in script
    assert not any('@let' in line and '(declare-fun ' in line for line in script.splitlines())


@pytest.mark.parametrize('domain,expected', [('1..3', lambda x: z3.And(x>=1,x<=3)),
                                            ('{1,4,9}', lambda x: z3.Or(x==1,x==4,x==9)),
                                            ('{}', lambda x: z3.BoolVal(False))])
def test_local_domains_are_exact_including_sparse_and_empty(domain,expected):
    x = z3.Int('x')
    equivalent('var int: x; constraint let {var '+domain+': c} in c=x;', expected(x))


@pytest.mark.parametrize('prefix', ['false -> ', 'true \\/ '])
def test_inactive_boolean_branch_does_not_leak_an_empty_local_domain(prefix):
    equivalent('constraint '+prefix+'(let {var 2..1: c} in c=0);', z3.BoolVal(True))


def test_local_constraint_and_initializer_preserve_definedness():
    x = z3.Int('x')
    equivalent('var int:x; constraint let {var 1..3:c=x; constraint c!=2;} in c>0;',
               z3.And(x>=1,x<=3,x!=2))
    equivalent('constraint not (let {var int: unused=1 div 0;} in true);', z3.BoolVal(True))
    equivalent('constraint not ((let {var int:c=1 div 0;} in c)>0);', z3.BoolVal(True))


def test_shadowing_and_initializer_see_the_enclosing_binding():
    x = z3.Int('x')
    equivalent('var int:x; constraint let {var int:x=x+1;} in x=3;', x==2)
    equivalent('constraint forall(x in 1..2) '
               '(let {int:x=x+1; int:y=x;} in y>=2);', z3.BoolVal(True))
    equivalent('constraint let {int:x=1;} in '
               '((let {int:x=2;} in x=2) /\\ x=1);', z3.BoolVal(True))


def test_uninitialized_bool_and_real_locals_are_bound():
    equivalent('constraint let {var bool:b; constraint b;} in b;', z3.BoolVal(True))
    x = z3.Real('x')
    equivalent('var float:x; constraint let {var float:y; constraint y>x;} in y<x+1;',
               z3.BoolVal(True))
    equivalent('constraint let {float:r=0.5; bool:b=true;} in b /\\ r>0.0;', z3.BoolVal(True))


@pytest.mark.parametrize('expression', [
    'not (let {var int:c;} in c=1)',
    '(let {var int:c;} in c=1) -> true',
    '(let {var int:c;} in c=1) <-> true',
    '(let {var int:c;} in c=1) = true',
    'bool2int(let {var int:c;} in c=1) > 0',
    '(let {var int:c;} in c=1) + 1 > 0',
])
def test_free_local_rejected_in_minizinc_negative_context(expression):
    result = sp.translate(source='constraint '+expression+';solve satisfy;', language='minizinc')
    assert not result.ok
    assert any('non-positive context' in d.message for d in result.diagnostic_items)


@pytest.mark.parametrize('expression', [
    'let {int:x=1;int:x=2;} in x=2',
    'let {var bool:b=2;} in b',
    'let {int:x;} in x=1',
    'let {constraint 3;} in true',
    'let {int:x=1 int:y=2;} in true',
])
def test_invalid_let_items_report_a_diagnostic(expression):
    result = sp.translate(source='constraint '+expression+';solve satisfy;', language='minizinc')
    assert not result.ok
