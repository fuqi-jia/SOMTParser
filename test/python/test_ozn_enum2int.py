import json
import os
from pathlib import Path
import subprocess

import pytest
import z3

from tools.semantic_checks.source_oracles.fzn_json_source import read_source, Unsupported
from tools.semantic_checks.source_oracles.ozn_observations import Program, Expression, Array, ABSENT


def source(variables=None, constraints=None, solve=None):
    return read_source(dict(version='1.0', variables=variables or {}, arrays={},
                            constraints=constraints or [], output=[], solve=solve or dict(method='satisfy')))


def call(value):
    return Expression(Program('', source()), [], {}).call('enum2int', [value])


@pytest.mark.parametrize('value', [-3, 0, 1, 41])
def test_integer_representation_is_preserved_without_guessing_domain(value):
    term = z3.IntVal(value)
    assert call(term).eq(term)


def test_symbolic_ordinal_does_not_gain_bounds():
    term = z3.Int('enum_integer')
    assert call(term).eq(term)
    solver=z3.Solver(); solver.add(call(term)<0); assert solver.check()==z3.sat


def test_array_coercion_preserves_rank_coordinates_and_aliases():
    a, b=z3.Ints('enum_a enum_b'); value=Array(((-2,3),(5,7)),[a,b,a,b])
    out=call(value)
    assert out is value and out.dimensions==((-2,3),(5,7))
    assert out.at((3,5)).eq(a) and out.at((-2,7)).eq(b)


@pytest.mark.parametrize('value',[frozenset({-3,2,9}),z3.Const('enum_set',z3.SetSort(z3.IntSort()))])
def test_set_representation_preserves_membership(value):
    out=call(value)
    assert out is value


@pytest.mark.parametrize('value',[z3.BoolVal(True),z3.RealVal(1),ABSENT,'symbol',Array(((1,),),[z3.BoolVal(False)]),Array(((1,2),),[z3.IntVal(1),frozenset({2})])])
def test_bad_or_absent_representation_is_not_coerced(value):
    with pytest.raises(Unsupported,match='enum2int'):
        call(value)


@pytest.mark.parametrize('args',[[],[z3.IntVal(1),z3.IntVal(2)]])
def test_enum2int_arity(args):
    with pytest.raises(Unsupported,match='arity'):
        Expression(Program('',source()),[],{}).call('enum2int',args)


@pytest.mark.parametrize('shift',[0,1])
def test_original_domains_and_signed_cost_are_retained(shift):
    flat=source({'s':dict(type='int',domain=[[1,3]])},solve=dict(method='maximize',objective='s'))
    program=Program('int:s;int:objective=enum2int(s);',flat)
    observed=program.name('objective',{});out,cost=z3.Ints('out cost')
    relation=flat.projected([(out,observed)],signed_cost=cost)
    candidate=z3.And(out>=1,out<=3,cost==-out+shift)
    solver=z3.Solver();solver.add(z3.Xor(relation,candidate))
    assert solver.check()==(z3.unsat if shift==0 else z3.sat)


def test_actual_official_compiler_enum_output(tmp_path):
    compiler=Path(os.environ['SOMTPARSER_MINIZINC_EXECUTABLE'])
    model=tmp_path/'source.mzn'
    model.write_text('enum Shelf = S(1..3);\narray[1..2] of var Shelf: shelf :: add_to_output;\nvar int: objective :: add_to_output = enum2int(max(shelf));\nsolve minimize objective;\n')
    command=[str(compiler),'-c','-g','--no-half-reifications','--fzn-format','json','--output-mode','dzn','--output-objective','--solver','org.gecode.gecode','--output-base',str(tmp_path/'reference'),str(model)]
    process=subprocess.run(command,capture_output=True,text=True)
    (tmp_path/'official-process.json').write_text(json.dumps(dict(argv=command,returncode=process.returncode,stdout=process.stdout,stderr=process.stderr),indent=2)+'\n')
    assert process.returncode==0,process.stderr
    flat=read_source((tmp_path/'reference.fzn.json').read_bytes());program=Program((tmp_path/'reference.ozn').read_text(),flat)
    observations=program.observations(['shelf','objective']);public=[z3.FreshInt('observed_enum')for _ in observations];cost=z3.FreshInt('signed_cost')
    relation=flat.projected(list(zip(public,[row['value']for row in observations])),signed_cost=cost)
    a,b,objective=public;expected=z3.And(a>=1,a<=3,b>=1,b<=3,objective==z3.If(a>=b,a,b),cost==objective)
    solver=z3.Solver();solver.add(z3.Xor(relation,expected));assert solver.check()==z3.unsat
