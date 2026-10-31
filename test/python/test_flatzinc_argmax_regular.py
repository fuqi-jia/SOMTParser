"""Exact Gecode argmax and DFA relations from independent finite enumeration.

No native implementation or HIR lowering is used by the Python references.
Every relation is checked by whole-module loading and an actual XOR query.
"""
from itertools import product
from fractions import Fraction
import json
import os
from pathlib import Path
import subprocess
import tempfile

import pytest
import z3

if not os.environ.get("SOMT_FZN_CLI"):
    import somtparser as sp


PROFILES = ("default", "ground", "quantified")
MODES = ("base", "reif", "imp", "negative")


def call(name, arguments, mode):
    if mode == "base":
        return f"constraint {name}({arguments});", None
    if mode == "negative":
        return f"constraint {name}_reif({arguments},false);", None
    return f"var bool: b; constraint {name}_{mode}({arguments},b);", z3.Bool("b")


def polarity(relation, mode, flag):
    if mode == "negative":
        return z3.Not(relation)
    if mode == "reif":
        return flag == relation
    if mode == "imp":
        return z3.Implies(flag, relation)
    return relation


def exact(source, expected, profile):
    if os.environ.get("SOMT_FZN_CLI"):
        process, report = cli_translate(source + "\nsolve satisfy;", profile)
        assert process.returncode == 0, process.stderr
        assert report["fidelity"]["sound"] and report["fidelity"]["complete"]
        script = process.stdout
    else:
        result = sp.translate(source=source + "\nsolve satisfy;", language="flatzinc",
                              profile=profile, dialect=sp.OmtDialect.Z3)
        assert result.ok, [d.message for d in result.diagnostic_items]
        assert result.report.fidelity.sound and result.report.fidelity.complete
        script = result.to_smt2(sp.OmtDialect.Z3)
    whole = z3.Optimize()
    whole.from_string(script)
    assert len(whole.objectives()) == 0
    checker = z3.Solver()
    checker.add(z3.Xor(z3.And(*whole.assertions()), expected))
    outcome = checker.check()
    assert outcome == z3.unsat, (outcome, checker.reason_unknown())


def cli_translate(source, profile):
    with tempfile.TemporaryDirectory(prefix="fzn-control-") as directory:
        report = Path(directory) / "report.json"
        process = subprocess.run([os.environ["SOMT_FZN_CLI"], profile, str(report)],
                                 input=source, text=True, capture_output=True)
        return process, json.loads(report.read_text()) if report.exists() else None


@pytest.mark.parametrize("profile", PROFILES)
@pytest.mark.parametrize("mode", MODES)
@pytest.mark.parametrize("offset", [-3, 1, 2**80 + 17])
def test_argmax_first_tie_exact_offset_and_repeated_alias(profile, mode, offset):
    source = "var -1..1: x; var -1..1: y; var int: i;"
    source += "array [1..5] of var int: a = [x,y,x,0,y];"
    constraint, flag = call("gecode_maximum_arg_int_offset", f"a,{offset},i", mode)
    x, y, index = z3.Ints("x y i")
    accepted = []
    for xv, yv in product(range(-1, 2), repeat=2):
        values = [xv, yv, xv, 0, yv]
        first = values.index(max(values))
        accepted.append(z3.And(x == xv, y == yv, index == offset + first))
    domains = z3.And(x >= -1, x <= 1, y >= -1, y <= 1)
    exact(source + constraint,
          z3.And(domains, polarity(z3.Or(*accepted), mode, flag)), profile)


@pytest.mark.parametrize("profile", PROFILES)
@pytest.mark.parametrize("mode", MODES)
@pytest.mark.parametrize("values,offset", [([7], 0), ([7, 7, 6], -2)])
def test_argmax_constant_relations(profile, mode, values, offset):
    constraint, flag = call("gecode_maximum_arg_int_offset", f"{values},{offset},i", mode)
    relation = z3.Int("i") == offset + values.index(max(values))
    exact("var int: i;" + constraint, polarity(relation, mode, flag), profile)


@pytest.mark.parametrize("profile", PROFILES)
@pytest.mark.parametrize("mode", MODES)
def test_argmax_result_may_also_be_an_input(profile, mode):
    source = ("predicate gecode_maximum_arg_int_offset(array [int] of var int: x, int: o, var int: i);"
              "var -1..2: i; var -1..1: x; int: offset = 0;")
    constraint, flag = call("gecode_maximum_arg_int_offset", "[i,x,i],offset,i", mode)
    index, x = z3.Ints("i x")
    accepted_values = []
    for iv, xv in product(range(-1, 3), range(-1, 2)):
        values = [iv, xv, iv]
        if iv == values.index(max(values)):
            accepted_values.append(z3.And(index == iv, x == xv))
    domain = z3.And(index >= -1, index <= 2, x >= -1, x <= 1)
    exact(source + constraint, z3.And(domain, polarity(z3.Or(*accepted_values), mode, flag)), profile)


def accepted(word, q, alphabet, table, start, finals):
    state = start
    for symbol in word:
        if state == 0 or symbol < 1 or symbol > alphabet:
            return False
        state = table[(state - 1) * alphabet + symbol - 1]
    return state in finals


DFA = [
    (2, 2, [1, 2, 0, 2], 1, [2]),
    (2, 2, [1, 0, 2, 0], 2, [2]),
    (1, 1, [0], 1, [1]),
    (2, 2, [2, 1, 1, 2], 1, []),
]


@pytest.mark.parametrize("profile", PROFILES)
@pytest.mark.parametrize("mode", MODES)
@pytest.mark.parametrize("length", [0, 1, 3])
@pytest.mark.parametrize("q,alphabet,table,start,finals", DFA)
def test_regular_complete_language_including_out_of_alphabet(profile, mode, length,
                                                            q, alphabet, table, start, finals):
    names = [f"x{i}" for i in range(length)]
    source = ("predicate gecode_regular(array [int] of var int: x, int: Q, int: S,"
              "array [int] of int: d, int: q0, set of int: F);")
    source += "".join(f"var int: {name};" for name in names)
    source += f"array [1..{len(table)}] of int: transitions = {table};"
    final_text = "{" + ",".join(map(str, finals)) + "}"
    args = f"[{','.join(names)}],{q},{alphabet},transitions,{start},{final_text}"
    constraint, flag = call("gecode_regular", args, mode)
    variables = [z3.Int(name) for name in names]
    # Enumerate the entire finite accepted language. Inputs remain unbounded,
    # so the XOR also checks rejection of every other integer symbol.
    words = [z3.And(*[variable == value for variable, value in zip(variables, word)])
             for word in product(range(1, alphabet + 1), repeat=length)
             if accepted(word, q, alphabet, table, start, finals)]
    exact(source + constraint, polarity(z3.Or(*words), mode, flag), profile)


@pytest.mark.parametrize("profile", PROFILES)
@pytest.mark.parametrize("mode", MODES)
@pytest.mark.parametrize("finals", ["{1,2,2}", "1..2", "{}", "4..3"])
def test_regular_parameters_ranges_duplicates_and_repeated_input(profile, mode, finals):
    source = "var int: x; int: q = 2; int: s = 2; int: start = 1;"
    source += f"set of int: final = {finals}; set of int: alias = final;"
    source += "array [1..4] of int: table = [2,0,1,2];"
    constraint, flag = call("gecode_regular", "[x,x],q,s,table,start,alias", mode)
    relation = z3.Int("x") == 1 if finals in ("{1,2,2}", "1..2") else z3.BoolVal(False)
    exact(source + constraint, polarity(relation, mode, flag), profile)


REJECTED = [
    "constraint gecode_maximum_arg_int_offset([],0,1);",
    "constraint gecode_maximum_arg_int_offset_reif([],0,1,false);",
    "constraint gecode_maximum_arg_int_offset_imp([],0,1,false);",
    "constraint gecode_maximum_arg_int_offset([true],0,1);",
    "constraint gecode_maximum_arg_int_offset([],false,1);",
    "constraint gecode_maximum_arg_int_offset([],0,true);",
    "var int: o; constraint gecode_maximum_arg_int_offset([1],o,1);",
    "constraint gecode_regular([true],1,1,[1],1,{1});",
    "constraint gecode_regular([],0,1,[],1,{});",
    "constraint gecode_regular([],1,0,[],1,{});",
    "constraint gecode_regular([],1,1,[1],0,{1});",
    "constraint gecode_regular([],1,1,[1],2,{1});",
    "constraint gecode_regular([],2,2,[1,2,1],1,{1});",
    "constraint gecode_regular([],1,1,[-1],1,{1});",
    "constraint gecode_regular([],1,1,[2],1,{1});",
    "constraint gecode_regular([],1,1,[1],1,{0});",
    "constraint gecode_regular([],1,1,[1],1,{2});",
    "constraint gecode_regular([],1,1,[1],1,0..1);",
    "constraint gecode_regular([],1,1,[1],1,1..2);",
    "constraint gecode_regular([],1,1,[1],1,true);",
    "var set of 1..1: f; constraint gecode_regular([],1,1,[1],1,f);",
    "var int: q; constraint gecode_regular([],q,1,[1],1,{1});",
    "var int: t; constraint gecode_regular([],1,1,[t],1,{1});",
    "array [1..1] of var int: t = [1]; constraint gecode_regular([],1,1,t,1,{1});",
    "constraint gecode_regular([],1,1,[true],1,{1});",
    "constraint gecode_regular([],1,1,[1],true,{1});",
    "constraint gecode_regular([],1,1,[1],1,{1},false);",
]


@pytest.mark.parametrize("source", REJECTED)
def test_malformed_parameter_and_type_contracts_are_rejected(source):
    if os.environ.get("SOMT_FZN_CLI"):
        process, _ = cli_translate(source + " solve satisfy;", "default")
        assert process.returncode == 2, process.stderr
        assert process.stderr.strip()
        return
    result = sp.translate(source=source + " solve satisfy;", language="flatzinc")
    assert not result.ok
    assert any(d.message for d in result.diagnostic_items)


@pytest.mark.parametrize("profile", PROFILES)
@pytest.mark.parametrize("direction", ["minimize", "maximize"])
@pytest.mark.parametrize("term", ["obj", "+7", "-7", "+1.5", "-1.25", "+2.0"])
def test_retained_annotated_goal_direction_and_signed_numeric_repairs(profile, direction, term):
    source = ("var -9..9: obj :: note(\") = phantom\");"
              f"solve :: seq_search([note(\"minimize; )\", [1,2])]) {direction} {term};")
    if os.environ.get("SOMT_FZN_CLI"):
        process, report = cli_translate(source, profile)
        assert process.returncode == 0, process.stderr
        assert report["fidelity"]["sound"] and report["fidelity"]["complete"]
        script = process.stdout
    else:
        result = sp.translate(source=source, language="flatzinc", profile=profile,
                              dialect=sp.OmtDialect.Z3)
        assert result.ok, [d.message for d in result.diagnostic_items]
        script = result.to_smt2(sp.OmtDialect.Z3)
    whole = z3.Optimize()
    whole.from_string(script)
    assert len(whole.objectives()) == 1
    obj = z3.Int("obj")
    reference = obj if term == "obj" else (z3.RealVal(str(Fraction(term))) if "." in term else z3.IntVal(int(term)))
    signed = -reference if direction == "maximize" else reference
    checker = z3.Solver()
    checker.add(whole.objectives()[0] != signed)
    assert checker.check() == z3.unsat
    checker = z3.Solver()
    checker.add(z3.Xor(z3.And(*whole.assertions()), z3.And(obj >= -9, obj <= 9)))
    assert checker.check() == z3.unsat
