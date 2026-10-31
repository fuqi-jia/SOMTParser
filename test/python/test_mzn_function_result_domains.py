"""A call preserves body partiality under value and Boolean consumers."""
import os
import subprocess

import pytest
import somtparser as sp
import z3


_PREFIX = """
array[1..2] of int: table = [7,9];
var 0..2: index;
function var int: lookup(int: ignored) = table[index];
"""

_CASES = [
    ("invalid-positive", _PREFIX + "constraint index=0 /\\ lookup(1)=7;", "unsat"),
    ("invalid-negated", _PREFIX + "constraint index=0 /\\ not(lookup(1)=7);", "sat"),
    ("invalid-default", _PREFIX + "constraint index=0 /\\ (lookup(1) default 7)=7;", "sat"),
    ("invalid-wrong-default", _PREFIX + "constraint index=0 /\\ (lookup(1) default 7)=9;", "unsat"),
    ("valid-first", _PREFIX + "constraint index=1 /\\ lookup(1)=7;", "sat"),
    ("valid-second", _PREFIX + "constraint index=2 /\\ lookup(1)=9;", "sat"),
    ("valid-default-does-not-override", _PREFIX + "constraint index=2 /\\ (lookup(1) default 7)=7;", "unsat"),
    ("nested", _PREFIX + "function var int: nested(int: n)=lookup(n)+1; constraint index=0 /\\ nested(1)=8;", "unsat"),
    ("nested-default", _PREFIX + "function var int: nested(int: n)=lookup(n)+1; constraint index=0 /\\ (nested(1) default 5)=5;", "sat"),
    ("coerced-real", _PREFIX + "function var float: real_lookup(int: n)=table[index]; constraint index=0 /\\ real_lookup(1)=7.0;", "unsat"),
]
for name, condition, expected in [
    ("argmax-function", "arg_max(t in 1..2)(f(t))=2", "unsat"),
    ("argmax-function-negated", "not(arg_max(t in 1..2)(f(t))=2)", "sat"),
]:
    _CASES.append((name, 'include "globals.mzn"; array[1..2] of int:e=[0,2]; '
                   'array[1..2] of var 0..2:p; function var int:f(int:t)=e[p[t]]; '
                   'constraint p[1]=0 /\\ p[2]=2; constraint ' + condition + ';', expected))


@pytest.mark.parametrize("name,source,expected", _CASES, ids=[x[0] for x in _CASES])
def test_function_body_domain(name, source, expected, tmp_path):
    source += " solve satisfy;"
    result = sp.translate(source=source, language="minizinc", strict=True,
                          dialect=sp.OmtDialect.Z3)
    solver = z3.Solver()
    solver.from_string(result.to_smt2(dialect=sp.OmtDialect.Z3))
    assert str(solver.check()) == expected
    official = os.environ.get("SOMTPARSER_MINIZINC_EXECUTABLE")
    if official:
        path = tmp_path / (name + ".mzn")
        path.write_text(source)
        backend = os.environ.get("SOMTPARSER_MINIZINC_SOLVER", "gecode")
        reference = subprocess.run([official, "--solver", backend, str(path)],
                                   text=True, capture_output=True, check=False)
        assert reference.returncode == 0, reference.stderr
        answer = "unsat" if "=====UNSATISFIABLE=====" in reference.stdout else (
            "sat" if "----------" in reference.stdout else "unknown")
        assert answer == expected, reference.stdout + reference.stderr
