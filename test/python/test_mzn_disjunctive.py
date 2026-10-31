"""MiniZinc task non-overlap preserves zero lengths and Boolean polarity."""
import pytest
import somtparser as sp
import z3


CASES = [('zero_inside', 'include "disjunctive.mzn";constraint disjunctive([0,1],[3,0]);solve satisfy;', 'sat'), ('strict_zero_inside', 'include "disjunctive_strict.mzn";constraint disjunctive_strict([0,1],[3,0]);solve satisfy;', 'unsat'), ('negative_duration', 'include "disjunctive.mzn";constraint disjunctive([0],[-1]);solve satisfy;', 'unsat'), ('negative_duration_negated', 'include "disjunctive.mzn";constraint not disjunctive([0],[-1]);solve satisfy;', 'sat'), ('strict_endpoint', 'include "disjunctive_strict.mzn";constraint disjunctive_strict([0,3],[3,0]);solve satisfy;', 'sat'), ('empty', 'include "disjunctive.mzn";constraint disjunctive([],[]);solve satisfy;', 'reject'), ('booleans', 'include "disjunctive.mzn";constraint disjunctive([false,true],[1,1]);solve satisfy;', 'sat'), ('zero_ties', 'include "disjunctive_strict.mzn";constraint disjunctive_strict([0,0],[0,0]);solve satisfy;', 'sat')]


@pytest.mark.parametrize("name,source,expected", CASES, ids=[r[0] for r in CASES])
def test_disjunctive_matches_reference(name, source, expected):
    result = sp.translate(source=source, language="minizinc")
    if expected == "reject":
        assert not result.ok
        assert any("empty duration" in d.message for d in result.diagnostic_items)
        return
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(*z3.parse_smt2_string(result.to_smt2(sp.OmtDialect.Z3)))
    assert str(solver.check()) == expected


@pytest.mark.parametrize("strict", [False, True])
def test_disjunctive_reification_is_exact_for_symbolic_starts_and_durations(strict):
    name = "disjunctive_strict" if strict else "disjunctive"
    source = f'include "{name}.mzn";array[-2..0] of var int:s;array[-2..0] of var int:d;var bool:b;constraint b={name}(s,d);solve satisfy;'
    result = sp.translate(source=source, language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]
    actual = z3.And(*z3.parse_smt2_string(result.to_smt2(sp.OmtDialect.Z3)))
    s = z3.Array("s", z3.IntSort(), z3.IntSort())
    d = z3.Array("d", z3.IntSort(), z3.IntSort())
    terms = [d[i] >= 0 for i in range(-2, 1)]
    for i in range(-2, 1):
        for j in range(i + 1, 1):
            alternatives = [s[i] + d[i] <= s[j], s[j] + d[j] <= s[i]]
            if not strict:
                alternatives += [d[i] == 0, d[j] == 0]
            terms.append(z3.Or(*alternatives))
    expected = z3.Bool("b") == z3.And(*terms)
    solver = z3.Solver()
    solver.set(timeout=10000)
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


@pytest.mark.parametrize("source", [
    'array[1..2] of var int:s;array[2..3] of var int:d;constraint disjunctive(s,d);solve satisfy;',
    'constraint disjunctive([1.5],[1]);solve satisfy;',
    'array[1..0] of var float:s;array[1..0] of var int:d;constraint disjunctive_strict(s,d);solve satisfy;',
])
def test_disjunctive_checks_index_sets_and_element_types(source):
    result = sp.translate(source='include "disjunctive.mzn";'+source, language="minizinc")
    assert not result.ok
    assert any("index sets" in d.message or "Int-compatible" in d.message
               for d in result.diagnostic_items)


def test_strict_empty_relation_is_true():
    result = sp.translate(source='include "disjunctive_strict.mzn";constraint not disjunctive_strict([],[]);solve satisfy;',language="minizinc")
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.add(*z3.parse_smt2_string(result.to_smt2(sp.OmtDialect.Z3)))
    assert solver.check() == z3.unsat
