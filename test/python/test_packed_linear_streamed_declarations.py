"""Independent relation/projection checks for streamed numeric declarations."""
import os
from pathlib import Path
import subprocess

import pytest

z3 = pytest.importorskip("z3")


@pytest.fixture(scope="module")
def exports(tmp_path_factory):
    root = Path(__file__).resolve().parents[2]
    build = os.environ.get("SOMTPARSER_BUILD_DIR")
    directories = ([Path(build)] if build else []) + [root / "build-rel", root / "build"]
    executable = next((p / "test" / "test_packed_linear_streamed_declarations"
                       for p in directories
                       if (p / "test" / "test_packed_linear_streamed_declarations").is_file()), None)
    if executable is None:
        pytest.skip("requires the C++ streamed-declaration test built by CMake")
    output = tmp_path_factory.mktemp("packed-linear-declarations")
    subprocess.run([str(executable), str(output)], check=True, timeout=90, capture_output=True)
    actual, ordinary = z3.Optimize(), z3.Optimize()
    actual.from_file(str(output / "packed.smt2"))
    ordinary.from_file(str(output / "expanded.smt2"))
    return actual, ordinary, (output / "packed.smt2").read_text()


def expected_relation():
    t, x, dep, bound = z3.Ints("true!1 x dep bound_only")
    f, collision, aux = z3.Reals("false!1 false!0 aux")
    return z3.And(0 <= t, t <= 2, -7 <= collision, collision <= 7,
                  -1 <= x, x <= 4, dep >= bound - 1, dep == x + 1,
                  t + f - aux == z3.RealVal("1/2"))


def check_status(formula, expected):
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(formula)
    assert solver.check() == expected


def test_full_relation_and_objective_match_ordinary_lowering(exports):
    actual, ordinary, _ = exports
    relation = z3.And(*actual.assertions())
    check_status(z3.Xor(relation, z3.And(*ordinary.assertions())), z3.unsat)
    check_status(z3.Xor(relation, expected_relation()), z3.unsat)
    assert len(actual.objectives()) == len(ordinary.objectives()) == 1
    check_status(actual.objectives()[0] != ordinary.objectives()[0], z3.unsat)
    # Optimize represents maximization by the negated minimization objective.
    check_status(actual.objectives()[0] != -(z3.Real("aux") - z3.RealVal("1/4")), z3.unsat)
    check_status(relation, z3.sat)


def test_auxiliary_projection_and_exact_objective_value(exports):
    actual, _, _ = exports
    relation = z3.And(*actual.assertions())
    aux = z3.Real("aux")
    value = z3.Int("true!1") + z3.Real("false!1") - z3.RealVal("1/2")
    check_status(z3.And(relation, aux != value), z3.unsat)
    projected = z3.substitute(relation, (aux, value))
    x, dep, bound = z3.Ints("x dep bound_only")
    t, collision = z3.Int("true!1"), z3.Real("false!0")
    expected_projection = z3.And(0 <= t, t <= 2, -7 <= collision, collision <= 7,
                                 -1 <= x, x <= 4, dep >= bound - 1, dep == x + 1)
    check_status(z3.Xor(projected, expected_projection), z3.unsat)
    check_status(z3.And(relation, actual.objectives()[0]
                        != -(value - z3.RealVal("1/4"))), z3.unsat)


@pytest.mark.parametrize("value,flag", [(-99, False), (101, True)])
def test_completely_unreferenced_columns_remain_free_and_declared(exports, value, flag):
    actual, _, text = exports
    # A new Z3 constant alone would make this satisfiability check vacuous if
    # the emitted source declaration were accidentally dropped.
    assert text.count("(declare-fun true!0 () Int)") == 1
    assert text.count("(declare-fun unused () Real)") == 1
    assert text.count("(declare-fun |space column| () Real)") == 1
    assert text.count("(declare-fun flag () Bool)") == 1
    check_status(z3.And(*actual.assertions(), z3.Int("true!0") == value,
                        z3.Real("unused") == value, z3.Real("space column") == value,
                        z3.Bool("flag") == flag), z3.sat)


@pytest.mark.parametrize("name,value", [("true!1", -1), ("true!1", 3), ("x", -2), ("x", 5)])
def test_streamed_and_materialized_domain_bounds_both_hold(exports, name, value):
    actual, _, _ = exports
    check_status(z3.And(*actual.assertions(), z3.Int(name) == value), z3.unsat)


def test_missing_packed_equation_is_detected_by_independent_oracle(exports):
    actual, _, _ = exports
    assertions = list(actual.assertions())
    # The defining row is the only hard formula mentioning this target-only
    # variable. Removing it must admit a wrong objective, while the full model
    # rejects precisely the same assignment.
    aux = z3.Real("aux")
    from z3.z3util import get_vars
    rows = [i for i, formula in enumerate(assertions)
            if any(aux.eq(variable) for variable in get_vars(formula))]
    assert len(rows) == 1
    mutant = z3.And(*(formula for i, formula in enumerate(assertions) if i != rows[0]))
    wrong = aux != z3.Int("true!1") + z3.Real("false!1") - z3.RealVal("1/2")
    check_status(z3.And(mutant, wrong), z3.sat)
    check_status(z3.And(*assertions, wrong), z3.unsat)
