"""Regression cases for parsed par/var dispatch of a test/native overload."""

import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


def _status(source):
    translated = sp.translate(source=source, language="minizinc")
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.set(timeout=5000)
    solver.add(*z3.parse_smt2_string(
        translated.to_smt2(sp.OmtDialect.Z3), ctx=context))
    status = solver.check()
    assert status != z3.unknown, solver.reason_unknown()
    return status


def test_fixed_arrays_select_source_test_over_native_global():
    source = """
        test connected(array[int] of int: f, array[int] of int: t,
                       array[int] of bool: ns, array[int] of bool: es) = false;
        constraint connected([1], [2], [true, true], [true]);
        solve satisfy;
    """
    assert _status(source) == z3.unsat


def test_decision_arrays_fall_back_to_native_global_over_par_test():
    source = """
        test connected(array[int] of int: f, array[int] of int: t,
                       array[int] of bool: ns, array[int] of bool: es) = false;
        array[1..2] of var bool: ns;
        array[1..1] of var bool: es;
        constraint forall(i in 1..2)(ns[i]);
        constraint es[1];
        constraint connected([1], [2], ns, es);
        solve satisfy;
    """
    assert _status(source) == z3.sat


def test_let_shadowed_name_is_resolved_from_the_parsed_argument():
    source = """
        var int: selected;
        test connected(array[int] of int: f, array[int] of int: t,
                       array[int] of bool: ns, array[int] of bool: es) = false;
        constraint connected(
          [1], [2],
          [(let { int: selected = 1; } in selected = 1) | i in 1..2],
          [true]);
        solve satisfy;
    """
    assert _status(source) == z3.unsat


def test_parameter_function_in_generator_keeps_par_overload_applicable():
    source = """
        function bool: selected(int: i) = i > 0;
        test connected(array[int] of int: f, array[int] of int: t,
                       array[int] of bool: ns, array[int] of bool: es) = false;
        constraint connected([1], [2], [selected(i) | i in 1..2], [true]);
        solve satisfy;
    """
    assert _status(source) == z3.unsat
