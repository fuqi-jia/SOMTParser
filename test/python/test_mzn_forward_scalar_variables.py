"""Forward global scalar variables resolve without weakening their domains."""
import pytest
import somtparser as sp

z3 = pytest.importorskip("z3")


def status(result):
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(z3.parse_smt2_string(result.to_smt2()))
    return solver.check()


def test_forward_int_range_is_declared_and_domain_is_retained():
    valid = sp.translate(
        source="constraint x=1; var 1..10:x; solve satisfy;",
        language="minizinc",
    )
    assert status(valid) == z3.sat
    assert valid.report.stats.num_vars == 1
    # If the later range were omitted, x=0 would be satisfiable.
    assert status(sp.translate(
        source="constraint x=0; var 1..10:x; solve satisfy;",
        language="minizinc",
    )) == z3.unsat


def test_forward_scalar_formula_can_be_sat_or_unsat():
    assert status(sp.translate(
        source="constraint x=1; var 1..10:x; solve satisfy;",
        language="minizinc",
    )) == z3.sat
    assert status(sp.translate(
        source="constraint x=1 /\\ x=2; var 1..10:x; solve satisfy;",
        language="minizinc",
    )) == z3.unsat


def test_forward_bool_and_float_keep_the_declared_carrier():
    assert status(sp.translate(
        source="constraint b; var bool:b; solve satisfy;",
        language="minizinc",
    )) == z3.sat
    assert status(sp.translate(
        source="constraint r=1.5; var float:r; solve satisfy;",
        language="minizinc",
    )) == z3.sat


def test_forward_identifier_still_checks_type_errors_and_duplicates():
    wrong_sort = sp.translate(
        source='constraint x="wrong sort"; var 1..10:x; solve satisfy;',
        language="minizinc",
    )
    assert not wrong_sort.ok
    assert all("undeclared identifier" not in d.message
               for d in wrong_sort.diagnostic_items)

    duplicate = sp.translate(
        source="constraint x=1; var 1..10:x; var 1..10:x; solve satisfy;",
        language="minizinc",
    )
    assert not duplicate.ok
    assert any("already declared" in d.message for d in duplicate.diagnostic_items)


def test_generator_binding_shadows_forward_global():
    result = sp.translate(
        source=("constraint forall (x in 1..2) (x > 0);"
                "constraint x=5; var 1..10:x; solve satisfy;"),
        language="minizinc",
    )
    assert status(result) == z3.sat


def test_later_included_scalar_declaration_resolves_earlier_use(tmp_path):
    (tmp_path / "later.mzn").write_text("var 1..10:x;\n")
    model = tmp_path / "model.mzn"
    model.write_text(
        'constraint x=1; include "later.mzn"; solve satisfy;\n'
    )
    assert status(sp.translate(str(model), language="minizinc")) == z3.sat
