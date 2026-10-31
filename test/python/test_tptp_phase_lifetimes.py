"""THF source ownership and theorem mode survive frontend phase teardown."""
import gc

import pytest
import somtparser as sp
import z3


@pytest.mark.parametrize("body", [
    "p", "(^ [X:$o] : X) @ p", "! [X:$o] : (X => X)",
])
@pytest.mark.parametrize("mode", ["inline", "include"])
def test_completed_thf_model_owns_its_terms_and_conjecture_mode(tmp_path, body, mode):
    declarations = "thf(p_type,type,p:$o).\n"
    fact = f"thf(fact,axiom,({body})).\n"
    goal = f"thf(goal,conjecture,({body})).\n"
    source = declarations + fact + goal
    if mode == "include":
        library = tmp_path / "facts.ax"
        library.write_text(declarations + fact, encoding="utf-8")
        problem = tmp_path / "problem.p"
        problem.write_text("include('facts.ax').\n" + goal, encoding="utf-8")
        result = sp.translate(str(problem), language="tptp")
        # No later operation may depend on the reader or included files.
        library.unlink()
        problem.unlink()
    else:
        result = sp.translate(source=source, language="tptp")
    del source
    gc.collect()
    assert result.ok, [item.message for item in result.diagnostic_items]
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(z3.parse_smt2_string(result.to_smt2()))
    # The premise entails the identical conjecture, including lambda binding.
    assert solver.check() == z3.unsat


def test_include_only_first_order_problem_still_uses_its_own_frontend(tmp_path):
    library = tmp_path / "first_order.ax"
    library.write_text("fof(fact,axiom,p).\nfof(goal,conjecture,p).\n", encoding="utf-8")
    problem = tmp_path / "first_order.p"
    problem.write_text("include('first_order.ax').\n", encoding="utf-8")
    result = sp.translate(str(problem), language="tptp")
    assert result.ok, [item.message for item in result.diagnostic_items]
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(z3.parse_smt2_string(result.to_smt2()))
    assert solver.check() == z3.unsat


def test_encoding_failure_never_publishes_partial_thf_model():
    result = sp.translate(source="thf(x_type,type,x:$int).\nthf(a,axiom,x=x).\n",
                          language="tptp")
    assert not result.ok
    assert any("interpreted arithmetic semantics" in item.message
               for item in result.diagnostic_items)
