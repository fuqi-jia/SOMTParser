"""Independent evaluator and source-witness checks for wide grammar alternatives."""

import pytest
import somtparser as sp
import z3


def numeral(value):
    return f"(- {-value})" if value < 0 else str(value)


@pytest.mark.parametrize("expected", [-16, -8, -1, 0, 1, 8, 16, 17])
def test_wide_alternatives_preserve_values_and_source_witnesses(expected):
    # An odd number of alternatives exercises both unequal subtrees. Include
    # duplicate productions: they denote the same source value but remain
    # separate derivations. No alternative is a wildcard/default production.
    values = list(range(-16, 17)) + [-8, 8]
    rules = " ".join(map(str, values))
    source = ("(set-logic LIA) "
              f"(synth-fun f () Int ((Start Int ({rules})))) "
              f"(constraint (= f {numeral(expected)})) (check-synth)")
    translated = sp.translate(source=source, language="sygus", profile="bmc",
                              options={"grammar_mode": "unbounded"})
    assert translated.ok, [d.message for d in translated.diagnostic_items]
    target = translated.to_smt2(sp.OmtDialect.Z3)
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.set(timeout=5000)
    solver.add(z3.parse_smt2_string(target, ctx=context))
    status = solver.check()
    assert status == (z3.sat if expected in values else z3.unsat)
    if status == z3.sat:
        witness = solver.model().eval(
            z3.String("__somt_sygus_witness_text_0", ctx=context),
            model_completion=True)
        assert z3.is_string_value(witness)
        # The renderer is checked independently of the target evaluator by
        # reparsing the projected source expression in a fresh SMT context.
        source_context = z3.Context()
        source_solver = z3.Solver(ctx=source_context)
        source_solver.add(z3.parse_smt2_string(
            f"(assert (not (= {witness.as_string()} {numeral(expected)})))",
            ctx=source_context))
        assert source_solver.check() == z3.unsat
