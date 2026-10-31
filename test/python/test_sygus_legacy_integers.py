"""SyGuS 1.0 signed tokens desugar without changing scope or grammar depth."""
import pytest
import somtparser as sp
import z3


def verdict(source):
    result = sp.translate(source=source, language="sygus", profile="bmc",
                          options={"grammar_depth": "0"})
    assert result.ok, [d.message for d in result.diagnostic_items]
    assert result.report.fidelity.sound
    assert not result.report.fidelity.complete
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(z3.parse_smt2_string(result.to_smt2()))
    return solver.check()


def numeral(value):
    return f"(- {-value})" if value < 0 else str(value)


@pytest.mark.parametrize("literal", ["-1", "-18446744073709551617", "-0"])
@pytest.mark.parametrize("delta", [0, 1])
def test_signed_grammar_terminal_preserves_arbitrary_precision_at_depth_zero(literal, delta):
    source = ('(set-logic LIA) '
              f'(synth-fun f ((x Int)) Int ((Start Int ({literal})))) '
              f'(constraint (= (f 0) {numeral(int(literal) + delta)})) '
              '(check-synth)')
    assert verdict(source) == (z3.sat if delta == 0 else z3.unsat)


@pytest.mark.parametrize("body", [
    '(+ x -1)', '(let ((offset Int -1)) (+ x offset))',
])
@pytest.mark.parametrize("offset", [1, 2])
def test_signed_tokens_in_helpers_typed_let_and_universal_constraints(body, offset):
    source = ('(set-logic LIA) '
              f'(define-fun dec ((x Int)) Int {body}) '
              '(synth-fun f ((x Int)) Int ((Start Int ((dec x))))) '
              '(declare-var x Int) '
              f'(constraint (= (f x) (+ x -{offset}))) (check-synth)')
    assert verdict(source) == (z3.sat if offset == 1 else z3.unsat)


@pytest.mark.parametrize("parameter,nonterminal", [("-1", "Start"), ("x", "-1")])
def test_declared_signed_spelling_is_a_symbol_in_its_scope(parameter, nonterminal):
    source = ('(set-logic LIA) '
              f'(synth-fun f (({parameter} Int)) Int '
              f'(({nonterminal} Int ({parameter})))) '
              '(declare-var u Int) (constraint (= (f u) u)) (check-synth)')
    assert verdict(source) == z3.sat
