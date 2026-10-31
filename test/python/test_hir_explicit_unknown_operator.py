"""A source-declared unknown operator is a finite decision, not ambiguity."""
import pytest

import somtparser as sp
from somtparser import natural_language
from somtparser.hir import build_hir

z3 = pytest.importorskip("z3")

SOURCE = (
    "A two-cell KenKen cage has target {target}. The operation symbols +, -, x and / are omitted, "
    "thus leaving the operation as another unknown to be determined. Each cell is an integer from 1 through 6. "
    "Either operand order is allowed for subtraction or division; division must be exact."
)


def var(name):
    return {"var": name}


def lit(value):
    return {"literal": value, "sort": "Int"}


def compare(op, lhs, rhs):
    return {"op": op, "args": [lhs, rhs]}


def cage_choice_model(target, source):
    a, b = var("a"), var("b")
    alternatives = [
        compare("eq", {"op": "add", "args": [a, b]}, lit(target)),
        {"op": "or", "args": [
            compare("eq", {"op": "sub", "args": [a, b]}, lit(target)),
            compare("eq", {"op": "sub", "args": [b, a]}, lit(target)),
        ]},
        compare("eq", {"op": "mul", "args": [a, b]}, lit(target)),
        {"op": "or", "args": [
            compare("eq", a, {"op": "mul", "args": [lit(target), b]}),
            compare("eq", b, {"op": "mul", "args": [lit(target), a]}),
        ]},
    ]
    return {
        "schema": "somt-hir-model-v1",
        "language": "hir",
        "decision": "satisfiability",
        "declarations": [
            {"name": "a", "sort": "Int", "lower": 1, "upper": 6},
            {"name": "b", "sort": "Int", "lower": 1, "upper": 6},
        ],
        "functions": [],
        "constraints": [{"expr": {"op": "or", "args": alternatives},
                         "span": [0, len(source)]}],
        "objectives": [],
        "objective_order": "single",
        "goal": None,
        "assumptions": [],
        "unresolved": [],
    }


@pytest.mark.parametrize("target,positive,negative", [
    (11, (5, 6), (1, 2)),  # Addition only.
    (6, (2, 3), (1, 2)),   # Multiplication only.
    (2, (6, 3), (4, 3)),   # Exact division only.
    (2, (3, 6), (3, 4)),   # Reversed exact division.
    (2, (5, 3), (4, 3)),   # Subtraction only.
    (2, (3, 5), (3, 4)),   # Reversed subtraction.
])
def test_explicit_unknown_operation_uses_provider_path_and_finite_disjunction(target, positive, negative):
    source = SOURCE.format(target=target)
    captured = {}

    def provider(request):
        captured.update(request)
        return cage_choice_model(target, source)

    candidate = sp.propose_nl(source, language="hir", provider=provider)
    assert candidate.valid, candidate.diagnostics
    assert candidate.model["unresolved"] == []
    assert captured["source"] == source
    assert captured["instruction"].endswith(natural_language._SOURCE_RELATION_GUIDANCE)
    translated = build_hir(candidate.model, source).translate()
    assert translated.ok, [d.message for d in translated.diagnostic_items]

    context = z3.Context()
    formula = z3.And(*z3.parse_smt2_string(translated.to_smt2(), ctx=context))
    a, b = z3.Int("a", ctx=context), z3.Int("b", ctx=context)

    def possible(left, right):
        solver = z3.Solver(ctx=context)
        solver.set(timeout=5000)
        solver.add(formula, a == left, b == right)
        result = solver.check()
        assert result != z3.unknown, solver.reason_unknown()
        return result == z3.sat

    assert possible(*positive)
    assert not possible(*negative)
