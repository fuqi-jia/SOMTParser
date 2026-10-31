"""Shared latch equations preserve the complete bounded transition relation."""
import pytest
import z3

import somtparser as sp


@pytest.mark.parametrize("depth", [0, 1, 3])
def test_shared_fanin_preserves_every_frame_and_literal_polarity(depth):
    # Two unconstrained initial latches sample opposite polarities of one AND.
    # Constant-true output isolates the transition relation from reachability.
    source = "aag 5 2 2 1 1\n2\n4\n6 10 6\n8 11 8\n1\n10 2 4\n"
    result = sp.translate(source=source, language="aiger", profile="bmc",
                          options={"bmc_depth": str(depth)})
    assert result.ok, [item.message for item in result.diagnostic_items]
    context = z3.Context()
    assertions = z3.parse_smt2_string(result.to_smt2(), ctx=context)
    actual = z3.And(*assertions) if len(assertions) else z3.BoolVal(True, ctx=context)
    expected = z3.BoolVal(True, ctx=context)
    for step in range(depth):
        signal = z3.And(z3.Bool(f"v1@{step}", ctx=context),
                        z3.Bool(f"v2@{step}", ctx=context))
        expected = z3.And(expected,
                          z3.Bool(f"v3@{step + 1}", ctx=context) == signal,
                          z3.Bool(f"v4@{step + 1}", ctx=context) == z3.Not(signal))
    solver = z3.Solver(ctx=context)
    solver.set(timeout=10000)
    solver.add(z3.Xor(actual, expected))
    assert solver.check() == z3.unsat


def test_many_latches_export_shared_fanin_once():
    inputs, latches = 8, 512
    gates = inputs - 1
    maximum = inputs + latches + gates
    source = [f"aag {maximum} {inputs} {latches} 1 {gates}"]
    source += [str(2 * i) for i in range(1, inputs + 1)]
    source += [f"{2 * (inputs + i)} {2 * maximum} 0"
               for i in range(1, latches + 1)]
    source.append("1")
    previous = 2
    for index in range(gates):
        gate = 2 * (inputs + latches + index + 1)
        source.append(f"{gate} {previous} {2 * (index + 2)}")
        previous = gate
    result = sp.translate(source="\n".join(source) + "\n", language="aiger",
                          profile="bmc", options={"bmc_depth": "1"})
    assert result.ok, [item.message for item in result.diagnostic_items]
    target = result.to_smt2()
    # The repeated eight-input expression is emitted once in a lexical let.
    assert "(let (" in target
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.set(timeout=10000)
    solver.add(z3.parse_smt2_string(target, ctx=context))
    next_latches = [z3.Bool(f"v{inputs + i}@1", ctx=context)
                    for i in range(1, latches + 1)]
    for false_input in [-1, *range(inputs)]:
        solver.push()
        solver.add(*[z3.Bool(f"v{i + 1}@0", ctx=context) == (i != false_input)
                     for i in range(inputs)])
        assert solver.check() == z3.sat
        expected = false_input == -1
        solver.add(z3.Or(*[latch != expected for latch in next_latches]))
        assert solver.check() == z3.unsat
        solver.pop()
