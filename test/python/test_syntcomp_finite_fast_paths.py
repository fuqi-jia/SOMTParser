import z3

import somtparser as sp


def _info(semantics, title):
    return (f'INFO {{ TITLE: "{title}" SEMANTICS: Finite,{semantics} '
            f'TARGET: {semantics} }}')


def _translate(source):
    result = sp.translate(source=source, language="syntcomp")
    assert result.ok, [diagnostic.message for diagnostic in result.diagnostic_items]
    return result


def _check(source):
    result = _translate(source)
    script = result.to_smt2()
    parser = sp.Parser()
    parser.parse_string(script)
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(z3.parse_smt2_string(script))
    return result, solver.check(), script


def _strategies(result):
    return {choice.strategy for choice in result.report.choices}


def test_unrestricted_input_invariant_uses_exact_unrealizable_shortcut():
    outputs = [f"o{k}" for k in range(1, 14)]
    declarations = " ".join(name + ";" for name in outputs)
    goals = " && ".join("F(" + name + ")" for name in outputs)
    source = f'''{_info("Moore", "unavoidable input invariant")}
MAIN {{ INPUTS {{ i; }} OUTPUTS {{ {declarations} }}
GUARANTEES {{ G(i) && {goals}; }} }}'''

    result, status, script = _check(source)
    assert status == z3.unsat
    assert "finite-unavoidable-environment-invariant" in _strategies(result)
    assert len(script.encode()) < 64_000


def test_one_position_moore_witness_handles_thirteen_eventualities():
    outputs = [f"o{k}" for k in range(1, 14)]
    declarations = " ".join(name + ";" for name in outputs)
    goals = " && ".join("F(" + name + ")" for name in outputs)
    source = f'''{_info("Moore", "one position witness")}
MAIN {{ INPUTS {{ i; }} OUTPUTS {{ {declarations} }}
ASSUMPTIONS {{ G(i); }} GUARANTEES {{ G(i) && {goals}; }} }}'''

    result, status, script = _check(source)
    assert status == z3.sat
    assert "finite-one-step-game-witness" in _strategies(result)
    assert len(script.encode()) < 64_000


def test_environment_assumption_disables_unconditional_input_shortcut():
    source = f'''{_info("Moore", "restricted environment")}
MAIN {{ INPUTS {{ i; }} OUTPUTS {{ o; }}
ASSUMPTIONS {{ G(i); }} GUARANTEES {{ G(i) && X[!] o; }} }}'''

    result, status, _ = _check(source)
    assert status == z3.sat
    strategies = _strategies(result)
    assert "finite-unavoidable-environment-invariant" not in strategies
    assert "finite-ltlf-symbolic-dfa-reachability-game" in strategies


def test_current_input_copy_distinguishes_mealy_from_moore():
    for semantics, expected in (("Mealy", z3.sat), ("Moore", z3.unsat)):
        source = f'''{_info(semantics, semantics + " current input")}
MAIN {{ INPUTS {{ i; }} OUTPUTS {{ o; }}
GUARANTEES {{ (i <-> o) && X[!] true; }} }}'''
        result, status, _ = _check(source)
        assert status == expected
        assert "finite-ltlf-symbolic-dfa-reachability-game" in _strategies(result)


def test_strong_next_requires_a_nonempty_continuation():
    impossible = f'''{_info("Moore", "strong next false")}
MAIN {{ GUARANTEES {{ X[!] false; }} }}'''
    eventual = f'''{_info("Moore", "strong next output")}
MAIN {{ OUTPUTS {{ o; }} GUARANTEES {{ X[!] o; }} }}'''

    impossible_result, impossible_status, _ = _check(impossible)
    eventual_result, eventual_status, _ = _check(eventual)
    assert impossible_status == z3.unsat
    assert eventual_status == z3.sat
    assert "finite-ltlf-symbolic-dfa-reachability-game" in _strategies(impossible_result)
    assert "finite-ltlf-symbolic-dfa-reachability-game" in _strategies(eventual_result)


def test_wide_transition_choice_is_a_flat_nary_disjunction():
    outputs = [f"b{k}" for k in range(1, 7)]
    declarations = " ".join(name + ";" for name in outputs)
    goals = " && ".join("F(" + name + ")" for name in outputs)
    source = f'''{_info("Moore", "wide successor disjunction")}
MAIN {{ OUTPUTS {{ {declarations} }} GUARANTEES {{ X[!] true && {goals}; }} }}'''

    result, status, script = _check(source)
    assert status == z3.sat
    assert "finite-ltlf-symbolic-dfa-reachability-game" in _strategies(result)

    parsed = z3.parse_smt2_string(script)
    pending = list(parsed)
    seen = set()
    maximum_or_arity = 0
    while pending:
        node = pending.pop()
        if not z3.is_expr(node) or node.get_id() in seen:
            continue
        seen.add(node.get_id())
        if z3.is_quantifier(node):
            pending.append(node.body())
        elif z3.is_app(node):
            if node.decl().kind() == z3.Z3_OP_OR:
                maximum_or_arity = max(maximum_or_arity, node.num_args())
            pending.extend(node.children())
    assert maximum_or_arity >= 16
