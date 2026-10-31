"""Infinite TLSF game decisions against a separate explicit Buchi oracle."""
import hashlib
import itertools
from pathlib import Path

import pytest
import somtparser as sp
import z3


def translate(body, semantics='Mealy'):
    source = f'INFO {{ SEMANTICS: {semantics} TARGET: {semantics} }} MAIN {{ {body} }}'
    result = sp.translate(source=source, language='syntcomp')
    assert result.ok, [d.message for d in result.diagnostic_items]
    assert not result.report.fidelity.bounds
    solver = z3.Solver()
    solver.set(timeout=10000)
    solver.add(z3.parse_smt2_string(result.to_smt2()))
    answer = solver.check()
    assert answer != z3.unknown, solver.reason_unknown()
    return result, answer == z3.sat


def explicit_game(mealy, initial, preset, assumption, guarantee, input_count=1):
    # Independent monitor: store the previous complete letter and two failed
    # bits. Check every adjacent pair directly, with no formula derivatives.
    first, won, lost = ('initial',), ('won',), ('lost',)
    inputs = list(itertools.product((False, True), repeat=input_count))
    letters = [(i, o) for i in inputs for o in (False, True)]

    def successor(state, letter):
        if state in (won, lost):
            return state
        if state == first:
            return won if not initial(letter) else lost if not preset(letter) else (letter, False, False)
        previous, bad_a, bad_b = state
        return (letter, bad_a or not assumption(previous, letter),
                bad_b or not guarantee(previous, letter))

    states, edges = [first], {}
    for state in states:
        edges[state] = {letter:successor(state, letter) for letter in letters}
        for target in edges[state].values():
            if target not in states:
                states.append(target)
    accepting = {s for s in states if s == won or s == first
                 or s != lost and (s[1] or not s[2])}

    def predecessor(region):
        if mealy:
            return {s for s in states if all(any(edges[s][i,o] in region for o in (False, True)) for i in inputs)}
        return {s for s in states if any(all(edges[s][i,o] in region for i in inputs) for o in (False, True))}

    outer = set(states)
    while True:
        inner = set()
        goal = accepting & predecessor(outer)
        while True:
            next_inner = goal | predecessor(inner)
            if next_inner == inner:
                break
            inner = next_inner
        if inner == outer:
            return first in outer
        outer = inner


@pytest.mark.parametrize('semantics', ['Mealy', 'Moore'])
@pytest.mark.parametrize('body,predicate,mealy,moore', [
    ('G (X o <-> i)', lambda old,new: new[1] == old[0][0], True, True),
    ('G (o <-> X i)', lambda old,new: old[1] == new[0][0], False, False),
    ('G (X o <-> X i)', lambda old,new: new[1] == new[0][0], True, False),
    ('G (X o <-> !o)', lambda old,new: new[1] != old[1], True, True),
])
def test_next_games_match_independent_full_game(semantics, body, predicate, mealy, moore):
    result, answer = translate(f'INPUTS {{ i; }} OUTPUTS {{ o; }} GUARANTEE {{ {body}; }}', semantics)
    expected = explicit_game(semantics == 'Mealy', lambda _:True, lambda _:True,
                             lambda _a,_b:True, predicate)
    assert answer == expected == (mealy if semantics == 'Mealy' else moore)
    assert '__somt_syntcomp_buchi_' in result.to_smt2()


@pytest.mark.parametrize('semantics', ['Mealy', 'Moore'])
def test_later_assumption_failure_rescues_prior_guarantee_failure(semantics):
    # At t=0, PRESET forces o and ASSERT fails. A later o=false rescues the
    # standard whole-trace implication. Strict implication would reject t=0.
    body = 'INPUTS { i; } OUTPUTS { o; } PRESET { o; } REQUIRE { o; } ASSERT { false; }'
    _, answer = translate(body, semantics)
    assert answer
    assert explicit_game(semantics == 'Mealy', lambda _:True, lambda x:x[1],
                         lambda old,_new:old[1], lambda _old,_new:False)
    strict = f'INFO {{ SEMANTICS: {semantics},Strict TARGET: {semantics} }} MAIN {{ {body} }}'
    result = sp.translate(source=strict, language='syntcomp')
    assert not result.ok


def test_environment_may_keep_assumption_forever_so_failure_is_not_vacuous():
    _, answer = translate('INPUTS { i; } OUTPUTS { o; } INITIALLY { i; } REQUIRE { i; } ASSERT { false; }')
    assert not answer


@pytest.mark.parametrize('initial,preset,assume,expected', [
    ('true', 'false', 'G false', False),
    ('false', 'false', 'G true', True),
    ('true', 'true', 'G false', True),
])
def test_initial_obligation_is_independent_of_safety_assumption(initial, preset, assume, expected):
    _, answer = translate(f'INPUTS {{ }} OUTPUTS {{ }} INITIALLY {{ {initial}; }} PRESET {{ {preset}; }} '
                          f'ASSUME {{ {assume}; }} ASSERT {{ false; }}')
    assert answer == expected


@pytest.mark.parametrize('semantics,expected', [('Mealy', True), ('Moore', False)])
def test_initial_output_choice_obeys_the_same_causality_order(semantics, expected):
    _, answer = translate('INPUTS { i; } OUTPUTS { o; } PRESET { o <-> i; } ASSERT { X true; }', semantics)
    assert answer == expected


def test_accepting_states_cannot_terminate_an_infinite_game():
    # A length-one finite trace can ignore weak-next false. Infinite semantics
    # must continue and therefore rejects every controller.
    _, answer = translate('INPUTS { } OUTPUTS { } ASSERT { X false; }')
    assert not answer


def test_symbolic_input_alphabet_does_not_have_a_sixteen_input_cutoff():
    inputs = ' '.join(f'i{k};' for k in range(17))
    # No output arrays are needed for this genuinely input-dependent losing
    # game, so the test isolates alphabet support from strategy-solving cost.
    _, answer = translate(f'INPUTS {{ {inputs} }} OUTPUTS {{ }} ASSERT {{ X i16; }}')
    assert not answer


@pytest.mark.parametrize('semantics', ['Mealy', 'Moore'])
@pytest.mark.parametrize('body,predicate,expected', [
    ('G (X o <-> i)', lambda old,new: new[1] == old[0][0], True),
    ('G (X i <-> o)', lambda old,new: new[0][0] == old[1], False),
])
def test_next_assumption_violation_is_a_game_obligation(semantics, body, predicate, expected):
    # An output-controlled next obligation can be violated deliberately; an
    # input-controlled next obligation can be maintained by the environment.
    _, answer = translate(f'INPUTS {{ i; }} OUTPUTS {{ o; }} ASSUME {{ {body}; }} ASSERT {{ false; }}', semantics)
    assert answer == expected
    assert explicit_game(semantics == 'Mealy', lambda _:True, lambda _:True,
                         predicate, lambda _a,_b:False) == expected


def test_original_official_amba_shift_is_unchanged_and_realizable():
    path = Path(__file__).parents[2]/'languages/syntcomp/instances/ok/amba_decomposed_shift.tlsf'
    raw = path.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == '54bc4453f8b1b41e652f7078f7a70494565c4679b19a8228f2dc85b668c1f22b'
    result = sp.translate(source=raw.decode(), language='syntcomp')
    assert result.ok, [d.message for d in result.diagnostic_items]
    text = result.to_smt2()
    parser = sp.Parser()
    parser.parse_string(text)
    assert parser.assertions
    # The full suite creates many expressions in Z3's global context. Keep this
    # quantified strategy check independent of its prior allocation history.
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.set(timeout=10000)
    solver.add(z3.parse_smt2_string(text, ctx=context))
    answer = solver.check()
    assert answer == z3.sat, solver.reason_unknown() if answer == z3.unknown else str(answer)
    assert explicit_game(True, lambda _:True, lambda _:True, lambda _a,_b:True,
        lambda old,new:new[1] == (old[0][1] if old[0][0] else old[1]), input_count=2)
    assert not result.report.fidelity.bounds


@pytest.mark.parametrize('section', [
    'ASSERT { X X o; }', 'GUARANTEE { F o; }',
    'ASSERT { X[!] o; }', 'INITIALLY { X i; }',
    'GUARANTEE { !(G (X o)); }',
    'GUARANTEE { G (X o) || G (X !o); }',
])
def test_other_infinite_temporal_fragments_are_explicitly_refused(section):
    source = ('INFO { SEMANTICS: Mealy TARGET: Mealy } '
              'MAIN { INPUTS { i; } OUTPUTS { o; } '+section+' }')
    result = sp.translate(source=source, language='syntcomp')
    assert not result.ok


@pytest.mark.parametrize('semantics', ['Mealy', 'Moore'])
@pytest.mark.parametrize('section,expected', [('ASSUME', True), ('GUARANTEE', False)])
def test_conjoined_global_clauses_match_separate_statements(semantics, section, expected):
    clauses = ['G (X o <-> i)', 'G (X o <-> !o)']
    suffix = 'ASSERT { false; }' if section == 'ASSUME' else ''
    body = 'INPUTS { i; } OUTPUTS { o; } '+section+' { %s } '+suffix
    joined, joined_answer = translate(body % (' && '.join(clauses)+';'), semantics)
    separate, separate_answer = translate(body % ('; '.join(clauses)+';'), semantics)
    assert joined_answer == separate_answer == expected
    assert '__somt_syntcomp_buchi_' in joined.to_smt2()
    assert '__somt_syntcomp_buchi_' in separate.to_smt2()
