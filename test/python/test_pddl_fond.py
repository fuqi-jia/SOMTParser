"""Bounded FOND policies compared with explicit finite-state policy search."""
import itertools
import random
from pathlib import Path

import pytest
import z3
import somtparser as sp


def canonical_noninitial_states(formula, size):
    # State 0 is initial. The other active state/action/rank tuples can be
    # permuted together into signature order without changing any successor,
    # goal, or rank-decrease condition. The active prefix stays a prefix.
    # This preserves policy existence, not every numbered SMT assignment.
    signatures = {}
    pending, visited = list(formula), set()
    while pending:
        term = pending.pop()
        if term.get_id() in visited:
            continue
        visited.add(term.get_id())
        if z3.is_const(term) and z3.is_bv(term):
            name = str(term.decl().name())
            if name.startswith('__fond_state_bits@'):
                signatures[name] = term
        pending.extend(term.children())
    assert set(signatures) == {f'__fond_state_bits@{i}' for i in range(size)}
    return [z3.Implies(z3.Bool(f'__fond_active@{i}'),
                      z3.ULT(signatures[f'__fond_state_bits@{i-1}'],
                             signatures[f'__fond_state_bits@{i}']))
            for i in range(2, size)]


def state_formula(state):
    return '(and ' + ' '.join(name if state & (1 << bit) else f'(not {name})'
                              for bit, name in enumerate(['(p)', '(q)'])) + ')'


def policy_exists(graph, mode, size=4):
    # Enumerate memoryless policies independently of SMT ranks or controller
    # coordinates. Goal 3 is terminal. Every reachable outcome must be retained.
    for choices in itertools.product(range(2), repeat=3):
        seen = {0}
        while True:
            following = seen | {t for s in seen if s != 3 for t in graph[s][choices[s]]}
            if following == seen:
                break
            seen = following
        if len(seen) > size:
            continue
        reaches_goal = {3}
        while True:
            more = reaches_goal | {
                s for s in seen if s != 3 and (
                    graph[s][choices[s]] <= reaches_goal if mode == 'strong'
                    else bool(graph[s][choices[s]] & reaches_goal))}
            if more == reaches_goal:
                break
            reaches_goal = more
        if seen <= reaches_goal:
            return True
    return False


def translate_graph(graph, mode, tmp_path, size=4):
    actions = []
    for state in range(3):
        for action, targets in enumerate(graph[state]):
            outcomes = ' '.join(state_formula(t) for t in sorted(targets))
            actions.append(f'(:action a{state}_{action} :parameters () '
                           f':precondition {state_formula(state)} :effect (oneof {outcomes}))')
    domain = ('(define (domain d) (:requirements :strips :negative-preconditions :non-deterministic) '
              '(:predicates (p) (q)) ' + ' '.join(actions) + ')')
    problem = tmp_path / 'problem.pddl'
    problem.write_text('(define (problem p) (:domain d) (:init) (:goal (and (p) (q))))')
    result = sp.translate(source=domain, data=[str(problem)], language='pddl', profile='bmc',
                          options={'fond_policy': mode, 'policy_size': str(size)})
    assert result.ok, [d.message for d in result.diagnostic_items]
    assert result.report.fidelity.sound and not result.report.fidelity.complete
    assert [b.kind for b in result.report.fidelity.bounds] == [sp.Bound.STRATEGY_SIZE]
    solver = z3.Solver()
    solver.set(timeout=10000)
    formula = z3.parse_smt2_string(result.to_smt2())
    solver.add(formula)
    answer = solver.check()
    assert answer != z3.unknown
    # Exercise the symmetry argument against independent exhaustive policy
    # enumeration in both strong and strong-cyclic modes, with the full formula.
    solver.add(*canonical_noninitial_states(formula, size))
    assert solver.check() == answer
    if answer == z3.sat:
        # Replay the actual target witness on the source transition graph.
        m = solver.model()
        true = lambda name: z3.is_true(m.eval(z3.Bool(name), model_completion=True))
        recovered = {}
        for i in range(size):
            if not true(f'__fond_active@{i}'):
                continue
            state = int(true(f'p@{i}')) + 2 * int(true(f'q@{i}'))
            assert state not in recovered
            if state == 3:
                recovered[state] = None
            else:
                selected = [a for a in range(2) if true(f'do_a{state}_{a}@{i}')]
                assert len(selected) == 1
                recovered[state] = selected[0]
        assert 0 in recovered
        reachable = {0}
        while True:
            successors = {t for s in reachable if s != 3 for t in graph[s][recovered[s]]}
            assert successors <= recovered.keys()
            extended = reachable | successors
            if extended == reachable:
                break
            reachable = extended
        good = {3}
        while True:
            extended = good | {s for s in reachable if s != 3 and (
                graph[s][recovered[s]] <= good if mode == 'strong'
                else bool(graph[s][recovered[s]] & good))}
            if extended == good:
                break
            good = extended
        assert reachable <= good
    return answer == z3.sat


@pytest.mark.parametrize('seed', range(20))
@pytest.mark.parametrize('mode', ['strong', 'strong-cyclic'])
def test_small_policy_graphs_against_exhaustive_search(seed, mode, tmp_path):
    rng = random.Random(seed)
    graph = {s: [set(rng.sample(range(4), rng.randint(1, 3))) for _ in range(2)]
             for s in range(3)}
    assert translate_graph(graph, mode, tmp_path) == policy_exists(graph, mode)


def test_retry_needs_fairness_and_two_states(tmp_path):
    graph = {0: [{0, 3}, {0}], 1: [{1}, {1}], 2: [{2}, {2}]}
    assert translate_graph(graph, 'strong-cyclic', tmp_path, 2)
    assert not translate_graph(graph, 'strong', tmp_path, 2)
    assert not translate_graph(graph, 'strong-cyclic', tmp_path, 1)


def test_one_good_outcome_does_not_hide_a_dead_end(tmp_path):
    graph = {0: [{1, 3}, {0}], 1: [{1}, {1}], 2: [{3}, {3}]}
    assert not translate_graph(graph, 'strong-cyclic', tmp_path)


def test_source_configuration_requires_the_right_kind_of_bound():
    spec = sp.source_semantics('pddl')
    assert spec.decision_bounds[sp.DecisionKind.PLAN_EXISTENCE] == [sp.Bound.PLAN_HORIZON]
    assert spec.decision_bounds[sp.DecisionKind.REACTIVE_REALIZABILITY] == [sp.Bound.STRATEGY_SIZE]


def test_independent_oneof_groups_form_cartesian_outcomes(tmp_path):
    domain = '''(define (domain d)
      (:requirements :strips :negative-preconditions :non-deterministic)
      (:predicates (p) (q))
      (:action toss :parameters () :precondition (and (not (p)) (not (q)))
       :effect (and (oneof (p) (not (p))) (oneof (q) (not (q))))))'''
    problem = tmp_path / 'problem.pddl'
    problem.write_text('(define (problem p) (:domain d) (:init) (:goal (and (p) (q))))')
    result = sp.translate(source=domain, data=[str(problem)], language='pddl', profile='bmc',
                          options={'fond_policy': 'strong-cyclic', 'policy_size': '4'})
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.add(z3.parse_smt2_string(result.to_smt2()))
    # Mixed outcomes are dead ends. Zipping the two oneof groups instead of
    # taking their product incorrectly leaves only retry and success.
    assert solver.check() == z3.unsat


def test_many_actions_remain_exclusive_without_quadratic_constraints(tmp_path):
    problem = tmp_path / 'problem.pddl'
    problem.write_text('(define (problem p) (:domain d) (:init) (:goal (p)))')
    actions = ' '.join(f'(:action a{i} :parameters () :effect (oneof (p) (not (p))))'
                       for i in range(128))
    domain = ('(define (domain d) (:requirements :strips :non-deterministic) '
              '(:predicates (p)) ' + actions + ')')
    result = sp.translate(source=domain, data=[str(problem)], language='pddl', profile='bmc',
                          options={'fond_policy': 'strong-cyclic', 'policy_size': '2'})
    assert result.ok, [d.message for d in result.diagnostic_items]
    assert result.report.stats.num_constraints < 2000
    solver = z3.Solver()
    solver.set(timeout=10000)
    solver.add(z3.parse_smt2_string(result.to_smt2()))
    # A choice at the end remains available, but cannot coexist with one at
    # the beginning. This checks the entire prefix, not just adjacent choices.
    solver.add(z3.Bool('do_a127@0'))
    assert solver.check() == z3.sat
    solver.add(z3.Bool('do_a0@0'))
    assert solver.check() == z3.unsat


def test_state_signature_keeps_an_odd_final_bit(tmp_path):
    domain = '''(define (domain d) (:requirements :strips :non-deterministic)
      (:predicates (p) (q) (r))
      (:action first :parameters () :effect (p))
      (:action second :parameters () :precondition (p) :effect (q))
      (:action third :parameters () :precondition (q) :effect (r)))'''
    problem = tmp_path / 'problem.pddl'
    problem.write_text('(define (problem p) (:domain d) (:init) (:goal (r)))')
    for size, expected in [(3, z3.unsat), (4, z3.sat)]:
        result = sp.translate(source=domain, data=[str(problem)], language='pddl', profile='bmc',
                              options={'fond_policy': 'strong', 'policy_size': str(size)})
        assert result.ok, [d.message for d in result.diagnostic_items]
        solver = z3.Solver()
        solver.add(z3.parse_smt2_string(result.to_smt2()))
        assert solver.check() == expected


def test_upstream_acrobatics_policy_replays_in_source_states():
    root = Path(__file__).resolve().parents[2] / 'languages/pddl/instances/upstream'
    result = sp.translate(str(root / 'acrobatics_domain.pddl'),
                          data=[str(root / 'acrobatics_p01.pddl')],
                          language='pddl', profile='bmc',
                          options={'fond_policy': 'strong-cyclic', 'policy_size': '6'})
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.set(timeout=10000)
    solver.add(z3.parse_smt2_string(result.to_smt2()))
    assert solver.check() == z3.sat
    model = solver.model()
    true = lambda name: z3.is_true(model.eval(z3.Bool(name), model_completion=True))
    # Independent source progression for the vendored two-location instance.
    # Static relations are decoded too, so an invented edge/ladder cannot
    # conceal an invalid policy. No target ranks or packed vectors are used.
    vocabulary = [('up',), ('broken-leg',)]
    vocabulary += [(p, x) for p in ('position', 'ladder-at') for x in ('p0', 'p1')]
    vocabulary += [(p, x, y) for p in ('next-fwd', 'next-bwd')
                   for x in ('p0', 'p1') for y in ('p0', 'p1')]
    states = {}
    actions = {}
    for node in range(6):
        if not true(f'__fond_active@{node}'):
            continue
        state = frozenset(atom for atom in vocabulary if true('_'.join(atom) + f'@{node}'))
        assert state not in states
        states[state] = node
        selected = [d.name()[3:-(len(str(node)) + 1)] for d in model.decls()
                    if d.name().startswith('do_') and d.name().endswith(f'@{node}')
                    and true(d.name())]
        goal = ('up',) in state and ('position', 'p1') in state
        assert len(selected) == (0 if goal else 1)
        if selected:
            actions[state] = selected[0].split('_')
    initial = frozenset({('next-fwd', 'p0', 'p1'), ('next-bwd', 'p1', 'p0'),
                         ('ladder-at', 'p0'), ('position', 'p0')})
    assert states[initial] == 0
    reached = {initial}
    edges = {}
    pending = [initial]
    while pending:
        state = pending.pop()
        if ('up',) in state and ('position', 'p1') in state:
            edges[state] = set()
            continue
        assert ('broken-leg',) not in state
        action, *args = actions[state]
        if action == 'climb':
            p, = args
            assert ('up',) not in state and ('position', p) in state and ('ladder-at', p) in state
            successors = {state | {('up',)}}
        elif action == 'climb-down':
            assert not args and ('up',) in state
            successors = {state - {('up',)}}
        else:
            assert action in ('walk-left', 'walk-right', 'walk-on-beam')
            p, q = args
            assert ('position', p) in state
            relation = 'next-bwd' if action == 'walk-left' else 'next-fwd'
            assert (relation, p, q) in state
            assert (('up',) in state) == (action == 'walk-on-beam')
            moved = (state - {('position', p)}) | {('position', q)}
            successors = {moved, moved - {('up',)}} if action == 'walk-on-beam' else {moved}
        assert successors <= states.keys()
        edges[state] = successors
        for successor in successors - reached:
            reached.add(successor)
            pending.append(successor)
    good = {s for s in reached if ('up',) in s and ('position', 'p1') in s}
    while True:
        extended = good | {s for s in reached if edges[s] & good}
        if extended == good:
            break
        good = extended
    assert good == reached


def test_upstream_beam_walk_needs_eight_policy_states():
    root = Path(__file__).resolve().parents[2] / 'languages/pddl/instances/upstream'
    # To reach the fourth location on the beam the policy must cover both
    # up/down states at all four locations: each forward step can cause a fall,
    # and the sole ladder is at p0. The source therefore needs eight states.
    for size, expected in [(7, z3.unsat), (8, z3.sat)]:
        result = sp.translate(str(root / 'beam-walk_domain.pddl'),
                              data=[str(root / 'beam-walk_p01.pddl')],
                              language='pddl', profile='bmc',
                              options={'fond_policy': 'strong-cyclic', 'policy_size': str(size)})
        assert result.ok, [d.message for d in result.diagnostic_items]
        solver = z3.Solver()
        solver.set(timeout=10000)
        formula = z3.parse_smt2_string(result.to_smt2())
        solver.add(formula)
        if size == 7:
            solver.add(*canonical_noninitial_states(formula, size))
        else:
            # Supply a complete source-state policy witness instead of asking
            # the solver to discover its arbitrary node numbering. All target
            # constraints remain present, including every action outcome.
            locations = tuple(f'p{i}' for i in range(4))
            states = [(p, up) for p in locations for up in (False, True)]
            static = {('ladder-at', 'p0')}
            static |= {('next-fwd', locations[i], locations[i+1]) for i in range(3)}
            static |= {('next-bwd', locations[i+1], locations[i]) for i in range(3)}
            vocabulary = [('up',)]
            vocabulary += [(p, x) for p in ('position', 'ladder-at') for x in locations]
            vocabulary += [(p, x, y) for p in ('next-fwd', 'next-bwd')
                           for x in locations for y in locations]
            edges = {}
            for node, (position, up) in enumerate(states):
                facts = static | {('position', position)} | ({('up',)} if up else set())
                solver.add(z3.Bool(f'__fond_active@{node}'))
                for atom in vocabulary:
                    solver.add(z3.Bool('_'.join(atom) + f'@{node}') == (atom in facts))
                index = locations.index(position)
                if up and index == 3:
                    edges[node] = set()
                    continue
                if up:
                    action = f'walk-on-beam_{position}_{locations[index+1]}'
                    successors = {(locations[index+1], False), (locations[index+1], True)}
                elif index == 0:
                    action, successors = 'climb_p0', {('p0', True)}
                else:
                    action = f'walk_{position}_{locations[index-1]}'
                    successors = {(locations[index-1], False)}
                edges[node] = {states.index(successor) for successor in successors}
                solver.add(z3.Bool(f'do_{action}@{node}'))
            # Source-level closure and fair progress do not inspect target
            # ranks or signatures. Every reachable outcome has a path to goal.
            reached = {0}
            while True:
                more = reached | {t for s in reached for t in edges[s]}
                if more == reached:
                    break
                reached = more
            good = {states.index(('p3', True))}
            while True:
                more = good | {s for s in reached if edges[s] & good}
                if more == good:
                    break
                good = more
            assert reached == good == set(range(8))
        assert solver.check() == expected
