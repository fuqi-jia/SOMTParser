"""Independent trace progression checks for the shared deterministic encoder."""
from itertools import combinations, product

import pytest
import somtparser as sp
import z3


DOMAIN = """(define (domain d) (:requirements :adl)
(:predicates (p) (q) (r))
(:action a :precondition (not (q))
 :effect (and (p) (when (q) (r)) (when (p) (not (p)))))
(:action b :precondition (p)
 :effect (and (not (p)) (q) (when (p) (r)) (when (r) (not (q)))))
(:action c :effect (and (not (q)) (when (r) (not (p))) (when (not (r)) (p)))))"""


def encode(tmp_path, domain, initial='', horizon=2):
    path = tmp_path / 'problem.pddl'
    path.write_text('(define (problem p) (:domain d) (:init ' + initial + ') (:goal (and)))')
    result = sp.translate(source=domain, data=[str(path)], language='pddl', profile='bmc',
                          options={'plan_horizon': str(horizon)})
    assert result.ok, [d.message for d in result.diagnostic_items]
    solver = z3.Solver()
    solver.set(timeout=10000)
    solver.add(z3.parse_smt2_string(result.to_smt2()))
    return result, solver


def progress(state, action):
    # All conditions read the old source state. Adds take precedence.
    if action == 'noop':
        return state
    if action == 'a':
        if 'q' in state:
            return None
        adds = {'p'} | ({'r'} if 'q' in state else set())
        deletes = {'p'} if 'p' in state else set()
    elif action == 'b':
        if 'p' not in state:
            return None
        adds = {'q'} | ({'r'} if 'p' in state else set())
        deletes = {'p'} | ({'q'} if 'r' in state else set())
    else:
        adds = {'p'} if 'r' not in state else set()
        deletes = {'q'} | ({'p'} if 'r' in state else set())
    return (state - deletes) | adds


def selected(result, action, step):
    name = f'__pddl_noop@{step}' if action == 'noop' else f'do_{action}@{step}'
    # An omitted source action was proved unreachable within the bound. Do
    # not create an unconstrained solver symbol for such an absent choice.
    return z3.Bool(name) if result.parser.is_declared_variable(name) else z3.BoolVal(False)


@pytest.mark.parametrize('bits', list(product([False, True], repeat=3)))
def test_all_short_traces_match_source_progression(tmp_path, bits):
    initial = {p for p, value in zip('pqr', bits) if value}
    result, solver = encode(tmp_path, DOMAIN, ' '.join(f'({p})' for p in initial))
    for trace in product(['a', 'b', 'c', 'noop'], repeat=2):
        states = [initial]
        padded = False
        for action in trace:
            next_state = None if padded and action != 'noop' else progress(states[-1], action)
            if next_state is None:
                break
            states.append(next_state)
            padded |= action == 'noop'
        valid = len(states) == 3
        solver.push()
        solver.add(*[selected(result, action, step) for step, action in enumerate(trace)])
        assert solver.check() == (z3.sat if valid else z3.unsat), (initial, trace)
        if valid:
            # No intermediate or final fluent may differ from the source trace.
            mismatches = [z3.Bool(f'{atom}@{step}') != (atom in state)
                          for step, state in enumerate(states) for atom in 'pqr']
            solver.add(z3.Or(*mismatches))
            assert solver.check() == z3.unsat, (initial, trace)
        solver.pop()


def test_selection_excludes_zero_and_multiple_actions(tmp_path):
    result, solver = encode(tmp_path, DOMAIN, '(p)', horizon=1)
    choices = [selected(result, action, 0) for action in ['a', 'b', 'c', 'noop']]
    solver.push()
    solver.add(*[z3.Not(choice) for choice in choices])
    assert solver.check() == z3.unsat
    solver.pop()
    for a, b in combinations(choices, 2):
        solver.push()
        solver.add(a, b)
        assert solver.check() == z3.unsat
        solver.pop()


def test_sparse_updates_do_not_construct_action_fluent_product(tmp_path):
    count = 512
    objects = ' '.join(f'c{i}' for i in range(count))
    domain = ('(define (domain d) (:requirements :strips) '
              f'(:constants {objects}) (:predicates (p ?x)) '
              '(:action act :parameters (?x) :effect (p ?x)))')
    result, solver = encode(tmp_path, domain, horizon=1)
    assert len(result.parser.assertions) < 20 * count
    solver.add(z3.Bool('do_act_c17@0'))
    assert solver.check() == z3.sat
    model = solver.model()
    assert all(z3.is_true(model.eval(z3.Bool(f'p_c{i}@1'))) == (i == 17)
               for i in range(count))
