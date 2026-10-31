"""Exact public-target relations on explicit source schedules and trajectories.

The polynomial curves below are mathematical *test inputs*, not a frontend
restriction or a solution procedure for arbitrary ODEs. We substitute each
entire function into the original epsilon/delta target, project administrative
constants, and compare every source pre/post state and the signed objective.
No time sampling, float tolerance, target-derived expected values or timeout.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json
import re
import sys
import time as clock
import z3
from z3.z3util import get_vars

ROOT = Path(sys.argv[1])

def value(coefficients, elapsed):
    result = Q(0)
    for coefficient in reversed(coefficients):
        result = result * elapsed + Q(coefficient)
    return result


def state(x=0, y=0, p=False, done=False):
    return {'(x)': None if x is None else Q(x), '(y)': None if y is None else Q(y),
            '(p)': p, '(done)': done, '(d)': x is not None and Q(x) > 0}


def reference(name):
    """Independently tabulated source trajectories and happening updates.

    Each case's derivative/invariant reasoning is explicit below. All source
    coordinates are determined, including undefined value totalization and
    inactive happening padding. Production HIR helpers are not imported.
    """
    horizon = 0 if name == 'empty' else 2 if name in ('overlap', 'internal_jump', 'internal_pre_spike', 'internal_post_spike') else 1
    schedules = [] if not horizon else [('a', Q(1), Q(3))]
    duration = Q(2)
    if name in ('interior_violation', 'history_false'):
        duration = Q(1); schedules = [('a', Q(1), Q(2))]
    if name == 'zero_duration':
        duration = Q(0); schedules = [('a', Q(1), Q(1))]
    if name == 'overlap':
        schedules.append(('b', Q(2), Q(4)))
    if name in ('internal_jump', 'internal_pre_spike', 'internal_post_spike'):
        schedules.append(('b', Q(2), Q(2)))
    initial = state(y=1 if name == 'coupled' else 0,
                    x=1 if name == 'nonlinear_wrong_witness' else 0,
                    p=name in ('guard_remember', 'guard_undefined'))
    if name in ('undefined_rate', 'guard_undefined', 'guard_rate_undefined'):
        initial = state(y=None, p=name == 'guard_undefined')
    if name == 'guard_false':
        initial = state(x=None)
    if name in ('derived_dip', 'derived_history_dip'):
        initial = state(x=1, y=-1)
    if name in ('internal_pre_spike', 'internal_post_spike'):
        initial = state(x=-1)
    if name in ('lexical_at', 'lexical_over'):
        predicate = 'at' if name == 'lexical_at' else 'over'
        for left in ('end', 'all', 'depot'):
            for right in ('end', 'all', 'depot'):
                initial[f'({predicate} {left} {right})'] = (left == ('end' if predicate == 'at' else 'all') and right == 'depot')
    # Each pair is (x(u),y(u)), u=time-left; every coefficient is exact.
    single = {
        'linear': ([1, 2], [0]),
        'lexical_at': ([0, 1], [0]),
        'lexical_over': ([0, 1], [0]),
        'derived_dip': ([1, -2, 1], [-1, 1]),
        'derived_history_dip': ([1, -2, 1], [-1, 1]),
        'coupled': ([0, 1, 1], [1, 2]),
        'derived_open': ([0, 1], [0]),
        'interior_violation': ([0, 4, -4], [0, 1]),
        'history_false': ([0, 4, -4], [0, 1]),
        'history_true': ([0, 1], [0]),
        'guard_remember': ([0, 1], [0]),
        'endpoint_singular': ([0, 1], [0, 1]),
        'forall_rate': ([0, 2], [0]),
        'nonlinear_wrong_witness': ([1, 1], [0]),
    }
    curves = [single.get(name, ([0], [0]))]
    if name == 'overlap':
        curves = [([0, 1], [0]), ([1, 3], [0]), ([4, 2], [0])]
    elif name == 'internal_jump':
        curves = [([0, 1], [0]), ([5, 1], [0])]
    elif name == 'internal_pre_spike':
        curves = [([-1, 1], [0]), ([-1, 1], [0])]
    elif name == 'internal_post_spike':
        curves = [([-1, -1], [0]), ([0, -1], [0])]
    times = sorted({t for _, start, end in schedules for t in (start, end)})
    pre, post = [initial], []
    active_curves = []
    for i, time in enumerate(times):
        current = dict(pre[-1])
        if name == 'linear':
            current['(x)'] += 1 if i == 0 else -1
        if name == 'guard_remember' and i == 0:
            current['(p)'] = False
        if name == 'history_true' and i == len(times) - 1:
            current['(done)'] = True
        if name == 'internal_jump' and time == 2:
            current['(x)'] = Q(5)
        if name == 'internal_pre_spike' and time == 2:
            current['(x)'] = Q(-1)
        if name == 'internal_post_spike' and time == 2:
            current['(x)'] = Q(0)
        current['(d)'] = current['(x)'] is not None and current['(x)'] > 0
        post.append(current)
        following = dict(current)
        if i + 1 < len(times):
            cx, cy = curves[i]
            active_curves.append((time, times[i + 1], cx, cy))
            for key, curve in [('(x)', cx), ('(y)', cy)]:
                if following[key] is not None:
                    following[key] = value(curve, times[i + 1] - time)
            following['(d)'] = following['(x)'] is not None and following['(x)'] > 0
        pre.append(following)
    count = horizon * 2
    while len(post) < count:
        post.append(dict(pre[-1])); pre.append(dict(pre[-1]))
    # Independent mathematical negative cases:
    # x=4u(1-u) violates x<1 at u=1/2; undefined y poisons a rate or
    # Boolean guard even under true OR; y/y has no source value at u=0;
    # 1+u does not solve x'=x except at its initial point.
    valid = name not in {'interior_violation', 'undefined_rate', 'guard_undefined',
                         'endpoint_singular', 'nonlinear_wrong_witness', 'derived_dip',
                         'internal_pre_spike', 'internal_post_spike'}
    return dict(horizon=horizon, schedule=schedules, times=times, pre=pre, post=post,
                curves=active_curves, valid=valid, makespan=max(times, default=Q(0)))


def exact(v):
    return z3.RealVal(str(v))


def polynomial(coefficients, elapsed):
    result = exact(0)
    for coefficient in reversed(coefficients):
        result = exact(coefficient) + elapsed * result
    return result


rows = []
def save():
    (ROOT / 'pddl-continuous-source-oracles.json').write_text(json.dumps({
        'passed': len(rows) == 25 and all(r['passed'] for r in rows), 'cases': rows,
        'scope': 'complete pre/post source-state and signed-objective relation for each fixed rational schedule and entire explicit trajectory witness',
        'unrestricted_ode_decision_claim': False, 'sampling': False, 'limits': None}, indent=2) + '\n')

ledger = [line.split('\t') for line in (ROOT / 'source-controls.tsv').read_text().splitlines()]
assert len(ledger) == 34 and len({r[0] for r in ledger}) == 34
assert all(expected == actual for _, expected, actual in ledger)
assert sum(expected == '1' for _, expected, _ in ledger) == 25
for name, accepted, _ in ledger:
    if accepted != '1':
        continue
    reference_state = reference(name)
    parsed = z3.Optimize(); parsed.from_file(str(ROOT / (name + '.smt2')))
    assert len(parsed.objectives()) == 1
    # Internal and public targets both undergo full SMT loading. The actual
    # relation below uses the public translate()/pass/lowering output.
    internal = z3.Optimize(); internal.from_file(str(ROOT / (name + '.internal.smt2')))
    assert len(internal.objectives()) == 1
    aliases = dict(line.split('\t') for line in (ROOT / (name + '.tsv')).read_text().splitlines())
    expected_labels = set()
    for mode, snapshots in [('state', reference_state['pre']), ('post', reference_state['post'])]:
        for step, snapshot in enumerate(snapshots):
            expected_labels.update(f'{mode}[{step}]::{atom}' for atom in snapshot)
            expected_labels.update(f'{mode}[{step}]::defined::{atom}' for atom in ('(x)', '(y)'))
    for slot, _ in enumerate(reference_state['schedule']):
        expected_labels.update((f'plan[{slot}]::start', f'plan[{slot}]::end'))
        expected_labels.update(f'choice[{slot}]::({action})' for action in {a for a, _, _ in reference_state['schedule']})
    for step in range(max(0, 2 * reference_state['horizon'] - 1)):
        expected_labels.update(f'flow[{step}]::{atom}' for atom in ('(x)', '(y)', '(d)'))
    assert set(aliases) == expected_labels, (name, 'incomplete source signature', sorted(expected_labels - set(aliases)), sorted(set(aliases) - expected_labels))
    signed = z3.Real('__independent_signed_makespan')
    actual = z3.And(*parsed.assertions(), signed == parsed.objectives()[0])
    function_replacements = []
    for step in range(max(0, 2 * reference_state['horizon'] - 1)):
        for index in range(2):
            curve = z3.Function(f'__pddl_flow_{step}_{index}', z3.RealSort(), z3.RealSort())
            time = z3.Var(0, z3.RealSort())
            if step < len(reference_state['curves']):
                left, right, cx, cy = reference_state['curves'][step]
                body = z3.If(z3.And(time >= exact(left), time <= exact(right)),
                             polynomial((cx, cy)[index], time - exact(left)), exact(0))
            else:
                body = exact(0)
            function_replacements.append((curve, body))
    if function_replacements:
        actual = z3.substitute_funs(actual, *function_replacements)
    expected, fixed, replacements, observed = [], [], [], {str(signed)}
    for slot, (action, start, end) in enumerate(reference_state['schedule']):
        for endpoint, v in [('start', start), ('end', end)]:
            base = f'__pddl_occurrence_{slot}_{endpoint}'
            replacements.extend([(z3.Int(base + '_numerator'), z3.IntVal(v.numerator)),
                                 (z3.Int(base + '_denominator'), z3.IntVal(v.denominator))])
    for label, target in aliases.items():
        match = re.fullmatch(r'(state|post)\[(\d+)\]::(.*)', label)
        if match:
            mode, step, atom = match.groups(); snapshot = reference_state['pre' if mode == 'state' else 'post'][int(step)]
            if atom.startswith('defined::'):
                term = z3.Bool(target) == (snapshot[atom[len('defined::'):]] is not None)
            elif atom in ('(x)', '(y)'):
                term = z3.Real(target) == exact(snapshot[atom] if snapshot[atom] is not None else 0)
            else:
                assert atom in snapshot, (name, label)
                term = z3.Bool(target) == snapshot[atom]
            observed.add(target); expected.append(term)
        elif label.startswith('plan['):
            slot, endpoint = re.fullmatch(r'plan\[(\d+)\]::(start|end)', label).groups()
            schedule = reference_state['schedule'][int(slot)]
            term = z3.Real(target) == exact(schedule[1 if endpoint == 'start' else 2])
            observed.add(target); expected.append(term); fixed.append(term)
            replacements.append((z3.Real(target), exact(schedule[1 if endpoint == 'start' else 2])))
        elif label.startswith('choice['):
            slot, action = re.fullmatch(r'choice\[(\d+)\]::\(([^()]+)\)', label).groups()
            term = z3.Bool(target) == (reference_state['schedule'][int(slot)][0] == action)
            observed.add(target); expected.append(term); fixed.append(term)
            replacements.append((z3.Bool(target), z3.BoolVal(reference_state['schedule'][int(slot)][0] == action)))
        else:
            assert re.fullmatch(r'flow\[\d+\]::\((?:x|y|d)\)', label), (name, label)
    # Fix administrative happening coordinates to this exact source schedule;
    # strict order + occupancy determine the same unique grid independently.
    for step in range(2 * reference_state['horizon']):
        active = step < len(reference_state['times'])
        replacements.extend([
            (z3.Bool(f'__pddl_happening_{step}_active'), z3.BoolVal(active)),
            (z3.Real(f'__pddl_happening_{step}_time'), exact(reference_state['times'][step] if active else 0))])
    if replacements:
        actual = z3.substitute(actual, *replacements)
    actual = z3.simplify(z3.And(actual, *fixed))
    auxiliary = [v for v in get_vars(actual) if str(v) not in observed]
    projected = z3.Exists(auxiliary, actual) if auxiliary else actual
    oracle = z3.And(*expected, signed == exact(reference_state['makespan'])) if reference_state['valid'] else z3.BoolVal(False)
    # Independently check every exported derived trajectory function itself,
    # including functions unused by a goal/invariant. Its full interpretation
    # must be the pointwise source LFP, not merely agree at two endpoints.
    derived_checks = []
    raw_target = (ROOT / (name + '.smt2')).read_text()
    for step in range(max(0, 2 * reference_state['horizon'] - 1)):
        point = z3.Real('__oracle_flow_point')
        if step < len(reference_state['curves']) and reference_state['post'][step]['(x)'] is not None:
            left, right, cx, _ = reference_state['curves'][step]
            wanted = z3.And(point >= exact(left), point <= exact(right), polynomial(cx, point - exact(left)) > 0)
        else:
            wanted = z3.BoolVal(False)
        target = aliases[f'flow[{step}]::(d)']
        assertion = f'(assert (forall ((__oracle_flow_point Real)) (= (|{target}| __oracle_flow_point) {wanted.sexpr()})))'
        check = z3.Optimize(); check.from_string(raw_target + '\n' + assertion)
        definition = check.assertions()[-1]
        if function_replacements:
            definition = z3.substitute_funs(definition, *function_replacements)
        scalar_definitions = []
        for index, snapshot in enumerate(reference_state['post']):
            for atom in ('(x)', '(y)'):
                target_defined = aliases[f'post[{index}]::defined::{atom}']
                scalar_definitions.append((z3.Bool(target_defined), z3.BoolVal(snapshot[atom] is not None)))
        definition = z3.substitute(definition, *(replacements + scalar_definitions))
        derived_checks.append(z3.Not(definition))
    # A bad exported derived function is a counterexample even when the
    # trajectory does not satisfy the rest of this particular plan's goal.
    # Exact QE specializes the nested epsilon/delta definition itself, not a
    # replacement derivative implementation. Unknown/failure remains failure.
    (ROOT / 'pddl-continuous-current.json').write_text(json.dumps({'case': name, 'phase': 'exact-trajectory-QE', 'started_unix': clock.time(), 'limits': None}) + '\n')
    xor = z3.Tactic('qe')(z3.simplify(z3.Or(z3.Xor(projected, oracle), *derived_checks))).as_expr()
    solver = z3.Solver(); solver.add(xor)
    result = solver.check()
    row = dict(case=name, passed=result == z3.unsat, full_witness_relation_xor=str(result),
               independently_valid=reference_state['valid'], source_observables=len(observed),
               entire_functions_specialized=len(function_replacements),
               pointwise_derived_functions_checked=len(derived_checks),
               target_sha256=hashlib.sha256((ROOT / (name + '.smt2')).read_bytes()).hexdigest(),
               public_pipeline=True)
    if result != z3.unsat:
        row['counterexample'] = str(solver.model()) if result == z3.sat else solver.reason_unknown()
    rows.append(row); save(); assert row['passed'], row
print(json.dumps({'passed': True, 'full_witness_relations': len(rows), 'rejected_sources': 9}))
