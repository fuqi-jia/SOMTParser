"""Complete object/preference relations, specialized to fixed source schedules.

The independent source oracle below uses object names/None and checks guarded
source read/write sets before simultaneous updates. The continuous clock has
the explicitly fixed, entire zero trajectory. Every exported object value and
definedness function is compared for ALL real arguments, including interval
boundaries and canonical out-of-domain values. No point sampling or solver
limits; no claim about arbitrary ODE decision procedures.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json
import re
import sys
import time
import z3
from z3.z3util import get_vars

OBJECTS = ('a', 'b')
CELLS = ('(pick)', '(other)', '(slot a)', '(slot b)')
PREDICATES = ('(done-reader)', '(done-writer)')


def source_address(spelling, state):
    if spelling == '(slot (other))':
        selected = state['(other)']
        return (None if selected is None else f'(slot {selected})'), {'(other)'}
    assert spelling in CELLS, spelling
    return spelling, set()


def source_preference(state):
    selected = state['(pick)']
    reads = {'(pick)'}
    if selected is None:
        return False, reads
    cell = f'(slot {selected})'
    reads.add(cell)
    return state[cell] == 'a', reads


def source_relation(case):
    specification = case['source']
    schedule = [(name, Q(start), Q(end)) for name, start, end in specification['schedule']]
    times = sorted({t for _, start, end in schedule for t in (start, end)})
    pre = [dict(specification['initial'], **{p: False for p in PREDICATES}, **{'(clock)': Q(0)})]
    post, valid, satisfaction = [], True, []
    for instant in times:
        old = pre[-1]
        events = []
        for name, start, end in schedule:
            if name == 'reader':
                for endpoint, when in (('start', start), ('end', end)):
                    if instant != when:
                        continue
                    reads, writes = set(), {}
                    if specification['preference_point'] == endpoint:
                        holds, preference_reads = source_preference(old)
                        reads |= preference_reads
                        satisfaction.append(holds)
                    if endpoint == 'start' and specification['own_assignment']:
                        target, rhs = specification['own_assignment']
                        address, address_reads = source_address(target, old)
                        reads |= address_reads
                        valid &= address is not None
                        if address is not None: writes[address] = None if rhs == 'undefined' else rhs
                    if endpoint == 'end': writes['(done-reader)'] = True
                    events.append((name + ':' + endpoint, reads, writes))
            elif instant == start:
                assert start == end
                target, rhs = specification['writer_assignment']
                address, reads = source_address(target, old)
                writes = {'(done-writer)': True}
                valid &= address is not None
                if address is not None: writes[address] = None if rhs == 'undefined' else rhs
                events.append(('writer:start', reads, writes))
        # Reads include undefined cells, while an undefined selector contributes
        # no fictitious selected-row read. Ownership exempts the same endpoint.
        for i, (owner, reads, writes) in enumerate(events):
            for other_owner, other_reads, other_writes in events[i+1:]:
                if owner != other_owner:
                    valid &= not (reads & other_writes.keys() or other_reads & writes.keys()
                                  or writes.keys() & other_writes.keys())
        successor = dict(old)
        for _, _, writes in events: successor.update(writes)
        post.append(successor)
        pre.append(dict(successor))  # Whole clock trajectory is identically zero.
    if specification['preference_point'] == 'overall':
        start, end = schedule[0][1:]
        for i in range(len(times)-1):
            if start <= times[i] and times[i+1] <= end:
                satisfaction.append(source_preference(post[i])[0])
        for i, instant in enumerate(times):
            if start < instant < end:
                satisfaction.extend((source_preference(pre[i])[0], source_preference(post[i])[0]))
    assert satisfaction
    violations = int(not all(satisfaction))
    cost = max((end for _, _, end in schedule), default=Q(0)) + 7 * violations
    assert dict(valid=bool(valid), violations=violations, signed_cost=int(cost)) == case['expected'], case['name']
    while len(post) < 2 * case['horizon']:
        post.append(dict(pre[-1])); pre.append(dict(pre[-1]))
    return schedule, times, pre, post, bool(valid), cost


def object_code(value):
    return 0 if value is None else OBJECTS.index(value) + 1


def real(value):
    return z3.RealVal(str(value))


def verify(output):
    cases = json.loads(Path(__file__).with_name('cases.json').read_text())
    ledger = [row.split('\t') for row in (output/'pddl3-object-preference-controls.tsv').read_text().splitlines()]
    assert len(ledger) == len(cases) == 13
    assert {n: int(h) for n,h in ledger} == {c['name']: c['horizon'] for c in cases}
    results = []
    for case in cases:
        name, count = case['name'], 2 * case['horizon']
        schedule, times, pre, post, valid, cost = source_relation(case)
        assert (output/(name+'.domain.pddl')).read_text() == case['domain']
        assert (output/(name+'.problem.pddl')).read_text() == case['problem']
        alias_rows = [row.split('\t') for row in (output/(name+'.tsv')).read_text().splitlines()]
        aliases = dict(alias_rows)
        assert len(aliases) == len(alias_rows)
        expected_values = {}
        for mode, snapshots in (('state', pre), ('post', post)):
            for step, state in enumerate(snapshots):
                prefix = f'{mode}[{step}]::'
                expected_values.update({prefix+p: state[p] for p in PREDICATES})
                expected_values[prefix+'(clock)'] = Q(0)
                expected_values[prefix+'defined::(clock)'] = True
                for cell in CELLS:
                    expected_values[prefix+'object-code::'+cell] = object_code(state[cell])
                    expected_values[prefix+'defined(object::'+cell+')'] = state[cell] is not None
        actions = ['reader'] + (['writer'] if case['source']['writer_assignment'] else [])
        for slot, (action, start, end) in enumerate(schedule):
            expected_values[f'plan[{slot}]::start'] = start
            expected_values[f'plan[{slot}]::end'] = end
            for alternative in actions:
                expected_values[f'choice[{slot}]::({alternative})'] = action == alternative
        functions = set()
        for step in range(count-1):
            functions.add(f'flow[{step}]::(clock)')
            for cell in CELLS:
                functions.update((f'flow[{step}]::object-code::{cell}', f'flow[{step}]::defined(object::{cell})'))
        assert set(aliases) == set(expected_values) | functions, (name, set(aliases) ^ (set(expected_values) | functions))
        equalities, observed, fixed, substitutions = [], set(), [], []

        def observe(target, value):
            if isinstance(value, bool): term, literal = z3.Bool(target), z3.BoolVal(value)
            elif isinstance(value, Q): term, literal = z3.Real(target), real(value)
            else: term, literal = z3.Int(target), z3.IntVal(value)
            observed.add(target)
            equalities.append(term == literal)
            return term, literal

        for label, value in expected_values.items():
            pair = observe(aliases[label], value)
            if label.startswith(('plan[', 'choice[')):
                substitutions.append(pair); fixed.append(pair[0] == pair[1])
        choices = [row.split('\t') for row in (output/(name+'.choices.tsv')).read_text().splitlines()]
        expected_choice_values = {}
        for mode, snapshots in (('state', pre), ('post', post)):
            for step, state in enumerate(snapshots):
                for cell in CELLS:
                    for alternative in ('undefined',) + OBJECTS:
                        wanted = 'undefined' if state[cell] is None else state[cell]
                        expected_choice_values[(f'{mode}[{step}]::object::{cell}', alternative)] = wanted == alternative
        for slot, (action, _, _) in enumerate(schedule):
            for alternative in ['__pddl_padding_noop'] + ['('+a+')' for a in actions]:
                expected_choice_values[(f'plan[{slot}]', alternative)] = alternative == '('+action+')'
        assert len(choices) == len(expected_choice_values)
        assert {(label, alternative) for label, alternative, _ in choices} == set(expected_choice_values)
        for label, alternative, target in choices:
            observe(target, expected_choice_values[(label, alternative)])
        for slot, (_, start, end) in enumerate(schedule):
            for endpoint, instant in (('start', start), ('end', end)):
                base = f'__pddl_occurrence_{slot}_{endpoint}'
                substitutions.extend(((z3.Int(base+'_numerator'), z3.IntVal(instant.numerator)),
                                      (z3.Int(base+'_denominator'), z3.IntVal(instant.denominator))))
        for step in range(count):
            substitutions.extend(((z3.Bool(f'__pddl_happening_{step}_active'), z3.BoolVal(step < len(times))),
                                  (z3.Real(f'__pddl_happening_{step}_time'), real(times[step] if step < len(times) else 0))))
        clock_witnesses = [(z3.Function(aliases[f'flow[{step}]::(clock)'], z3.RealSort(), z3.RealSort()), real(0))
                           for step in range(count-1)]
        target = output/(name+'.smt2')
        raw = target.read_text()
        loaded = z3.Optimize(); loaded.from_string(raw)
        assert len(loaded.objectives()) == 1
        signed = z3.Real('__object_preference_source_signed_cost'); observed.add(str(signed))
        actual = z3.And(*loaded.assertions(), signed == loaded.objectives()[0])
        actual = z3.simplify(z3.And(z3.substitute(z3.substitute_funs(actual, *clock_witnesses), *substitutions), *fixed))
        auxiliaries = [term for term in get_vars(actual) if str(term) not in observed]
        projected = z3.Exists(auxiliaries, actual) if auxiliaries else actual
        oracle = z3.And(*equalities, signed == real(cost)) if valid else z3.BoolVal(False)
        # Reparse the actual public define-fun bodies, retaining all scalar
        # dependencies; NEVER replace object trajectories with our expected
        # definitions before proving they agree for every real argument.
        cut = raw.index('(check-sat)')
        point = z3.Real('__object_preference_source_time')
        view_failures = []
        for step in range(count-1):
            inside = z3.And(point >= real(times[step]), point <= real(times[step+1])) if step+1 < len(times) else z3.BoolVal(False)
            for cell in CELLS:
                wanted = {'object-code::'+cell: z3.If(inside, object_code(post[step][cell]), 0),
                          'defined(object::'+cell+')': z3.And(inside, post[step][cell] is not None)}
                for suffix, value in wanted.items():
                    function = aliases[f'flow[{step}]::{suffix}']
                    assertion = f'(assert (forall ((__object_preference_source_time Real)) (= (|{function}| __object_preference_source_time) {value.sexpr()})))'
                    parsed = z3.Optimize(); parsed.from_string(raw[:cut] + assertion + '\n' + raw[cut:])
                    view = parsed.assertions()[-1]
                    view_failures.append(z3.Not(z3.substitute(z3.substitute_funs(view, *clock_witnesses), *substitutions)))
        full_relation_query = z3.simplify(z3.Or(z3.Xor(projected, oracle), z3.And(actual, z3.Or(*view_failures))))
        (output/'pddl3-object-preference-current.json').write_text(json.dumps(dict(case=name,phase='full-relation',started_unix=time.time(),limits=None))+'\n')
        reduced = z3.Tactic('qe')(full_relation_query).as_expr()
        solver = z3.Solver(); solver.add(reduced); answer = solver.check()
        row = dict(case=name, whole_module_loaded=True, source_schedule_valid=valid,
            preference_violations=case['expected']['violations'], expected_signed_cost=str(cost),
            full_relation_xor=str(answer), all_source_aliases=len(aliases),
            scalar_equalities=len(equalities), named_object_and_plan_alternatives=len(choices),
            entire_clock_witnesses=len(clock_witnesses), entire_object_function_checks=len(view_failures),
            target_sha256=hashlib.sha256(target.read_bytes()).hexdigest())
        if answer != z3.unsat: row['detail'] = str(solver.model()) if answer == z3.sat else solver.reason_unknown()
        results.append(row)
        (output/'pddl3-object-preference-source-oracles.partial.json').write_text(json.dumps(results,indent=2)+'\n')
        assert answer == z3.unsat, row
    result = dict(passed=True, cases=results, full_relation_cases=len(results), limits=None, sampling=False,
        scope='complete observable and exact signed cost relation at fixed rational source schedules and an entire zero clock witness; every object pre/post, named alternative, and complete object function domain checked')
    (output/'pddl3-object-preference-source-oracles.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(passed=True,full_relation_cases=len(results))))


if __name__ == '__main__':
    verify(Path(sys.argv[1]))
