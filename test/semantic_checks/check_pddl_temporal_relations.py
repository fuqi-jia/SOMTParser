"""Independent source-derived duration, history, frame and concurrency controls.

Run only on the server. These checks examine the complete emitted assertions;
they impose no solver deadline and do not classify timeout as a semantic result.
"""
from fractions import Fraction
from pathlib import Path
import json
import sys
import z3

root = Path(sys.argv[1])
expected = {
    'duration_update': True, 'invariant_broken': False, 'open_interval': True,
    'history_true': True, 'history_false': False, 'conditional_interval': True,
    'overlap': True, 'concurrent_add': True, 'concurrent_assign': True,
    'inactive_disjunct_read': True, 'duration_start_state': True,
    'duration_end_state': True, 'derived_open_interval': True, 'derived_broken': False,
    'derived_mutex': True, 'duration_read_mutex': True, 'relative_undefined': False,
    'folded_derived_mutex': True, 'folded_numeric_derived_mutex': True,
    'zero_horizon': True, 'zero_duration': True, 'negative_duration': False,
    'duration_inequality': True,
}
two = {'overlap', 'concurrent_add', 'concurrent_assign', 'inactive_disjunct_read',
       'derived_mutex', 'duration_read_mutex', 'folded_derived_mutex', 'folded_numeric_derived_mutex'}
results = []
for name, satisfiable in expected.items():
    parsed = z3.Optimize()
    parsed.from_file(str(root / (name + '.smt2')))
    solver = z3.Solver()
    solver.add(*parsed.assertions())
    aliases = dict(line.split('\t') for line in (root / (name + '.tsv')).read_text().splitlines())
    check_count = 0

    def check(answer, *assumptions):
        global check_count
        solver.push()
        solver.add(*assumptions)
        actual = solver.check()
        assert actual == answer, (name, answer, actual, assumptions)
        solver.pop()
        check_count += 1

    def time(slot, endpoint):
        return z3.Real(aliases[f'plan[{slot}]::{endpoint}'])

    check(z3.sat if satisfiable else z3.unsat)
    if satisfiable and name != 'zero_horizon':
        # Goal forces a real occurrence, whose start must be strictly positive.
        check(z3.unsat, time(0, 'start') <= 0)
    if name in {'duration_update', 'duration_start_state', 'duration_end_state', 'zero_duration'}:
        duration = {'duration_update': Fraction('2.5'), 'duration_start_state': 1,
                    'duration_end_state': 2, 'zero_duration': 0}[name]
        exact = z3.RealVal(str(duration))
        check(z3.unsat, time(0, 'end') - time(0, 'start') != exact)
        check(z3.sat, time(0, 'start') == 1, time(0, 'end') == 1 + exact)
    if name == 'duration_update':
        x = z3.Real(aliases['state[2]::(x)'])
        check(z3.unsat, x != z3.RealVal('7/2'))
        assert len(parsed.objectives()) == 1
        check(z3.unsat, parsed.objectives()[0] != z3.RealVal('7/2'))
        # The unused y remains undefined, with its canonical zero value.
        y = z3.Real(aliases['state[2]::(y)'])
        check(z3.unsat, y != 0)
    if name == 'overlap':
        check(z3.sat, time(0, 'start') == 1, time(0, 'end') == 3,
              time(1, 'start') == 2, time(1, 'end') == 4)
        x, y = (z3.Real(aliases[f'state[4]::({label})']) for label in ['x', 'y'])
        check(z3.unsat, z3.Or(x != 2, y != 2))
    if name in two - {'overlap'}:
        simultaneous = [time(slot, end) == value for slot in range(2)
                        for end, value in [('start', 1), ('end', 2)]]
        check(z3.sat if name == 'concurrent_add' else z3.unsat, *simultaneous)
    if name == 'open_interval':
        initial = z3.Bool(aliases['state[0]::(p)'])
        final = z3.Bool(aliases['state[2]::(p)'])
        check(z3.unsat, z3.Or(initial, final))
    if name == 'conditional_interval':
        check(z3.unsat, z3.Bool(aliases['state[2]::(done)']))
    if name == 'duration_inequality':
        start, end = time(0, 'start'), time(0, 'end')
        for duration in ['199/100', '2', '5/2', '3', '301/100']:
            legal = Fraction(2) <= Fraction(duration) <= Fraction(3)
            check(z3.sat if legal else z3.unsat, start == 1, end - start == z3.RealVal(duration))
        assert len(parsed.objectives()) == 1
        check(z3.unsat, parsed.objectives()[0] != end)
    results.append({'case': name, 'source_satisfiable': satisfiable,
                    'whole_module_loaded': True, 'solver_checks': check_count})

output = {'passed': True, 'cases': results, 'solver_checks': sum(row['solver_checks'] for row in results),
          'claim': 'Independent source-derived discrete temporal controls; no official-corpus coverage claim.'}
(root / 'pddl-temporal-source-oracles.json').write_text(json.dumps(output, indent=2) + '\n')
print(json.dumps(output))
