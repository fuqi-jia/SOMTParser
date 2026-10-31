"""Independent AI2009 Figure 1 relation oracle. Run on the server only.

No generated formulas are inspected to select an expected answer. Finite
semantics below follows the paper's quantifier definitions (including its
explicit final-state fallback), independently of the production algorithms.
"""
from pathlib import Path
import hashlib
import json
import sys
import z3


def finite_oracle(kind):
    times = [0, 2, 5, 9]
    active = [z3.BoolVal(True)] + [z3.Bool(f'a{i}') for i in range(1, 4)]
    p = [z3.Bool(f'p{i}') for i in range(4)]
    defined = [z3.Bool(f'd{i}') for i in range(4)]
    positive = [z3.And(defined[i], p[i]) for i in range(4)]
    negative = [z3.And(defined[i], z3.Not(p[i])) for i in range(4)]
    other = [z3.And(z3.Bool(f'e{i}'), z3.Bool(f'q{i}')) for i in range(4)]
    # Disjoin every possible actual trajectory length. No prefix recurrence,
    # accumulated monitor state, or source implementation helper is reused.
    lengths = []
    for last in range(4):
        shape = z3.And(*[active[i] if i <= last else z3.Not(active[i]) for i in range(4)])
        positions = range(last + 1)
        if kind == 'end':
            sat = positive[last]
        elif kind == 'always':
            sat = z3.And(*[positive[i] for i in positions])
        elif kind == 'sometime':
            sat = z3.Or(*[positive[i] for i in positions])
        elif kind == 'within':
            sat = z3.Or(*[positive[i] for i in positions if times[i] <= 3])
        elif kind == 'once':
            sat = z3.And(*[
                z3.Implies(positive[i], z3.Or(*[
                    z3.And(*[positive[k] for k in range(i, j + 1)],
                           *[negative[k] for k in range(j + 1, last + 1)])
                    for j in range(i, last + 1)]))
                for i in positions])
        elif kind in {'before', 'after', 'always_within'}:
            sat = z3.And(*[
                z3.Implies(positive[i], z3.Or(*[
                    other[j] for j in positions
                    if (j < i if kind == 'before' else j >= i)
                    and (kind != 'always_within' or times[j] - times[i] <= 3)]))
                for i in positions])
        elif kind == 'hold_after':
            sat = (z3.Or(*[positive[i] for i in positions if times[i] > 3])
                   if times[last] > 3 else positive[last])
        elif kind == 'during':
            if times[last] <= 3:
                sat = positive[last]
            else:
                sat = z3.And(*[positive[i] for i in positions if 3 <= times[i] < 8],
                             *[positive[j] for j in range(last) if times[j] <= 3 < times[j+1]])
        else:
            raise AssertionError(kind)
        lengths.append(z3.And(shape, z3.Bool('result') == sat))
    return z3.Or(*lengths)


def expected_relations():
    operations = ['end', 'always', 'sometime', 'within', 'once', 'before', 'after',
                  'always_within', 'during', 'hold_after']
    result = {f'{profile}_{op}': finite_oracle(op)
              for profile in ['finite', 'observed'] for op in operations}
    # Exact analytic truth, including interior-only witnesses/counterexamples.
    dense = {
        'dense_always': False, 'dense_sometime': True, 'dense_within': True,
        'dense_once_gap': False, 'dense_once_interval': True,
        'dense_undefined_tail': False, 'dense_during': True,
        'dense_hold_after_strict': False, 'dense_hold_after_witness': True,
        'dense_hold_after_fallback': True, 'dense_before_strict': False,
        'dense_after_same': True, 'scope_shadow': True, 'phase_order': True,
    }
    result.update({name: z3.Bool('result') == value for name, value in dense.items()})
    a, b, on = z3.Bools('a b on')
    unit = lambda formula: z3.If(formula, 0, 1)
    anon = unit(a) + z3.If(on, unit(b), 0)
    result['preferences'] = z3.And(
        z3.Int('outer') == unit(z3.And(a, b)),
        z3.Int('inner') == unit(a) + unit(b),
        z3.Int('pre') == z3.If(on, 3 * unit(z3.And(a, b)), 0),
        z3.Int('anonymous') == anon,
        z3.Real('min') == z3.RealVal('3/2') + anon,
        z3.Int('max') == 7 - anon)
    result['preferences_empty'] = z3.And(z3.Int('zero') == 0, z3.Int('empty_group') == 0)
    return result


def main(directory):
    rows = []
    expected = expected_relations()
    found = {p.stem for p in directory.glob('*.smt2')}
    if found != set(expected):
        raise AssertionError({'missing': sorted(set(expected)-found), 'extra': sorted(found-set(expected))})
    for name, oracle in expected.items():
        path = directory/f'{name}.smt2'
        target = z3.And(*z3.parse_smt2_file(str(path)))
        difference = z3.Xor(target, oracle)
        # Linear Real/Int domain quantifiers are eliminated exactly; this is
        # not endpoint sampling or a finite set of time instantiations.
        reduced = z3.Tactic('qe')(difference).as_expr()
        solver = z3.Solver()
        solver.add(reduced)
        answer = solver.check()
        row = {'case': name, 'target_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
               'whole_target_parse': True, 'full_relation': str(answer)}
        if answer != z3.unsat:
            row['diagnostic'] = str(solver.model()) if answer == z3.sat else solver.reason_unknown()
        rows.append(row)
        (directory/'planning-trajectory-full-relations.json').write_text(
            json.dumps({'passed': all(r['full_relation']=='unsat' for r in rows),
                        'completed': len(rows), 'expected': len(expected), 'cases': rows}, indent=2)+'\n')
        if answer != z3.unsat:
            raise AssertionError(row)
    # Mutants encode familiar but false substitutions; these SAT checks ensure
    # the independent cases actually distinguish each mistake.
    mutants = {}
    for name, wrong in {
        'dense_always': True,       # Endpoints-only sampling.
        'dense_after_same': False, # Replacing >= by >.
        'dense_before_strict': True,
        'dense_hold_after_witness': False, # Replacing exists-after by always-after.
        'dense_during': False,     # Closing the right endpoint.
        'dense_undefined_tail': True,
    }.items():
        solver=z3.Solver();solver.add(z3.Xor(expected[name], z3.Bool('result')==wrong))
        answer=solver.check();assert answer==z3.sat
        mutants[name]=str(answer)
    receipt={'passed':True,'complete_relation_checks':len(rows),'cases':rows,
             'mutant_counterexamples':mutants,'solver':z3.get_version_string()}
    (directory/'planning-trajectory-full-relations.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'passed':True,'complete_relation_checks':len(rows),'mutants':len(mutants)}))


if __name__=='__main__':
    main(Path(sys.argv[1]))
