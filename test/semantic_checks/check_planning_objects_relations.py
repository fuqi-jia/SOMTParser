"""Exhaustive finite-state reference, then full SMT relation XOR; server only.

This interprets the fixtures directly using Python objects/None. It does not
copy the HIR selector/frame encoding or use SAT agreement as equivalence.
Neither solver resources nor elapsed time are capped. Unknown is a failure.
"""
from fractions import Fraction
from itertools import product
from pathlib import Path
import hashlib
import json
import sys
import z3

root = Path(sys.argv[1])
old = z3.Ints('x y z')
new = z3.Ints('nx ny nz')
od = z3.Bools('xd yd zd')
nd = z3.Bools('nxd nyd nzd')
a, b = z3.Bools('a b')
observed, observed_defined = z3.Bools('observed observed_defined')
observed_int = z3.Int('observed_int')
observed_real = z3.Real('observed_real')
codes = {None: 0, 'a': 1, 'b': 2, 'p': 3}
BAD = object()


def lookup(state, argument):
    return None if argument is None else state[0 if argument == 'a' else 1]


def reference(name, state, ga, gb):
    nxt = list(state)
    obs = {}
    writes = []
    agreeing = name in {'alias_agree', 'value_conflict', 'undefined_agree', 'undefined_conflict'}
    if name == 'initial' and state != (None, 'b', None):
        return None
    if name == 'constant' and ga:
        writes = [(0, 'b')]
    elif name == 'undefined' and ga:
        writes = [(0, None)]
    elif name == 'swap' and ga:
        if state[0] is None or state[1] is None:
            return None
        writes = [(0, state[1]), (1, state[0])]
    elif name == 'nested' and ga:
        value = lookup(state, lookup(state, state[2]))
        if value is None:
            return None
        writes = [(2, value)]
    elif name in {'dynamic_address', 'old_address'} and ga:
        if state[2] is None:
            return None
        writes = [(0 if state[2] == 'a' else 1, 'b' if name == 'dynamic_address' else 'a')]
        if name == 'old_address':
            writes.append((2, 'b'))
    elif name in {'alias_conflict', 'alias_agree'}:
        for flag, address in ((ga, state[2]), (gb, state[1])):
            if flag:
                if address is None:
                    return None
                writes.append((0 if address == 'a' else 1, 'a'))
    elif name in {'value_conflict', 'undefined_agree', 'undefined_conflict'}:
        if ga:
            writes.append((0, 'a' if name == 'value_conflict' else None))
        if gb:
            writes.append((0, 'b' if name == 'value_conflict' else None if name == 'undefined_agree' else 'a'))
    elif name == 'union_assignment' and ga:
        writes = [(2, 'p')]
    assigned = {}
    for target, value in writes:
        if target in assigned and (not agreeing or assigned[target] != value):
            return None
        assigned[target] = value
        nxt[target] = value
    if name.startswith(('not_', 'or_')):
        strict = name.endswith('_strict')
        value = state[2] == 'a'
        defined = state[2] is not None
        if name.startswith('not_'):
            obs[observed] = not value
        else:
            obs[observed] = True
        obs[observed_defined] = defined if strict else True
    elif name.startswith('predicate_'):
        value = lookup(state, state[2])
        obs[observed] = value == 'b'
        obs[observed_defined] = value is not None if name.endswith('_strict') else True
    elif name == 'numeric_arguments':
        value = lookup(state, state[2])
        obs[observed_real] = 0 if value is None else Fraction(1 if value == 'a' else 2, 3)
        obs[observed_defined] = value is not None
    elif name == 'numeric_undefined':
        value = Fraction(1, 3) if state[2] == 'a' else None
        obs[observed_real] = 0 if value is None else value
        obs[observed_defined] = value is not None
    elif name == 'empty_carrier':
        obs[observed_int] = 0
        obs[observed_defined] = False
    elif name == 'nullary':
        obs[observed_int] = codes[state[1]]
        obs[observed_defined] = state[1] is not None
    return tuple(nxt), obs


names = ['initial', 'frame', 'constant', 'undefined', 'swap', 'nested',
         'dynamic_address', 'old_address', 'alias_conflict', 'alias_agree',
         'value_conflict', 'undefined_agree', 'undefined_conflict',
         'not_strict', 'not_atomic_false', 'or_strict', 'or_atomic_false',
         'predicate_strict', 'predicate_atomic_false', 'numeric_arguments',
         'numeric_undefined', 'union_assignment', 'empty_carrier', 'nullary']
expected_refusals = {
    'undefined_is_not_a_term', 'type_cycle', 'duplicate_object', 'unknown_union_member',
    'missing_table_row', 'duplicate_table_row', 'wrong_type_table_row',
    'wrong_argument_type', 'wrong_return_type', 'aliased_ground_cells',
    'duplicate_initialization', 'wrong_initial_type', 'inactive_wrong_assignment_type',
    'inactive_wrong_sort', 'missing_read_metadata', 'future_hidden_active',
    'future_hidden_inactive', 'invalid_target_cell', 'unbound_table_argument',
    'free_bound_variable',
}
refusals = json.loads((root / 'object-refusals.json').read_text())
assert refusals['passed'] is True
assert set(refusals['cases']) == expected_refusals
assert len(refusals['cases']) == len(expected_refusals)
assert set(path.stem for path in root.glob('*.smt2')) == set(names)
rows = []
for name in names:
    domain = (None, 'a', 'b')
    third = (None,) if name == 'empty_carrier' else domain + ('p',) if name == 'union_assignment' else domain
    alternatives = []
    for state in product(domain, domain, third):
        for ga, gb in product((False, True), repeat=2):
            result = reference(name, state, ga, gb)
            if result is None:
                continue
            nxt, obs = result
            terms = [a == ga, b == gb]
            for vals, defs, objects in ((old, od, state), (new, nd, nxt)):
                for value, defined, obj in zip(vals, defs, objects):
                    terms.extend((value == codes[obj], defined == (obj is not None)))
            for symbol, value in obs.items():
                if isinstance(value, Fraction):
                    value = z3.RealVal(f'{value.numerator}/{value.denominator}')
                terms.append(symbol == value)
            alternatives.append(z3.And(*terms))
    oracle = z3.Or(*alternatives)
    path = root / (name + '.smt2')
    target = z3.And(*z3.parse_smt2_file(str(path)))
    solver = z3.Solver()
    solver.add(z3.Xor(target, oracle))
    result = solver.check()
    row = {'case': name, 'complete_finite_reference_rows': len(alternatives),
           'full_relation_xor': str(result), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
    if result != z3.unsat:
        row['diagnostic'] = str(solver.model()) if result == z3.sat else solver.reason_unknown()
        (root / 'object-oracle-failure.json').write_text(json.dumps(row, indent=2) + '\n')
        raise AssertionError(row)
    # A whole-cell shifted successor relation must be distinguishable. This
    # control catches a checker that accidentally drops all successor values.
    mutant = z3.substitute(oracle, (new[0], new[0] + 1))
    check = z3.Solver()
    check.add(target, z3.Not(mutant))
    mutation = check.check()
    assert mutation == z3.sat, (name, mutation)
    row['shifted_successor_detected'] = True
    rows.append(row)
report = {'passed': True, 'api_only': True, 'pddl_frontend_qualified': False,
          'cases': rows, 'refusals': refusals, 'limits': None}
(root / 'object-full-relations.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
