"""Full observable relations at fixed rational source schedules/flow witnesses.

Independent named-object/Fraction snapshots come from the source fixtures. Each
entire numeric function is specialized to its stated exact polynomial witness;
object/derived exported functions are compared pointwise, never sampled. The
frontend is not restricted to these polynomials. Valid schedules require an
actual model AND absence of any wrong observable tuple/function/objective;
invalid schedules/witnesses require UNSAT. Unknown is a failure. No limits.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json
import re
import sys
import z3
from check_pddl_object_relations import Source, call


def polynomial(coefficients, elapsed):
    value = z3.RealVal(0)
    for coefficient in reversed(coefficients): value = z3.RealVal(str(coefficient)) + elapsed * value
    return value


def numeric_value(coefficients, elapsed):
    value = Q(0)
    for coefficient in reversed(coefficients): value = Q(coefficient) + elapsed * value
    return value


def reference(case):
    source = Source(case['domain'], case['problem'])
    times = sorted({Q(t) for _, start, end in case['schedule'] for t in (start, end)})
    pre, post = [source.start()], []
    for i, time in enumerate(times):
        current = dict(pre[-1])
        for spelling, value in case['updates'].get(str(time), {}).items():
            key = tuple(spelling[1:-1].split())
            if key in source.fkeys:
                current[('function',) + key] = Q(value) if value is not None and source.fkeys[key] == 'number' else value
            else:
                assert key in source.pkeys
                current[('predicate',) + key] = value
        current = source.closure(current); post.append(current)
        following = dict(current)
        if case['curves'] is not None and i + 1 < len(times):
            curves = case['curves'][i]
            assert set(curves) == {call(k) for k, typ in source.fkeys.items() if typ == 'number'}
            for spelling, coefficients in curves.items():
                key = ('function',) + tuple(spelling[1:-1].split())
                if following[key] is not None:
                    # The initial value is an independent consistency check of
                    # the source witness, not inferred from the target.
                    assert following[key] == Q(coefficients[0]), (case['name'], spelling)
                    following[key] = numeric_value(coefficients, times[i + 1] - time)
        pre.append(source.closure(following))
    while len(post) < 2 * case['horizon']:
        post.append(dict(pre[-1])); pre.append(dict(pre[-1]))
    return source, times, pre, post


def verify(root):
    cases = json.loads(Path(__file__).with_name('pddl_object_temporal_cases.json').read_text())
    ledger = [line.split('\t') for line in (root / 'object-temporal-source-controls.tsv').read_text().splitlines()]
    assert {n: (int(h), a) for n, h, a in ledger} == {c['name']: (c['horizon'], '1') for c in cases}
    assert len(ledger) == len(cases) == 35
    rows = []
    for case in cases:
        name, count = case['name'], 2 * case['horizon']
        source, times, pre, post = reference(case)
        assert (root / (name + '.domain.pddl')).read_text() == case['domain']
        assert (root / (name + '.problem.pddl')).read_text() == case['problem']
        alias_rows = [line.split('\t') for line in (root / (name + '.tsv')).read_text().splitlines()]
        aliases = dict(alias_rows); assert len(aliases) == len(alias_rows)
        choices = [line.split('\t') for line in (root / (name + '.choices.tsv')).read_text().splitlines()]
        expected, scalar_values, fixed = {}, {}, []
        numeric_keys = [k for k, typ in source.fkeys.items() if typ == 'number']
        object_keys = [k for k, typ in source.fkeys.items() if typ != 'number']
        for mode, snapshots in [('state', pre), ('post', post)]:
            for step, state in enumerate(snapshots):
                prefix = f'{mode}[{step}]::'
                if mode == 'state' or case['curves'] is not None:
                    for key in source.pkeys: expected[prefix + call(key)] = bool(state[('predicate',) + key])
                    for key in numeric_keys:
                        value = state[('function',) + key]
                        expected[prefix + call(key)] = Q(0) if value is None else value
                        expected[prefix + 'defined::' + call(key)] = value is not None
                for key in object_keys:
                    value = state[('function',) + key]
                    expected[prefix + 'object-code::' + call(key)] = 0 if value is None else [o for o, _ in source.objects].index(value) + 1
                    expected[prefix + 'defined(object::' + call(key) + ')'] = value is not None
        action_names = {section[1] for section in source.domain[2:] if section[0] in (':action', ':durative-action')}
        for slot, (action, start, end) in enumerate(case['schedule']):
            expected[f'plan[{slot}]::start'] = Q(start); expected[f'plan[{slot}]::end'] = Q(end)
            for alternative in action_names: expected[f'choice[{slot}]::({alternative})'] = alternative == action
        flow_labels = set()
        if case['curves'] is not None:
            for step in range(max(0, count - 1)):
                prefix = f'flow[{step}]::'
                flow_labels.update(prefix + call(k) for k in numeric_keys)
                flow_labels.update(prefix + call(k) for k in source.pkeys if k[0] in source.derived)
                for key in object_keys:
                    flow_labels.update((prefix + 'object-code::' + call(key), prefix + 'defined(object::' + call(key) + ')'))
        assert set(aliases) == set(expected) | flow_labels, (name, set(aliases) ^ (set(expected) | flow_labels))
        def term(target, value):
            symbol = z3.Bool(target) if isinstance(value, bool) else z3.Real(target) if isinstance(value, Q) else z3.Int(target)
            literal = z3.BoolVal(value) if isinstance(value, bool) else z3.RealVal(str(value)) if isinstance(value, Q) else z3.IntVal(value)
            scalar_values[target] = (symbol, literal)
            return symbol == literal
        equalities = [term(aliases[label], value) for label, value in expected.items()]
        expected_choices = set()
        for mode, snapshots in [('state', pre), ('post', post)]:
            for step, state in enumerate(snapshots):
                for key in object_keys:
                    label = f'{mode}[{step}]::object::' + call(key)
                    expected_choices.add((label, 'undefined'))
                    expected_choices.update((label, obj) for obj, typ in source.objects if source.subtype(typ, source.fkeys[key]))
        for slot in range(case['horizon']):
            expected_choices.add((f'plan[{slot}]', '__pddl_padding_noop'))
            expected_choices.update((f'plan[{slot}]', '(' + action + ')') for action in action_names)
        assert {(label, alt) for label, alt, _ in choices} == expected_choices and len(choices) == len(expected_choices)
        for label, alternative, target in choices:
            if label.startswith('plan['):
                slot = int(label[5:-1]); truth = alternative == '(' + case['schedule'][slot][0] + ')'
            else:
                match = re.fullmatch(r'(state|post)\[(\d+)\]::object::\((.*)\)', label); assert match
                state = (pre if match[1] == 'state' else post)[int(match[2])]
                value = state[('function',) + tuple(match[3].split())]
                truth = alternative == ('undefined' if value is None else value)
            equalities.append(term(target, truth))
        # Pick canonical representatives of the same fixed rational schedule.
        # Numerator/denominator are existential administrative witnesses only.
        replacements = []
        for slot, (_, start, end) in enumerate(case['schedule']):
            for endpoint, value in [('start', Q(start)), ('end', Q(end))]:
                base = f'__pddl_occurrence_{slot}_{endpoint}'
                replacements += [(z3.Int(base + '_numerator'), z3.IntVal(value.numerator)),
                                 (z3.Int(base + '_denominator'), z3.IntVal(value.denominator))]
        for label, value in expected.items():
            if label.startswith(('plan[', 'choice[')):
                pair = scalar_values[aliases[label]]; replacements.append(pair); fixed.append(pair[0] == pair[1])
        for step in range(count):
            replacements += [(z3.Bool(f'__pddl_happening_{step}_active'), z3.BoolVal(step < len(times))),
                             (z3.Real(f'__pddl_happening_{step}_time'), z3.RealVal(str(times[step] if step < len(times) else 0)))]
        function_replacements = []
        if case['curves'] is not None:
            for step in range(max(0, count - 1)):
                point = z3.Var(0, z3.RealSort())
                for key in numeric_keys:
                    target = aliases[f'flow[{step}]::' + call(key)]
                    function = z3.Function(target, z3.RealSort(), z3.RealSort())
                    body = z3.RealVal(0)
                    if step + 1 < len(times):
                        body = z3.If(z3.And(point >= z3.RealVal(str(times[step])), point <= z3.RealVal(str(times[step + 1]))),
                                     polynomial(case['curves'][step][call(key)], point - z3.RealVal(str(times[step]))), z3.RealVal(0))
                    function_replacements.append((function, body))
        for suffix in ('.smt2', '.internal.smt2'):
            path = root / (name + suffix); raw = path.read_text()
            optimizer = z3.Optimize(); optimizer.from_string(raw)
            assert len(optimizer.objectives()) == 1
            signed = z3.Real('__object_temporal_reference_cost')
            relation = z3.And(*optimizer.assertions(), signed == optimizer.objectives()[0])
            wrong = [z3.Not(e) for e in equalities] + [signed != z3.RealVal(str(max(times, default=Q(0))))]
            # Public defined-function beta maps must equal the complete source
            # object/derived trajectory, including their out-of-interval value.
            extra = []
            for label in sorted(flow_labels):
                match = re.fullmatch(r'flow\[(\d+)\]::(.*)', label); step = int(match[1]); atom = match[2]
                if atom in {call(k) for k in numeric_keys}: continue
                point = z3.Real('__object_flow_point')
                inside = z3.And(point >= z3.RealVal(str(times[step])), point <= z3.RealVal(str(times[step + 1]))) if step + 1 < len(times) else z3.BoolVal(False)
                state = post[step]
                if atom.startswith('object-code::'):
                    key = tuple(atom[len('object-code::')+1:-1].split()); value = state[('function',)+key]
                    code = 0 if value is None else [o for o,_ in source.objects].index(value)+1
                    wanted = z3.If(inside, code, 0)
                elif atom.startswith('defined(object::'):
                    key = tuple(atom[len('defined(object::')+1:-2].split())
                    wanted = z3.And(inside, state[('function',)+key] is not None)
                else:
                    key = tuple(atom[1:-1].split()); assert key[0] in source.derived
                    # This suite's derived bodies depend on object/basic facts,
                    # which are constant in a segment. Their LFP is recomputed
                    # after each object update by the independent interpreter.
                    wanted = z3.And(inside, bool(state[('predicate',)+key]))
                query = f'(assert (forall ((__object_flow_point Real)) (= (|{aliases[label]}| __object_flow_point) {wanted.sexpr()})))'
                check = z3.Optimize(); check.from_string(raw + '\n' + query)
                extra.append(z3.Not(check.assertions()[-1]))
            wrong += extra
            if function_replacements:
                relation = z3.substitute_funs(relation, *function_replacements)
                wrong = [z3.substitute_funs(t, *function_replacements) for t in wrong]
            if replacements:
                relation = z3.substitute(relation, *replacements)
                wrong = [z3.substitute(t, *replacements) for t in wrong]
            relation = z3.simplify(z3.And(relation, *fixed))
            current = dict(case=name,file=path.name,phase='full-relation',limits=None)
            (root/'object-temporal-current.json').write_text(json.dumps(current)+'\n')
            # Exact quantifier elimination specializes the emitted derivative
            # definition itself, never substitutes a cheaper derivative rule.
            reduced = z3.Tactic('qe')(relation).as_expr() if function_replacements else relation
            solver = z3.Solver(); solver.add(reduced); feasible = solver.check()
            uniqueness = None
            if case['valid']:
                assert feasible == z3.sat, (name, suffix, 'expected point missing', str(feasible),solver.reason_unknown())
                counterexample = z3.And(relation,z3.Or(*wrong))
                if function_replacements: counterexample = z3.Tactic('qe')(z3.simplify(counterexample)).as_expr()
                check=z3.Solver();check.add(counterexample);uniqueness=check.check()
                assert uniqueness == z3.unsat, (name,suffix,'wrong projected tuple',str(uniqueness),str(check.model()) if uniqueness==z3.sat else check.reason_unknown())
            else:
                assert feasible == z3.unsat, (name,suffix,'invalid schedule/witness admitted',str(feasible))
            rows.append(dict(case=name,file=path.name,passed=True,full_point_relation_equivalence=True,
                             independently_valid=case['valid'],actual_feasibility=str(feasible),wrong_tuple_check=str(uniqueness) if uniqueness is not None else None,
                             complete_scalar_observations=len(equalities),entire_numeric_functions=len(function_replacements),entire_object_derived_function_checks=len(extra),
                             target_sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
            (root/'object-temporal-full-relations.json').write_text(json.dumps(dict(passed=len(rows)==2*len(cases),rows=rows,limits=None,
                scope='complete source-observable and signed-objective relation conditioned on each stated rational schedule and entire numeric trajectory witness',
                sampling=False,unrestricted_ode_decision_claim=False),indent=2)+'\n')
    print(json.dumps(dict(passed=True,source_cases=len(cases),complete_relations=len(rows))))

if __name__=='__main__': verify(Path(sys.argv[1]))
