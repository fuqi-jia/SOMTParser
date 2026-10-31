"""Complete joint source-state/plan/signed-cost relation for eight combinations.

Uses the independent name/None/Fraction source interpreter from the object
controls. Soft preference counting and finite modal semantics are evaluated over
source traces here, without importing any frontend or HIR encoding implementation.
Run only on the qualification server; no limits or unknown-as-success policy.
"""
from collections import Counter
from fractions import Fraction
from pathlib import Path
import hashlib
import json
import sys
import z3
from z3.z3util import get_vars
from check_pddl_object_relations import Source, call, typed


class CombinedSource(Source):
    def __init__(self, domain, problem):
        super().__init__(domain, problem)
        self.preferences = []
        self.action_preferences = {}
        self.constraints = []
        self.counts = Counter()
        self.goal = self.strip(self.goal, self.preferences, False)
        ground = []
        for name, args, env, pre, effect in self.ground_actions:
            records = []
            stripped = self.strip(pre, records, False)
            self.action_preferences[(name, args)] = records
            ground.append((name, args, env, stripped, effect))
        self.ground_actions = ground
        for document in (self.domain, self.problem):
            for section in document[2:]:
                if section[0] == ':constraints':
                    self.constraints.append(self.strip(section[1], self.preferences, True))

    def strip(self, expr, records, trajectory, frames=()):
        if not expr: return []
        if expr[0] == 'preference':
            name, body = (expr[1], expr[2]) if len(expr) == 3 else ('', expr[1])
            records.append((name, body, trajectory, frames))
            return ['and']
        if expr[0] == 'and': return ['and'] + [self.strip(x, records, trajectory, frames) for x in expr[1:]]
        if expr[0] == 'forall':
            return ['forall', expr[1], self.strip(expr[2], records, trajectory, frames + (typed(expr[1]),))]
        return expr

    def term(self, expr, state, environment):
        if isinstance(expr, list) and expr and expr[0] == 'is-violated':
            return Fraction(self.counts[expr[1]])
        return super().term(expr, state, environment)

    def modal(self, expr, states, environment):
        if not expr: return True
        op, *args = expr
        if op == 'and': return all(self.modal(x, states, environment) for x in args)
        if op == 'forall':
            return all(self.modal(args[1], states, env) for env in self.environments(typed(args[0]), environment))
        if op == 'at':
            assert args[0] == 'end'
            return self.condition(args[1], states[-1], environment) is True
        if op == 'always': return all(self.condition(args[0], state, environment) is True for state in states)
        if op == 'sometime': return any(self.condition(args[0], state, environment) is True for state in states)
        if op == 'within':
            bound = Fraction(args[0])
            return any(i <= bound and self.condition(args[1], state, environment) is True for i, state in enumerate(states))
        raise AssertionError(('unexpected source modality', op))

    def violations(self, records, states, environment):
        counts = Counter()
        for name, body, trajectory, frames in records:
            environments = [environment]
            for frame in frames:
                environments = [bound for env in environments for bound in self.environments(frame, env)]
            for env in environments:
                satisfied = self.modal(body, states, env) if trajectory else self.condition(body, states[-1], env) is True
                counts[name] += int(not satisfied)
        return counts

    def complete_traces(self, horizon):
        metric, self.metric = self.metric, None
        traces = super().traces(horizon)
        self.metric = metric
        out = []
        for states, plan in traces:
            length = next((i for i, a in enumerate(plan) if a is None), len(plan))
            actual_states = states[:length+1]
            if not all(self.modal(expr, actual_states, {}) for expr in self.constraints): continue
            self.counts = self.violations(self.preferences, actual_states, {})
            for step, selected in enumerate(plan):
                if selected is None: continue
                action = next(a for a in self.ground_actions if tuple([a[0]] + list(a[1])) == selected)
                self.counts += self.violations(self.action_preferences[(action[0], action[1])], states[:step+1], action[2])
            assert metric is not None
            base = self.term(metric[1], states[-1], {})
            if base is None: continue
            signed = (base if metric[0] == 'minimize' else -base) + self.counts['']
            out.append((states, plan, signed))
        return out


def verify(root):
    expected = {'goal_object_cost', 'action_old_object_cost', 'goal_undefined_cost', 'quantified_object_cost',
                'trajectory_object_cost', 'derived_trajectory_cost', 'guard_old_preference', 'anonymous_object_cost'}
    ledger = [line.split('\t') for line in (root/'object-combined-controls.tsv').read_text().splitlines()]
    assert len(ledger) == 8 and {n for n, _, _ in ledger} == expected
    rows = []
    for name, horizon, accepted in ledger:
        assert accepted == '1'
        domain = root/(name+'.domain.pddl'); problem = root/(name+'.problem.pddl')
        source = CombinedSource(domain.read_text(), problem.read_text())
        traces = source.complete_traces(int(horizon)); assert traces, name
        aliases = dict(line.split('\t') for line in (root/(name+'.tsv')).read_text().splitlines())
        choices = [line.split('\t') for line in (root/(name+'.choices.tsv')).read_text().splitlines()]
        signed = z3.Real('__independent_object_preference_signed_cost')
        branches = []
        for states, plan, cost in traces:
            values = {}
            for step, state in enumerate(states):
                prefix = f'state[{step}]::'
                for key in source.pkeys: values[prefix+call(key)] = state[('predicate',)+key]
                for key, typ in source.fkeys.items():
                    value = state[('function',)+key]
                    if typ == 'number':
                        stem = ('numeric::' if key[0] in source.predicates else '')+call(key)
                        values[prefix+stem] = Fraction(0) if value is None else value
                        values[prefix+'defined('+stem+')'] = value is not None
                    else:
                        values[prefix+'object-code::'+call(key)] = 0 if value is None else [n for n, _ in source.objects].index(value)+1
                        values[prefix+'defined(object::'+call(key)+')'] = value is not None
            for step, selected in enumerate(plan):
                for action in source.ground_actions:
                    key = tuple([action[0]]+list(action[1]))
                    values[f'choice[{step}]::'+call(key)] = selected == key
            assert set(values) == set(aliases), (name, set(values)^set(aliases))
            facts = [signed == z3.RealVal(str(cost))]
            for label, value in values.items():
                ctor = z3.Bool if isinstance(value, bool) else z3.Real if isinstance(value, Fraction) else z3.Int
                facts.append(ctor(aliases[label]) == value)
            expected_choices = set()
            for step, state in enumerate(states):
                for key, typ in source.fkeys.items():
                    if typ == 'number': continue
                    label = f'state[{step}]::object::'+call(key)
                    expected_choices.add((label, 'undefined'))
                    expected_choices.update((label, obj) for obj, actual in source.objects if source.subtype(actual, typ))
            for step in range(int(horizon)):
                expected_choices.add((f'plan[{step}]', '__pddl_padding_noop'))
                expected_choices.update((f'plan[{step}]', call(tuple([a[0]]+list(a[1])))) for a in source.ground_actions)
            assert len(choices) == len(expected_choices)
            assert {(label, value) for label, value, _ in choices} == expected_choices
            for label, alternative, target in choices:
                if label.startswith('plan['):
                    selected = plan[int(label[5:-1])]
                    truth = alternative == ('__pddl_padding_noop' if selected is None else call(selected))
                else:
                    step = int(label.split(']')[0][6:])
                    key = tuple(label.split('::object::(')[1][:-1].split())
                    value = states[step][('function',)+key]
                    truth = alternative == ('undefined' if value is None else value)
                facts.append(z3.Bool(target) == truth)
            branches.append(z3.And(*facts))
        oracle = z3.Or(*branches)
        observed = set(aliases.values()) | {t for _, _, t in choices} | {str(signed)}
        for suffix in ('.smt2', '.internal.smt2'):
            path = root/(name+suffix)
            opt = z3.Optimize(); opt.from_file(str(path)); assert len(opt.objectives()) == 1
            actual = z3.And(*opt.assertions(), signed == opt.objectives()[0])
            hidden = [v for v in get_vars(actual) if str(v) not in observed]
            if hidden: actual = z3.Exists(hidden, actual)
            solver = z3.Solver(); solver.add(z3.Xor(actual, oracle)); answer = solver.check()
            row = dict(case=name,file=path.name,source_traces=len(traces),full_relation_and_signed_cost=str(answer),
                       target_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                       source_sha256={'domain':hashlib.sha256(domain.read_bytes()).hexdigest(),'problem':hashlib.sha256(problem.read_bytes()).hexdigest()})
            if answer != z3.unsat: row['diagnostic'] = str(solver.model()) if answer == z3.sat else solver.reason_unknown()
            rows.append(row)
            (root/'object-combined-partial.json').write_text(json.dumps(rows,indent=2)+'\n')
            assert answer == z3.unsat, row
    result = dict(passed=True,cases=rows,source_cases=8,limits=None,scope='complete bounded joint object/numeric/preference/trajectory relation and signed cost')
    (root/'object-combined-full-relations.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))


if __name__ == '__main__': verify(Path(sys.argv[1]))
