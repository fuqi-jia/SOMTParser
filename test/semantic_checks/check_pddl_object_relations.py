"""Independent finite source interpreter and complete exported-relation checks.

Run only on the qualification server. No solver limits, sampling, or SAT-only
comparison. This fixture interpreter stores Python object names/None, never HIR
codes. It enumerates every bounded source trace including suffix padding. SMT
codes are introduced only when comparing the explicit source signature.
"""
from fractions import Fraction
from itertools import product
from pathlib import Path
import hashlib
import json
import re
import sys
import z3
from z3.z3util import get_vars


def read(source):
    tokens = re.findall(r'[^\s()]+|[()]', re.sub(r';[^\n]*', '', source).lower())
    stack, top = [], []
    for token in tokens:
        if token == '(':
            node = []
            (stack[-1] if stack else top).append(node)
            stack.append(node)
        elif token == ')':
            assert stack
            stack.pop()
        else:
            assert stack
            stack[-1].append(token)
    assert not stack and len(top) == 1
    return top[0]


def typed(items, default='object'):
    out, pending = [], []
    at = 0
    while at < len(items):
        if items[at] == '-':
            typ = items[at+1]
            out += [(name, typ) for name in pending]
            pending = []
            at += 2
        else:
            pending.append(items[at]); at += 1
    return out + [(name, default) for name in pending]


def call(key):
    return '(' + ' '.join(key) + ')'


class Source:
    def __init__(self, domain, problem):
        self.domain, self.problem = read(domain), read(problem)
        sections = self.domain[2:]
        self.parents = {'object': []}
        self.objects, self.predicates, self.functions, self.rules, self.actions = [], {}, {}, [], []
        self.initial, self.goal, self.metric = [], [], None
        for sec in sections:
            if sec[0] == ':types':
                for name, typ in typed(sec[1:]): self.parents[name] = [typ]
            elif sec[0] == ':constants': self.objects += typed(sec[1:])
            elif sec[0] == ':predicates':
                for declaration in sec[1:]: self.predicates[declaration[0]] = typed(declaration[1:])
            elif sec[0] == ':functions':
                for declaration, result in typed(sec[1:], 'number'):
                    self.functions[declaration[0]] = (typed(declaration[1:]), result)
            elif sec[0] == ':derived': self.rules.append((sec[1], sec[2]))
            elif sec[0] == ':action':
                fields = dict(zip(sec[2::2], sec[3::2]))
                self.actions.append((sec[1], typed(fields[':parameters']), fields.get(':precondition', []), fields.get(':effect', [])))
        for sec in self.problem[2:]:
            if sec[0] == ':objects': self.objects += typed(sec[1:])
            elif sec[0] == ':init': self.initial = sec[1:]
            elif sec[0] == ':goal': self.goal = sec[1]
            elif sec[0] == ':metric': self.metric = (sec[1], sec[2])
        self.object_types = dict(self.objects)
        self.derived = {head[0] for head, _ in self.rules}
        self.pkeys = [tuple([name] + list(args)) for name, params in self.predicates.items() for args in self.tuples(params)]
        self.fkeys = {tuple([name] + list(args)): result for name, (params, result) in self.functions.items() for args in self.tuples(params)}
        self.ground_actions = [(name, tuple(args), dict(zip((v for v, _ in params), args)), pre, effect)
                               for name, params, pre, effect in self.actions for args in self.tuples(params)]

    def subtype(self, actual, expected):
        if isinstance(expected, list): return any(self.subtype(actual, t) for t in expected[1:])
        return actual == expected or any(self.subtype(parent, expected) for parent in self.parents[actual])

    def tuples(self, params):
        return product(*[[name for name, actual in self.objects if self.subtype(actual, typ)] for _, typ in params])

    def environments(self, params, environment):
        for args in self.tuples(params): yield dict(environment, **dict(zip((v for v, _ in params), args)))

    def term(self, term, state, environment):
        if isinstance(term, str):
            if term.startswith('?'): return environment[term]
            try: return Fraction(term)
            except ValueError: pass
            if term in self.functions and self.functions[term][1] == 'number': return state.get(('function', term))
            assert term in self.object_types, term
            return term
        op, *args = term
        values = [self.term(t, state, environment) for t in args]
        if any(v is None for v in values): return None
        if op in ('+', '-', '*', '/'):
            if op == '+': return values[0] + values[1]
            if op == '-': return -values[0] if len(values) == 1 else values[0] - values[1]
            if op == '*': return values[0] * values[1]
            return None if values[1] == 0 else values[0] / values[1]
        assert op in self.functions
        return state.get(tuple(['function', op] + values))

    def condition(self, expression, state, environment):
        if not expression: return True
        op, *args = expression
        if op in ('and', 'or', 'not', 'imply'):
            values = [self.condition(t, state, environment) for t in args]
            # The recorded STRICT policy propagates definedness independently
            # of Boolean short circuit, matching numeric precondition rules.
            if any(v is None for v in values): return None
            if op == 'and': return all(values)
            if op == 'or': return any(values)
            if op == 'not': return not values[0]
            return not values[0] or values[1]
        if op in ('forall', 'exists'):
            values = [self.condition(args[1], state, bound) for bound in self.environments(typed(args[0]), environment)]
            if any(v is None for v in values): return None
            return all(values) if op == 'forall' else any(values)
        if op in ('=', '<', '<=', '>', '>='):
            left, right = [self.term(t, state, environment) for t in args]
            if left is None or right is None: return None
            return {'=': lambda: left == right, '<': lambda: left < right, '<=': lambda: left <= right,
                    '>': lambda: left > right, '>=': lambda: left >= right}[op]()
        values = [self.term(t, state, environment) for t in args]
        if any(v is None for v in values): return None
        return bool(state.get(tuple(['predicate', op] + values), False))

    def closure(self, basic):
        state = dict(basic)
        for key in self.pkeys:
            if key[0] in self.derived: state[('predicate',) + key] = False
        while True:
            new = dict(state)
            for head, body in self.rules:
                params = self.predicates[head[0]]
                variables = [v for v, _ in typed(head[1:])]
                for args in self.tuples(params):
                    key = tuple([head[0]] + list(args))
                    if self.condition(body, state, dict(zip(variables, args))) is True: new[('predicate',) + key] = True
            if new == state: return state
            state = new

    def start(self):
        state = {('predicate',) + key: False for key in self.pkeys}
        state.update({('function',) + key: None for key in self.fkeys})
        for literal in self.initial:
            if literal[0] == '=':
                target = [literal[1]] if isinstance(literal[1], str) else literal[1]
                key = tuple(target)
                state[('function',) + key] = Fraction(literal[2]) if self.fkeys[key] == 'number' else literal[2]
            elif literal[0] == 'not': state[('predicate',) + tuple(literal[1])] = False
            else: state[('predicate',) + tuple(literal)] = True
        return self.closure(state)

    def step(self, state, action):
        _, _, env, pre, effect = action
        if self.condition(pre, state, env) is not True: return None
        writes, additions, deletions = {}, set(), set()
        def effects(expr, environment):
            if not expr: return True
            op, *args = expr
            if op == 'and': return all(effects(x, environment) for x in args)
            if op == 'forall': return all(effects(args[1], e) for e in self.environments(typed(args[0]), environment))
            if op == 'when':
                guard = self.condition(args[0], state, environment)
                return guard is not None and (not guard or effects(args[1], environment))
            if op in ('assign', 'increase', 'decrease', 'scale-up', 'scale-down'):
                address = [self.term(t, state, environment) for t in args[0][1:]]
                if any(x is None for x in address): return False
                key = tuple([args[0][0]] + address)
                value = None if args[1] == 'undefined' else self.term(args[1], state, environment)
                if value is None and args[1] != 'undefined': return False
                writes.setdefault(key, []).append((op, value))
                return True
            atom = args[0] if op == 'not' else expr
            address = [self.term(t, state, environment) for t in atom[1:]]
            if any(x is None for x in address): return False
            (deletions if op == 'not' else additions).add(tuple([atom[0]] + address))
            return True
        if not effects(effect, env): return None
        successor = dict(state)
        for key, changes in writes.items():
            if self.fkeys[key] != 'number':
                if len(changes) != 1: return None  # Explicit SINGLE_WRITER.
                successor[('function',) + key] = changes[0][1]
                continue
            additive = all(op in ('increase', 'decrease') for op, _ in changes)
            if len(changes) > 1 and not additive: return None
            if additive:
                if state[('function',) + key] is None: return None
                successor[('function',) + key] = state[('function',) + key] + sum(v if op == 'increase' else -v for op, v in changes)
            else:
                op, value = changes[0]
                if op == 'assign': successor[('function',) + key] = value
                else:
                    if state[('function',) + key] is None or op == 'scale-down' and value == 0: return None
                    successor[('function',) + key] = state[('function',) + key] * value if op == 'scale-up' else state[('function',) + key] / value
        for key in deletions: successor[('predicate',) + key] = False
        for key in additions: successor[('predicate',) + key] = True
        return self.closure(successor)

    def traces(self, horizon):
        frontier = [([self.start()], [], False)]
        for _ in range(horizon):
            next_frontier = []
            for states, choices, padded in frontier:
                next_frontier.append((states + [states[-1]], choices + [None], True))
                if not padded:
                    for action in self.ground_actions:
                        successor = self.step(states[-1], action)
                        if successor is not None:
                            next_frontier.append((states + [successor], choices + [tuple([action[0]] + list(action[1]))], False))
            frontier = next_frontier
        return [(states, choices) for states, choices, _ in frontier
                if self.condition(self.goal, states[-1], {}) is True
                and (not self.metric or self.term(self.metric[1], states[-1], {}) is not None)]


def verify(root):
    rows = []
    ledger = [line.split('\t') for line in (root / 'object-source-controls.tsv').read_text().splitlines()]
    assert len(ledger) == len({name for name, _, _ in ledger})
    expected = {'empty': ('0', '1'), 'initial': ('0', '1'), 'nested': ('0', '1'), 'predicate_dynamic': ('0', '1'), 'predicate_dynamic_false': ('0', '1'), 'undefined_not': ('0', '1'), 'undefined_or': ('0', '1'), 'undefined_imply': ('0', '1'), 'undefined_predicate': ('0', '1'), 'undefined_exists': ('0', '1'), 'assign': ('1', '1'), 'reset': ('1', '1'), 'rhs_undefined': ('1', '1'), 'swap': ('1', '1'), 'old_address': ('1', '1'), 'undefined_address': ('1', '1'), 'alias_conflict': ('1', '1'), 'disjoint_writes': ('1', '1'), 'predicate_address': ('1', '1'), 'predicate_undefined_address': ('1', '1'), 'guard_false': ('1', '1'), 'guard_undefined': ('1', '1'), 'guard_old': ('1', '1'), 'forall_assign': ('1', '1'), 'forall_alias_conflict': ('1', '1'), 'two_steps': ('2', '1'), 'goal_after': ('2', '1'), 'derived_dynamic': ('1', '1'), 'derived_nested_recursion': ('1', '1'), 'empty_argument': ('1', '1'), 'empty_result': ('0', '1'), 'union_return': ('1', '1'), 'grouped_return': ('0', '1'), 'numeric_dynamic': ('0', '1'), 'numeric_selected_undefined': ('0', '1'), 'numeric_address_undefined': ('0', '1'), 'numeric_old_address': ('1', '1'), 'numeric_guard_false': ('1', '1'), 'numeric_initialize_undefined': ('1', '1'), 'metric_minimize': ('1', '1'), 'metric_maximize': ('1', '1'), 'nullary_numeric': ('1', '1'), 'same_predicate_function': ('1', '1'), 'bad_requirement': ('0', '0'), 'bad_return': ('0', '0'), 'bad_numeric_object_mixed': ('0', '0'), 'bad_term_undefined': ('0', '0'), 'bad_object_operator': ('0', '0'), 'bad_rhs_type': ('0', '0'), 'bad_dynamic_argument': ('0', '0'), 'bad_nested_arity': ('0', '0'), 'bad_init_nested': ('0', '0'), 'bad_init_undefined': ('0', '0'), 'bad_init_duplicate': ('0', '0'), 'bad_free_variable': ('0', '0'), 'bad_derived_effect': ('0', '0'), 'bad_temporal': ('0', '1'), 'bad_boolean_return': ('0', '0'), 'bad_function_duplicate': ('0', '0'), 'official_blocks': ('1', '1'), 'official_logistics': ('1', '1'), 'official_depots': ('1', '0')}
    assert {n: (h, a) for n, h, a in ledger} == expected

    for name, horizon, accepted in ledger:
        if accepted != '1':
            assert (root / 'rejected' / (name + '.diagnostics.txt')).read_text().strip()
            rows.append({'case': name, 'rejected': True}); continue
        source = Source((root / (name + '.domain.pddl')).read_text(), (root / (name + '.problem.pddl')).read_text())
        traces = source.traces(int(horizon))
        aliases = dict(line.split('\t') for line in (root / (name + '.tsv')).read_text().splitlines())
        choices = [line.split('\t') for line in (root / (name + '.choices.tsv')).read_text().splitlines()]
        expected_labels = set()
        expected_choices = set()
        for step in range(int(horizon) + 1):
            prefix = f'state[{step}]::'
            expected_labels.update(prefix + call(key) for key in source.pkeys)
            for key, typ in source.fkeys.items():
                if typ == 'number':
                    stem = ('numeric::' if key[0] in source.predicates else '') + call(key)
                    expected_labels.update((prefix + stem, prefix + 'defined(' + stem + ')'))
                else:
                    expected_labels.update((prefix + 'object-code::' + call(key), prefix + 'defined(object::' + call(key) + ')'))
                    expected_choices.add((prefix + 'object::' + call(key), 'undefined'))
                    for obj, actual in source.objects:
                        if source.subtype(actual, typ): expected_choices.add((prefix + 'object::' + call(key), obj))
            if step < int(horizon):
                for action in source.ground_actions:
                    action_label = call(tuple([action[0]] + list(action[1])))
                    expected_labels.add(f'choice[{step}]::' + action_label)
                    expected_choices.add((f'plan[{step}]', action_label))
                expected_choices.add((f'plan[{step}]', '__pddl_padding_noop'))
        assert set(aliases) == expected_labels, (name, set(aliases) ^ expected_labels)
        assert {(label, value) for label, value, _ in choices} == expected_choices, name
        assert len(choices) == len(expected_choices), name
        sorts, reference_terms, objectives = {}, [], []
        for states, plan in traces:
            coordinates = {}
            for step, state in enumerate(states):
                prefix = f'state[{step}]::'
                for key in source.pkeys: coordinates[prefix + call(key)] = bool(state[('predicate',) + key])
                for key, typ in source.fkeys.items():
                    value = state[('function',) + key]
                    if typ == 'number':
                        stem = ('numeric::' if key[0] in source.predicates else '') + call(key)
                        coordinates[prefix + stem] = Fraction(0) if value is None else value
                        coordinates[prefix + 'defined(' + stem + ')'] = value is not None
                    else:
                        coordinates[prefix + 'object-code::' + call(key)] = 0 if value is None else [n for n, _ in source.objects].index(value) + 1
                        coordinates[prefix + 'defined(object::' + call(key) + ')'] = value is not None
            for step, selected in enumerate(plan):
                for action in source.ground_actions:
                    key = tuple([action[0]] + list(action[1]))
                    coordinates[f'choice[{step}]::' + call(key)] = selected == key
            assert set(coordinates) == set(aliases), (name, set(coordinates) ^ set(aliases))
            facts = []
            for label, value in coordinates.items():
                symbol = aliases[label]
                ctor = z3.Bool if isinstance(value, bool) else z3.Real if isinstance(value, Fraction) else z3.Int
                sorts[symbol] = ctor
                facts.append(ctor(symbol) == value)
            for label, alternative, target in choices:
                if label.startswith('plan['):
                    step = int(label[5:-1]); selected = plan[step]
                    truth = alternative == ('__pddl_padding_noop' if selected is None else call(selected))
                else:
                    match = re.fullmatch(r'state\[(\d+)\]::object::\((.*)\)', label)
                    assert match, label
                    value = states[int(match[1])][('function',) + tuple(match[2].split())]
                    truth = alternative == ('undefined' if value is None else value)
                sorts[target] = z3.Bool
                facts.append(z3.Bool(target) == truth)
            reference_terms.append(z3.And(*facts))
            if source.metric:
                value = source.term(source.metric[1], states[-1], {})
                objectives.append(value if source.metric[0] == 'minimize' else -value)
        oracle = z3.Or(*reference_terms)
        observed = set(aliases.values()) | {target for _, _, target in choices}
        for suffix in ('.smt2', '.internal.smt2'):
            path = root / (name + suffix)
            optimizer = z3.Optimize(); optimizer.from_file(str(path))
            target = z3.And(*optimizer.assertions())
            hidden = [v for v in get_vars(target) if str(v) not in observed]
            projected = z3.Exists(hidden, target) if hidden else target
            solver = z3.Solver(); solver.add(z3.Xor(projected, oracle)); result = solver.check()
            row = {'case': name, 'file': path.name, 'traces': len(traces), 'full_relation_xor': str(result),
                   'objectives': len(optimizer.objectives()), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
            if result != z3.unsat:
                row['diagnostic'] = str(solver.model()) if result == z3.sat else solver.reason_unknown()
                (root / 'object-oracle-failure.json').write_text(json.dumps(row, indent=2) + '\n')
                raise AssertionError(row)
            assert len(optimizer.objectives()) == bool(source.metric), row
            for reference, expected in zip(reference_terms, objectives):
                checker = z3.Solver(); checker.add(target, reference, optimizer.objectives()[0] != expected)
                assert checker.check() == z3.unsat, (name, 'signed objective mismatch', expected)
            rows.append(row)
    summary = {'passed': True, 'limits': None, 'scope': 'complete bounded sequential strict-undefined single-writer source relation', 'cases': rows}
    (root / 'object-full-relations.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary))


if __name__ == '__main__': verify(Path(sys.argv[1]))
