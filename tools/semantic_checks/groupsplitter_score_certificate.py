"""Checked score upper bound for the one-group MiniZinc groupsplitter family.

A single group forces all users to share the same activity in each phase.
The full literal activity and preference relations determine each phase's
score. Enumerating these finite columns gives independent phase maxima; their
sum bounds the complete objective. Temporal and other constraints can only
restrict this relaxation. This is an objective bound, not relation equivalence.
"""
import hashlib
import json
import re

import z3

from .source_oracles.ozn_observations import lex, split
from .source_oracles.target_relation import read_target


def need(value, message):
    if not value:
        raise ValueError(message)


def digest(value):
    return hashlib.sha256(value).hexdigest()


REQUIRED = {
    'users': 'set of int: user_ids;',
    'groups': 'set of int: group_ids;',
    'phase1': 'set of int: activity1_ids;',
    'phase2': 'set of int: activity2_ids;',
    'eta': 'int: eta;',
    'rating_domain': 'set of int: pub_rating_domain = 0..5;',
    'weight_domain': 'set of int: user_rating_domain = -2..2;',
    'objective_declaration': 'var objlb..objub: objective;',
    'objective': '''constraint objective = (eta * sum(user_weight_map1) +
        (10-eta) * sum(user_pub_rating_map1) + (10-eta) * sum(user_pub_rating_map2) +
        eta * sum(user_weight_map2));''',
}
for phase in (1, 2):
    REQUIRED.update({
        f'activities{phase}': f'array[activity{phase}_ids,1..5] of int: activities{phase};',
        f'preferences{phase}': f'array[user_ids,activity{phase}_ids] of user_rating_domain: preferences{phase};',
        f'group_map{phase}': f'array[user_ids] of var group_ids: user_group_map{phase};',
        f'group_activity{phase}': f'array[group_ids] of var activity{phase}_ids: group_act_map{phase};',
        f'user_activity{phase}': f'array[user_ids] of var activity{phase}_ids: user_act_map{phase};',
        f'user_rating{phase}': f'array[user_ids] of var pub_rating_domain: user_pub_rating_map{phase};',
        f'user_weight{phase}': f'array[user_ids] of var user_rating_domain: user_weight_map{phase};',
        f'activity_relation{phase}': f'''array[activity{phase}_ids,1..6] of int: activities{phase}_data =
            array2d(activity{phase}_ids,1..6,[if i=1 then j else activities{phase}[j,i-1] endif |
            j in activity{phase}_ids, i in 1..6]);''',
        f'preference_relation{phase}': f'''array[1..max(user_ids)*max(activity{phase}_ids),1..3] of int:
            preferences{phase}_data = array2d(1..max(user_ids)*max(activity{phase}_ids),1..3,
            [if k=1 then i else if k=2 then j else preferences{phase}[i,j] endif endif |
            i in user_ids,j in activity{phase}_ids,k in 1..3]);''',
        f'activity_table{phase}': f'''constraint forall(i in user_ids)(table([
            user_act_map{phase}[i], activity_available_from{phase}[i], user_end_map{phase}[i],
            user_duration_map{phase}[i], user_cell_map{phase}[i], user_pub_rating_map{phase}[i]],
            activities{phase}_data));''',
        f'preference_table{phase}': f'''constraint forall(i in user_ids)(table([
            i,user_act_map{phase}[i],user_weight_map{phase}[i]],preferences{phase}_data));''',
        f'channel{phase}': f'''constraint forall(i in user_ids)(
            user_act_map{phase}[i] = group_act_map{phase}[user_group_map{phase}[i]]);''',
    })
DATA_NAMES = frozenset(['user_ids', 'group_ids', 'activity1_ids', 'activity2_ids',
    'cell_ids', 'time_slot_ids', 'min_group_size', 'usersn', 'max_wait', 'startAfter',
    'eta', 'activities1', 'activities2', 'preferences1', 'preferences2',
    'oid1', 'oid2', 'distances'])


def source_facts(source, data):
    tokens, data_tokens = lex(source.decode()), lex(data.decode())
    for stream in (tokens, data_tokens):
        need(not any((a, b) in [('/', '*'), ('*', '/')] for a, b in zip(stream, stream[1:])),
             'block comments outside this narrow source checker scope')
    need(not any(token.startswith("'") for token in tokens), 'quoted source identifiers unsupported')
    statements = [tuple(s) for s in split(tokens, ';') if s]
    for s in statements:
        need(s[0] not in ['function', 'predicate', 'test', 'type', 'enum', 'annotation'],
             'custom source definitions unsupported')
        need(s[0] != 'include' or s in [('include', '"count.mzn"'), ('include', '"table.mzn"')],
             'only standard count/table includes supported')
        need(len(s) < 2 or s[1] != '=', 'extra source assignment unsupported')
    matched = {}
    for label, template in REQUIRED.items():
        expected = tuple(lex(template)[:-1])
        need(statements.count(expected) == 1, 'unsupported source clause: ' + label)
        matched[label] = statements.index(expected)
    solves = [s for s in statements if s[0] == 'solve']
    need(len(solves) == 1 and solves[0][-2:] == ('maximize', 'objective'),
         'one complete maximized objective required')
    assignments = {}
    for s in [s for s in split(data_tokens, ';') if s]:
        need(len(s) > 2 and s[1] == '=' and re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', s[0]),
             'ordinary data assignment required')
        need(s[0] in DATA_NAMES and s[0] not in assignments, 'unknown or duplicate data input')
        assignments[s[0]] = s[2:]
    def integer_tokens(t):
        need((len(t) == 1 and re.fullmatch(r'\d+', t[0])) or
             (len(t) == 2 and t[0] in ['+', '-'] and re.fullmatch(r'\d+', t[1])),
             'literal integer required')
        return int(''.join(t))
    def domain(name):
        t = assignments.get(name, [])
        need(len(t) == 3 and t[:2] == ['1', '..'] and re.fullmatch(r'\d+', t[2]) and int(t[2]) > 0,
             'one-based nonempty contiguous domain required: ' + name)
        return int(t[2])
    users, groups = domain('user_ids'), domain('group_ids')
    need(groups == 1, 'single group required')
    counts = [domain('activity1_ids'), domain('activity2_ids')]
    eta = integer_tokens(assignments.get('eta', []))
    need(0 <= eta <= 10, 'eta outside supported nonnegative score weights')
    def matrix(name, nr, nc):
        t = assignments.get(name, [])
        need(t[:2] == ['[', '|'] and t[-2:] == ['|', ']'], 'plain literal matrix required: ' + name)
        rows = []
        for r in split(t[2:-2], '|'):
            cells = split(r, ',')
            if cells and not cells[-1]:
                cells.pop()
            need(cells and all(cells), 'empty matrix cell')
            rows.append([integer_tokens(c) for c in cells])
        need(len(rows) == nr and all(len(r) == nc for r in rows), 'matrix shape mismatch: ' + name)
        return rows
    activities, preferences, scores = [], [], []
    for phase, count in zip((1, 2), counts):
        a = matrix(f'activities{phase}', count, 5)
        p = matrix(f'preferences{phase}', users, count)
        need(all(0 <= r[4] <= 5 for r in a), 'public rating outside source domain')
        need(all(-2 <= x <= 2 for r in p for x in r), 'preference outside source domain')
        activities.append(a)
        preferences.append(p)
        scores.append([eta * sum(p[u][j] for u in range(users)) + (10-eta)*users*a[j][4]
                       for j in range(count)])
    return dict(users=users, counts=counts, eta=eta, activities=activities, preferences=preferences,
                phase_scores=scores, phase_upper_bounds=[max(s) for s in scores],
                source_clause_indices=matched)


def _canonical(expr):
    """Exact scalar syntax normalization; never traverse finite table arrays."""
    memo = {}
    def visit(n):
        k = n.get_id()
        if k in memo:
            return memo[k]
        if z3.is_int_value(n):
            result = ('int', n.as_long())
        elif z3.is_true(n) or z3.is_false(n):
            result = ('bool', z3.is_true(n))
        elif z3.is_const(n) and n.decl().kind() == z3.Z3_OP_UNINTERPRETED:
            result = ('symbol', str(n.decl().name()), str(n.sort()))
        else:
            need(z3.is_app(n), 'binder in required scalar clause')
            op, children = n.decl().kind(), list(n.children())
            if op in (z3.Z3_OP_AND, z3.Z3_OP_OR, z3.Z3_OP_ADD):
                work, values = children[:], []
                while work:
                    child = work.pop()
                    if z3.is_app_of(child, op):
                        work.extend(child.children())
                    else:
                        values.append(visit(child))
                result = (op, tuple(sorted(values, key=repr)))
            else:
                if op in (z3.Z3_OP_GE, z3.Z3_OP_GT):
                    children.reverse()
                    op = z3.Z3_OP_LE if op == z3.Z3_OP_GE else z3.Z3_OP_LT
                values = [visit(child) for child in children]
                if op in (z3.Z3_OP_EQ, z3.Z3_OP_MUL):
                    values.sort(key=repr)
                result = (op, tuple(values))
        memo[k] = result
        return result
    return visit(z3.simplify(expr))


def _finite_relation(array, arity):
    """Decode the entire Store/K relation, including defaults and overwrites.

    Every infinite default branch must denote false. A true/default-true or
    symbolic branch is rejected, never ignored as an out-of-range value.
    Memoize completed array roots, not every prefix of a Store chain.
    """
    memo = {}
    def decode(node, depth):
        ident = (node.get_id(), depth)
        if ident in memo:
            return memo[ident][1]
        if depth == 0:
            need(z3.is_true(node) or z3.is_false(node), 'nonliteral relation leaf')
            return z3.is_true(node)
        need(node.sort().kind() == z3.Z3_ARRAY_SORT and node.sort().domain().kind() == z3.Z3_INT_SORT,
             'relation must have integer array indices')
        current, writes = node, {}
        while z3.is_store(current):
            base, key, value = current.children()
            key = z3.simplify(key)  # SMT negative numerals parse as unary minus.
            need(z3.is_int_value(key), 'symbolic relation store key')
            writes.setdefault(key.as_long(), value)  # outer write wins
            current = base
        need(z3.is_const_array(current), 'only Store/K relations supported')
        default = decode(current.arg(0), depth-1)
        need(not default, 'infinite nonempty relation default unsupported')
        result = {}
        for key, value in writes.items():
            decoded = decode(value, depth-1)
            if decoded:
                result[key] = decoded
        memo[ident] = (node, result)
        return result
    trie = decode(array, arity)
    tuples = set()
    def walk(node, prefix):
        if len(prefix) == arity:
            need(node is True, 'nonboolean relation support')
            tuples.add(prefix)
        else:
            for key, child in node.items():
                walk(child, prefix+(key,))
    walk(trie, ())
    return tuples


def check_groupsplitter_score_bound(source, data, target):
    facts = source_facts(source, data)
    variables, program, directions = read_target(target)
    need('objective' in variables and variables['objective'].sort().kind() == z3.Z3_INT_SORT,
         'integer target objective required')
    objective = variables['objective']
    need(directions == ['maximize'] and len(program.objectives()) == 1 and
         z3.eq(z3.simplify(program.objectives()[0]), z3.simplify(-objective)),
         'complete target maximized objective changed')
    users = range(1, facts['users']+1)
    names = [f'{stem}{p}' for p in (1, 2) for stem in ['user_group_map', 'group_act_map',
        'user_act_map', 'activity_available_from', 'user_end_map', 'user_duration_map',
        'user_cell_map', 'user_pub_rating_map', 'user_weight_map']]
    array_sort = z3.ArraySort(z3.IntSort(ctx=program.ctx), z3.IntSort(ctx=program.ctx))
    need(all(n in variables and variables[n].sort() == array_sort for n in names),
         'target score observation arrays/sorts changed')
    rows = []
    def flatten(node, index, path):
        if z3.is_and(node):
            for i, child in enumerate(node.children()):
                flatten(child, index, path+[i])
        else:
            rows.append((node, dict(assertion=index, conjunct_path=path)))
    assertions = list(program.assertions())
    for i, node in enumerate(assertions):
        flatten(node, i, [])
    scalar_index, relation_index = {}, {}
    for node, origin in rows:
        current, args = node, []
        while z3.is_select(current):
            args.append(current.arg(1))
            current = current.arg(0)
        if args and node.sort().kind() == z3.Z3_BOOL_SORT:
            args.reverse()
            key = tuple(_canonical(a) for a in args)
            relation_index.setdefault(key, []).append((current, origin))
        else:
            # Extra quantifiers constrain the full model, but are never used
            # as premises for this finite score bound.
            if not z3.is_quantifier(node):
                scalar_index.setdefault(_canonical(node), []).append(origin)
    checks = []
    def require(label, expected):
        found = scalar_index.get(_canonical(expected))
        need(found, 'missing complete target clause: ' + label)
        checks.append(dict(label=label, actual_original_clause=found[0]))
    relation_cache = {}
    def require_table(label, args, expected):
        candidates = relation_index.get(tuple(_canonical(a) for a in args), [])
        need(candidates, 'missing complete target table: ' + label)
        for array, origin in candidates:
            ident = (array.get_id(), len(args))
            if ident not in relation_cache:
                relation_cache[ident] = (array, _finite_relation(array, len(args)))
            actual = relation_cache[ident][1]
            if actual == expected:
                checks.append(dict(label=label, actual_original_clause=origin, complete_relation_tuples=len(actual),
                    relation_sha256=digest(json.dumps(sorted(actual), separators=(',', ':')).encode())))
                return
        raise ValueError('complete target table differs from source: ' + label)
    terms = []
    for phase, count in zip((1, 2), facts['counts']):
        get = lambda stem, u: z3.Select(variables[f'{stem}{phase}'], u)
        activity_rows = {(j+1, *row) for j, row in enumerate(facts['activities'][phase-1])}
        preference_rows = {(u, j+1, value) for u, row in enumerate(facts['preferences'][phase-1], 1)
                           for j, value in enumerate(row)}
        for u in users:
            group = get('user_group_map', u)
            require(f'phase-{phase}-user-{u}-group-lower', group >= 1)
            require(f'phase-{phase}-user-{u}-group-upper', group <= 1)
            require(f'phase-{phase}-user-{u}-shared-activity',
                    get('user_act_map', u) == z3.Select(variables[f'group_act_map{phase}'], group))
            require_table(f'phase-{phase}-user-{u}-activity', [get(stem, u) for stem in ['user_act_map',
                'activity_available_from', 'user_end_map', 'user_duration_map', 'user_cell_map', 'user_pub_rating_map']], activity_rows)
            require_table(f'phase-{phase}-user-{u}-preference', [z3.IntVal(u, ctx=program.ctx),
                get('user_act_map', u), get('user_weight_map', u)], preference_rows)
        terms.extend([facts['eta']*z3.Sum([get('user_weight_map', u) for u in users]),
                      (10-facts['eta'])*z3.Sum([get('user_pub_rating_map', u) for u in users])])
    require('complete-score-objective', objective == z3.Sum(terms))
    upper = sum(facts['phase_upper_bounds'])
    return dict(passed=True, kind='checked-one-group-score-upper-bound', upper_bound=upper,
        source_upper_bound=upper, target_upper_bound=upper, phase_upper_bounds=facts['phase_upper_bounds'],
        users=facts['users'], activity_counts=facts['counts'], eta=facts['eta'],
        source_sha256=digest(source), data_sha256=digest(data), target_sha256=digest(target),
        source_clause_indices=facts['source_clause_indices'], target_checks=checks,
        phase_score_vectors=facts['phase_scores'], original_target_assertions=len(assertions),
        original_target_conjuncts=len(rows), target_objective_directions=directions,
        target_objective_count=1, candidate_coordinates_used=False,
        candidate_objective_bound_assumed=False, solver_optimality_claimed=False,
        complete_relation_equivalence_claimed=False,
        derivation=['Every user group index is 1; exact channels identify one shared activity per phase.',
            'Complete finite activity and preference tables determine every user rating and preference.',
            'For each phase, its complete score equals one column of the checked finite score vector.',
            'Each phase score is at most its enumerated maximum; the complete objective is their sum.',
            'All other original constraints remain present and can only restrict the feasible set.'])
