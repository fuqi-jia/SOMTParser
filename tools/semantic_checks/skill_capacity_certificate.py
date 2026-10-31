"""Checked capacity lower bounds for the MiniZinc skill-allocation model family.

Scope: one scalar skill per job, any positive integer number of training slots per engineer, positive
uniform total-job capacity, integer allocations, and one minimized objective
equal to the number of strictly positive training slots. The source clauses
are recognized by exact tokens; only ordinary data-input assignments and the
standard globals include are accepted, without custom source definitions.
Their finite literal data and the matching
complete target clauses are checked independently. This proves an objective
lower bound, not equivalence of the two complete feasible relations.
"""
import hashlib
import json
import re

import z3

from .source_oracles.ozn_observations import lex, split
from .source_oracles.target_relation import read_target


REQUIRED_SOURCE = {
    'training_parameter': 'int: nNewSkillsPerPerson;',
    'capacity_parameter': 'int: nMaxJobs;',
    'skills': 'set of int: SKILLS = index_set(sSkills);',
    'training': 'set of int: TRAINING = 1..nNewSkillsPerPerson;',
    'engineers': 'set of int: ENGS = index_set_1of2(engineer_skills);',
    'jobs': 'set of int: JOBS = index_set_1of2(jobs);',
    'skills_data': 'array[int] of string: sSkills;',
    'engineer_data': 'array[int,int] of int: engineer_skills;',
    'job_data': 'array[int,int] of int: jobs;',
    'allocations': 'array[JOBS] of var ENGS: allocations;',
    'new_skills': 'array[ENGS,TRAINING] of var 0..0 union SKILLS: new_skills;',
    'allEng_default': 'bool: allEng = false;',
    'skill_matching': r'''constraint if allEng then true else forall(i in JOBS)(
        let { set of int: POSENGS = {e | e in ENGS where engineer_skills[e,jobs[i,1]] == 1}, }
        in (allocations[i] in POSENGS)
        \/ exists(e in ENGS, t in TRAINING)(jobs[i,1] == new_skills[e,t] /\ allocations[i]==e)
        ) endif;''',
    'job_capacity': '''constraint if nMaxJobs == 0 then true else forall(e in ENGS)(
        sum(i in JOBS)(allocations[i] == e) <= nMaxJobs) endif;''',
    'objective_declaration': 'var int: objective;',
    'objective_count': '''constraint objective == sum(e in ENGS, t in TRAINING)(
        new_skills[e,t] > 0);''',
}

DATA_INPUT_NAMES = frozenset([
    'nNewSkillsPerPerson', 'nMaxJobs', 'sSkills', 'engineer_skills',
    'engineer_location', 'jobs', 'nTrainingCap', 'nInterstateCap',
    'nOverseasCap', 'nMinJobs', 'allEng',
])


def need(condition, message):
    if not condition:
        raise ValueError(message)


def digest(text):
    return hashlib.sha256(text.encode()).hexdigest()


def source_facts(source, data):
    """Accept the literal one-based data and only the supported source clauses."""
    source_text, data_text = source.decode(), data.decode()
    source_tokens, data_tokens = lex(source_text), lex(data_text)
    for tokens in [source_tokens, data_tokens]:
        need(not any((a, b) in [('/', '*'), ('*', '/')] for a, b in zip(tokens, tokens[1:])),
             'block comments are outside this narrow source checker scope')
    statements = [tuple(s) for s in split(source_tokens, ';') if s]
    need(not any(token.startswith("'") for token in source_tokens),
         'quoted source identifiers are outside checker scope')
    for statement in statements:
        need(statement[0] not in ['function', 'predicate', 'test', 'type', 'enum', 'annotation'],
             'custom source definitions are outside checker scope')
        need(statement[0] != 'include' or statement == ('include', '"globals.mzn"'),
             'only the standard globals include is supported')
        need(len(statement) < 2 or statement[1] != '=',
             'extra top-level source assignments are unsupported')
    recognized = {}
    for label, template in REQUIRED_SOURCE.items():
        expected = tuple(lex(template)[:-1])
        need(statements.count(expected) == 1, 'unsupported source clause: ' + label)
        recognized[label] = dict(statement_index=statements.index(expected), tokens=list(expected))
    solves = [s for s in statements if s[:1] == ('solve',)]
    need(len(solves) == 1 and solves[0][-2:] == ('minimize', 'objective'),
         'one original minimized objective required')
    data_statements = [s for s in split(data_tokens, ';') if s]
    assignments = {}
    for statement in data_statements:
        need(len(statement) > 2 and statement[1] == '=' and
             re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', statement[0]),
             'only ordinary identifier data assignments are supported')
        name = statement[0]
        need(name in DATA_INPUT_NAMES, 'data key is not an original input parameter: ' + name)
        need(name not in assignments, 'duplicate data assignment: ' + name)
        assignments[name] = statement[2:]
    need('allEng' not in assignments or assignments['allEng'] == ['false'],
         'skill-matching bypass is unsupported')
    def integer(name):
        tokens = assignments.get(name)
        need(tokens is not None and len(tokens) == 1 and re.fullmatch(r'\d+', tokens[0]),
             'literal nonnegative data integer required: ' + name)
        return int(tokens[0])
    slots, capacity = integer('nNewSkillsPerPerson'), integer('nMaxJobs')
    need(slots > 0, 'positive training slots per engineer required')
    need(capacity > 0, 'disabled job capacity is unsupported')
    def matrix(name):
        tokens = assignments.get(name, [])
        need(tokens[:2] == ['[', '|'] and tokens[-2:] == ['|', ']'],
             'one plain one-based literal matrix required: ' + name)
        rows = []
        for row in split(tokens[2:-2], '|'):
            cells = split(row, ',')
            if cells and not cells[-1]:
                cells.pop()  # A legal trailing separator, never an omitted cell.
            need(cells and all(cells), 'empty literal matrix cell')
            values = []
            for cell in cells:
                need((len(cell) == 1 and re.fullmatch(r'\d+', cell[0])) or
                     (len(cell) == 2 and cell[0] in ['+', '-'] and re.fullmatch(r'\d+', cell[1])),
                     'nonliteral matrix value: ' + name)
                values.append(int(''.join(cell)))
            rows.append(values)
        need(rows and len({len(row) for row in rows}) == 1, 'nonrectangular literal matrix')
        return rows
    engineers, jobs = matrix('engineer_skills'), matrix('jobs')
    need(all(x in (0, 1) for row in engineers for x in row), 'Boolean skill matrix required')
    skill_names = assignments.get('sSkills', [])
    need(skill_names[:1] == ['['] and skill_names[-1:] == [']'], 'one literal one-based skill-name array required')
    cells = split(skill_names[1:-1], ',')
    if cells and not cells[-1]:
        cells.pop()
    need(cells and all(len(cell) == 1 and cell[0].startswith('"') for cell in cells), 'literal skill names')
    names = [json.loads(cell[0]) for cell in cells]
    need(len(names) == len(engineers[0]), 'skill-name and matrix extents differ')
    need(all(len(row) == 5 and 1 <= row[0] <= len(names) for row in jobs), 'job skill outside original skill index set')
    return dict(engineer_skills=engineers, jobs=jobs, capacity=capacity, slots=slots,
                source_clauses=recognized, allEng=False, skill_count=len(names),
                one_based_literal_index_sets=True, objective='sum(new_skills[e,t] > 0)')


def canonical(expr):
    """Exact syntax normalization: commutative order and inequality direction."""
    memo = {}
    def visit(node):
        ident = node.get_id()
        if ident in memo:
            return memo[ident]
        if z3.is_int_value(node):
            result = ('int', node.as_long())
        elif z3.is_true(node) or z3.is_false(node):
            result = ('bool', z3.is_true(node))
        elif z3.is_const(node) and node.decl().kind() == z3.Z3_OP_UNINTERPRETED:
            result = ('symbol', str(node.decl().name()), str(node.sort()))
        else:
            need(z3.is_app(node), 'binders are unsupported in certificate clauses')
            op = node.decl().kind()
            children = list(node.children())
            if op in (z3.Z3_OP_AND, z3.Z3_OP_OR, z3.Z3_OP_ADD):
                flat = []
                def flatten(n):
                    if z3.is_app_of(n, op):
                        for child in n.children():
                            flatten(child)
                    else:
                        flat.append(visit(n))
                for child in children:
                    flatten(child)
                result = (str(op), tuple(sorted(flat, key=repr)))
            else:
                if op in (z3.Z3_OP_GE, z3.Z3_OP_GT):
                    children.reverse()
                    op = z3.Z3_OP_LE if op == z3.Z3_OP_GE else z3.Z3_OP_LT
                values = [visit(child) for child in children]
                if op == z3.Z3_OP_EQ:
                    values.sort(key=repr)
                result = (str(op), tuple(values))
        memo[ident] = result
        return result
    return visit(z3.simplify(expr))


def check_skill_capacity_group_bounds(source, data, target, projection, selected_skill_groups):
    """Sum checked bounds for pairwise disjoint nonempty skill groups.

    For group G, let q_G count training slots whose scalar value is in G.
    A non-knowing engineer assigned any G-job must have at least one such
    slot. Thus |jobs_G| <= capacity * (|known_G| + q_G). Integer rounding
    gives q_G >= max(0, ceil(|jobs_G|/capacity) - |known_G|). Disjoint
    positive-valued groups charge each slot at most once, so their bounds
    sum to a lower bound on the complete positive-slot objective. Known
    engineer sets may overlap; only skill groups must be disjoint.
    """
    facts = source_facts(source, data)
    groups, used_skills = [], set()
    need(isinstance(selected_skill_groups, (list, tuple)) and selected_skill_groups,
         'nonempty list of skill groups required')
    for selected in selected_skill_groups:
        need(isinstance(selected, (list, tuple)), 'skill group must be a list or tuple')
        group = list(selected)
        need(group and all(type(s) is int and 1 <= s <= facts['skill_count'] for s in group),
             'nonempty supported skill subset required')
        need(len(set(group)) == len(group), 'duplicate selected skill')
        need(not used_skills.intersection(group), 'overlapping or duplicate skill groups')
        used_skills.update(group)
        groups.append(sorted(group))
    matrix, jobs, capacity = facts['engineer_skills'], facts['jobs'], facts['capacity']
    engineers = list(range(1, len(matrix) + 1))
    job_ids = list(range(1, len(jobs) + 1))
    slots = list(range(1, facts['slots'] + 1))
    group_facts = []
    for group in groups:
        selected_jobs = [i for i in job_ids if jobs[i-1][0] in group]
        need(selected_jobs, 'selected skills have no jobs')
        known = sorted(e for e in engineers if any(matrix[e-1][s-1] == 1 for s in group))
        bound = max(0, (len(selected_jobs) + capacity - 1) // capacity - len(known))
        group_facts.append(dict(selected_skills=group, selected_distinct_jobs=selected_jobs,
                                known_engineer_union=known, lower_bound=bound))
    selected_jobs = sorted(j for group in group_facts for j in group['selected_distinct_jobs'])
    expected_projection = []
    for j in job_ids:
        expected_projection.append(dict(id=f'allocations[{j}]', symbol='allocations', indices=[j], source_name='allocations', source_indices=[j]))
    for e in engineers:
        for t in slots:
            expected_projection.append(dict(id=f'new_skills[{e},{t}]', symbol='new_skills',
                indices=[(e-1)*facts['slots']+(t-1)], source_name='new_skills', source_indices=[e,t]))
    expected_projection.append(dict(id='objective', symbol='objective', indices=[], source_name='objective', source_indices=[]))
    need(json.dumps(projection, sort_keys=True) == json.dumps(expected_projection, sort_keys=True),
         'complete typed original-to-target coordinate map differs')
    variables, program, directions = read_target(target)
    need(all(n in variables for n in ['allocations', 'new_skills', 'objective']), 'missing target declaration')
    allocations, training, objective = (variables[n] for n in ['allocations', 'new_skills', 'objective'])
    need(allocations.sort() == z3.ArraySort(z3.IntSort(ctx=program.ctx), z3.IntSort(ctx=program.ctx)) and
         training.sort() == allocations.sort() and objective.sort().kind() == z3.Z3_INT_SORT,
         'unexpected target observation sorts')
    need(directions == ['minimize'] and len(program.objectives()) == 1 and z3.eq(program.objectives()[0], objective),
         'complete original objective/direction changed')
    rows = []
    def flatten(node, index, path):
        if z3.is_and(node):
            for i, child in enumerate(node.children()):
                flatten(child, index, path+[i])
        else:
            rows.append((node, dict(assertion=index, conjunct_path=path, sexpr_sha256=digest(node.sexpr()))))
    assertions = list(program.assertions())
    for i, node in enumerate(assertions):
        flatten(node, i, [])
    index = {}
    for node, origin in rows:
        index.setdefault(canonical(node), []).append(origin)
    checks = []
    def require_clause(label, expected):
        found = index.get(canonical(expected))
        need(found is not None, 'missing complete target clause: ' + label)
        checks.append(dict(label=label, actual_original_clause=found[0], expected_sexpr=expected.sexpr()))
    A = {j:z3.Select(allocations, j) for j in job_ids}
    T = {(e,t):z3.Select(training, (e-1)*facts['slots']+(t-1))
         for e in engineers for t in slots}
    charge = {et:z3.If(value > 0, 1, 0) for et,value in T.items()}
    for j in job_ids:
        require_clause(f'allocation-{j}-lower', A[j] >= 1)
        require_clause(f'allocation-{j}-upper', A[j] <= len(engineers))
    for j in selected_jobs:
        skill = jobs[j-1][0]
        alternatives = [A[j] == e for e in engineers if matrix[e-1][skill-1] == 1]
        alternatives += [z3.And(A[j] == e, T[e,t] == skill) for e in engineers for t in slots]
        require_clause(f'job-{j}-skill-{skill}', z3.Or(*alternatives))
    for e in engineers:
        total = z3.Sum([z3.If(A[j] == e, 1, 0) for j in job_ids])
        require_clause(f'engineer-{e}-complete-job-capacity', total <= capacity)
    require_clause('complete-positive-training-objective', objective == z3.Sum(list(charge.values())))
    for group in group_facts:
        count, known_count = len(group['selected_distinct_jobs']), len(group['known_engineer_union'])
        group['charged_training'] = 'sum(e,t)(new_skills[e,t] in selected_skills)'
        group['derivation'] = dict(
            partition=f'{count} = sum_e selected_count(e)',
            per_known_engineer_upper=capacity,
            per_other_engineer_upper=f'{capacity} * sum_t If(new_skills[e,t] in selected_skills, 1, 0)',
            capacity_inequality=f'{count} <= {capacity*known_count} + {capacity} * group_slot_count',
            integer_rounding='max(0, ceil(number_selected_jobs / capacity) - cardinality(known_engineer_union))',
            reason=[
                'Each selected job has exactly one integer allocation in the full engineer index set.',
                'Every original engineer capacity counts the complete distinct job index set.',
                'Outside the known union, a matching skill alternative needs at least one slot holding a selected skill.',
                'Zero group slots forbid selected jobs; one or more group slots bound the engineer selected count by capacity times its number of group slots.'])
    bound = sum(group['lower_bound'] for group in group_facts)
    return dict(passed=True, kind='checked-disjoint-skill-capacity-lower-bound', lower_bound=bound,
        source_sha256=hashlib.sha256(source).hexdigest(), data_sha256=hashlib.sha256(data).hexdigest(),
        target_sha256=hashlib.sha256(target).hexdigest(), source_facts=facts, skill_groups=group_facts,
        all_engineers=engineers, maximum_total_jobs_per_engineer=capacity, training_slots_per_engineer=facts['slots'],
        target_checks=checks, original_target_assertions=len(assertions), original_target_conjuncts=len(rows),
        target_objective_directions=directions, target_objective_count=1,
        charged_training='If(new_skills[e,t] > 0, 1, 0)',
        groups_pairwise_disjoint=True,
        sum_derivation='Each scalar training slot belongs to at most one checked positive-valued skill group. Thus sum(group_slot_count) <= complete positive-slot objective; sum the independently rounded group bounds.',
        source_lower_bound=bound, target_lower_bound=bound,
        complete_relation_equivalence_claimed=False, solver_optimality_claimed=False,
        candidate_coordinates_used=False, candidate_objective_bound_assumed=False)


def check_skill_capacity_bound(source, data, target, projection, selected_skills):
    """Backward-compatible single-group entry point, including its named fields."""
    report = check_skill_capacity_group_bounds(source, data, target, projection, [list(selected_skills)])
    group = report['skill_groups'][0]
    report.update(kind='checked-skill-capacity-lower-bound',
                  selected_skills=group['selected_skills'],
                  selected_distinct_jobs=group['selected_distinct_jobs'],
                  known_engineer_union=group['known_engineer_union'],
                  derivation=group['derivation'])
    return report
