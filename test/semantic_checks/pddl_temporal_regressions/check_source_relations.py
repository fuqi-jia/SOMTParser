"""Server-only focused source schedules against every emitted assertion.

The independent reference interprets simple happenings as sets of grounded
action names. It does not import any SOMTParser implementation or repair SMT.
"""
from fractions import Fraction
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import resource
import subprocess
import time
import traceback


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def sexp(path):
    tokens = re.findall(r'\(|\)|[^\s()]+',re.sub(r';[^\r\n]*','',Path(path).read_text()).lower())
    index = 0
    def take():
        nonlocal index
        token = tokens[index]
        index += 1
        if token != '(':
            assert token != ')'
            return token
        values = []
        while tokens[index] != ')':
            values.append(take())
        index += 1
        return values
    value = take()
    assert index == len(tokens)
    return value


def conjunctions(value):
    return value[1:] if value and value[0] == 'and' else ([] if not value else [value])


def source_relation(example, domain, problem):
    schedule = example['schedule']
    fields = {row[0]:row[1:] for row in problem[2:]}
    if example['kind'] == 'simple-happening-set':
        actions = {row[1]:dict(zip(row[2::2],row[3::2])) for row in domain[2:] if row[0] == ':action'}
        # Set construction is the source Definition 11, independent of the
        # target's occurrence-index implementation and its emitted updates.
        events = {(Fraction(row['start']),row['action'],tuple(row.get('arguments',[]))) for row in schedule}
        x = next(Fraction(row[2]) for row in fields[':init'] if row[:2] == ['=',['x']])
        for _, name, _ in events:
            effect = actions[name][':effect']
            assert effect[:2] == ['increase',['x']]
            x += Fraction(effect[2])
        valid = all(Fraction(row['start']) > 0 and Fraction(row['start']) == Fraction(row['end']) for row in schedule)
        return valid,x,dict(unique_source_events=len(events),raw_trace_entries=len(schedule))
    if example['kind'] in ('empty-duration','zero-duration','zero-duration-conflict'):
        action = next(row for row in domain[2:] if row[0] == ':durative-action')
        af = dict(zip(action[2::2],action[3::2]))
        start,end = (Fraction(schedule[0][key]) for key in ('start','end'))
        if example['kind'] == 'empty-duration':
            assert af[':duration'] == []
            valid = start > 0 and end >= start
        else:
            assert af[':duration'] == ['=','?duration','0']
            valid = start > 0 and end == start
            if example['kind'] == 'zero-duration-conflict':
                endpoints = {'start':{'adds':set(),'deletes':set()},'end':{'adds':set(),'deletes':set()}}
                for effect in conjunctions(af[':effect']):
                    assert effect[0] == 'at'
                    value = effect[2]
                    negative = value[0] == 'not'
                    atom = value[1] if negative else value
                    endpoints[effect[1]]['deletes' if negative else 'adds'].add(tuple(atom))
                a,b = endpoints['start'],endpoints['end']
                valid &= not bool((a['adds'] & b['deletes']) | (b['adds'] & a['deletes']))
        return valid,end,dict(duration=str(end-start),zero_not_unconditionally_rejected=True)
    assert example['kind'] == 'TIL-stable-goal' and not schedule
    goal = fields[':goal'][0]
    assert len(goal) == 1
    truth,events = set(),{}
    for entry in fields[':init']:
        if entry[0] == 'at':
            time = Fraction(entry[1])
            events.setdefault(time,[]).append(entry[2])
        else:
            truth.add(tuple(entry))
    trace = [(Fraction(0),tuple(goal) in truth)]
    for time,effects in sorted(events.items()):
        adds = {tuple(x) for x in effects if x[0] != 'not'}
        deletes = {tuple(x[1]) for x in effects if x[0] == 'not'}
        if adds & deletes:
            return False,None,dict(reason='conflicting mandatory events')
        truth = (truth-deletes)|adds
        trace.append((time,tuple(goal) in truth))
    valid = trace[-1][1]
    makespan = next((time for i,(time,_) in enumerate(trace) if all(g for _,g in trace[i:])),None)
    return valid,makespan,dict(source_trace=[(str(t),g) for t,g in trace])


def symbols(expressions,z3):
    found,seen = {},set()
    stack = list(expressions)
    while stack:
        expr = stack.pop()
        if expr.get_id() in seen:
            continue
        seen.add(expr.get_id())
        if z3.is_const(expr) and expr.decl().kind() == z3.Z3_OP_UNINTERPRETED:
            found[str(expr.decl().name())] = expr
        stack.extend(expr.children())
    return found


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary',required=True,type=Path)
    parser.add_argument('--binary-sha256',required=True)
    parser.add_argument('--dispatch',default='joint_corpus_translate',help='Empty for the standalone public tool')
    parser.add_argument('--output',required=True,type=Path)
    args = parser.parse_args()
    # Server placement is enforced by the campaign runner, not this portable oracle.
    assert resource.getrlimit(resource.RLIMIT_AS) == (-1,-1)
    assert resource.getrlimit(resource.RLIMIT_CPU) == (-1,-1)
    assert sha(args.binary) == args.binary_sha256
    import z3
    root = Path(__file__).resolve().parent
    manifest = json.loads((root/'cases.json').read_text())
    args.output.mkdir()
    rows = []
    for case in manifest:
        out = args.output/case['id']
        out.mkdir()
        row = dict(id=case['id'],passed=False,solver_timeout_ms=0,resource_limits=None)
        try:
            domain,problem = (root/case[key] for key in ('domain','problem'))
            expected,cost,reference = source_relation(case,sexp(domain),sexp(problem))
            row.update(expected_source_valid=expected,expected_source_metric=None if cost is None else str(cost),reference=reference,
                domain_sha256=sha(domain),problem_sha256=sha(problem),schedule=case['schedule'])
            command = [str(args.binary)]+([args.dispatch] if args.dispatch else [])+[str(domain),str(problem),
                str(case['horizon']),str(out/'target.smt2'),str(out/'translation-report.json'),'strict']
            (out/'command.json').write_text(json.dumps(dict(argv=command,binary_sha256=args.binary_sha256),indent=2)+'\n')
            started = time.monotonic()
            with (out/'translation.stdout').open('xb') as stdout,(out/'translation.stderr').open('xb') as stderr:
                process = subprocess.run(command,stdout=stdout,stderr=stderr)
            row.update(translation_returncode=process.returncode,translation_wall_seconds=time.monotonic()-started)
            assert process.returncode == 0,'valid source form rejected before relation comparison'
            model = z3.Optimize()
            model.set(timeout=0)
            model.from_file(str(out/'target.smt2'))
            assert len(model.objectives()) == 1
            env = symbols([*model.assertions(),*model.objectives()],z3)
            assumptions = []
            for slot in range(case['horizon']):
                base = '__pddl_occurrence_'+str(slot)
                active = slot < len(case['schedule'])
                assumptions.append(env[base+'_active'] == active)
                if not active:
                    continue
                entry = case['schedule'][slot]
                assumptions.extend([env[base+'_start'] == z3.RealVal(entry['start']),
                    env[base+'_end'] == z3.RealVal(entry['end']),env[base+'_action_'+str(entry['action_index'])]])
            solver = z3.Solver()
            solver.set(timeout=0)
            solver.add(*model.assertions(),*assumptions)
            answer = solver.check()
            row['actual_grounded_trace_result'] = str(answer)
            row['complete_assertions'] = len(model.assertions())
            if answer == z3.sat and not expected:
                (out/'relation-counterexample.txt').write_text(str(solver.model()))
            assert answer == (z3.sat if expected else z3.unsat),'grounded source/target relation differs'
            if expected:
                exact = z3.RealVal(str(cost))
                solver.push()
                solver.add(model.objectives()[0] != exact)
                bad = solver.check()
                row['exact_cost_negation_result'] = str(bad)
                if bad == z3.sat:
                    (out/'cost-counterexample.txt').write_text(str(solver.model()))
                solver.pop()
                assert bad == z3.unsat,'target objective differs from exact source value'
                row['wrong_cost_controls'] = []
                for wrong in [cost-1,cost+1]:
                    solver.push()
                    solver.add(model.objectives()[0] == z3.RealVal(str(wrong)))
                    value = solver.check()
                    solver.pop()
                    row['wrong_cost_controls'].append(dict(value=str(wrong),result=str(value)))
                    assert value == z3.unsat,'wrong cost was not rejected'
            row.update(passed=True,target_sha256=sha(out/'target.smt2'),whole_module_loaded=True)
        except Exception as error:
            row.update(error=repr(error),traceback=traceback.format_exc())
        rows.append(row)
        (out/'result.json').write_text(json.dumps(row,indent=2)+'\n')
    result = dict(passed=all(row['passed'] for row in rows),cases=rows,case_count=len(rows),
        source_relation_scope='original focused schedules; every emitted assertion and exact objective',
        primary_semantics='Fox-Long Definitions 11/13/17/18 and Appendix A.3; IPC-4 stable-goal definition',
        no_accuracy_claim=True,resource_limits=None,solver_timeout_ms=0)
    (args.output/'source-relations.json').write_text(json.dumps(result,indent=2)+'\n')
    return 0 if result['passed'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
