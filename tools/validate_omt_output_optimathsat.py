#!/usr/bin/env python3
"""Small real-OptiMathSAT qualification; run only against a hash-pinned new build.

Each OMS model is checked against the original Z3 hard relation and ordered,
signed objective vector. Lex compares optimal costs; Pareto enumerates this
fixture's entire finite front; box loads each independent objective model.
This is fixture-level solver evidence, not a general equivalence proof.
"""
import argparse
import csv
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import subprocess
import time
import traceback


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def sexprs(text):
    # Solver responses use ordinary numerals, Booleans and simple fixture names.
    # Keep quoted symbols/strings intact so an error cannot be mistaken for SAT.
    tokens = re.findall(r';[^\n]*|"(?:[^"]|"")*"|\|[^|]*\||[()]|[^\s()]+', text)
    stack, result = [], []
    for token in tokens:
        if token.startswith(';'):
            continue
        if token == '(':
            stack.append([])
        elif token == ')':
            if not stack:
                raise ValueError('unbalanced solver response')
            item = stack.pop()
            (stack[-1] if stack else result).append(item)
        else:
            (stack[-1] if stack else result).append(token)
    if stack:
        raise ValueError('incomplete solver response')
    return result


def smt_text(value):
    return '(' + ' '.join(map(smt_text, value)) + ')' if isinstance(value, list) else value


def fixtures():
    one = '(declare-const x Int)(assert (and (<= 0 x) (<= x 7)))'
    two = ('(declare-const x Int)(declare-const y Int)'
           '(assert (and (>= x 0) (>= y 0) (= (+ x y) 4)))')
    mixed = ('(declare-const x Int)(declare-const p Bool)'
             '(assert (and (>= x 0) (<= x 5) (= p (= x 0))))')
    cases = []

    def add(name, body, names, mode='lex'):
        cases.append(dict(name=name, source=f'(set-option :opt.priority {mode})' + body
                          + '(check-sat)(get-objectives)', names=names, mode=mode))

    add('single_min', one + '(minimize x)', {'x': 'Int'})
    add('single_max', one + '(maximize x)', {'x': 'Int'})
    add('lex_xy', two + '(minimize x)(minimize y)', {'x': 'Int', 'y': 'Int'})
    add('lex_yx', two + '(minimize y)(minimize x)', {'x': 'Int', 'y': 'Int'})
    add('pareto', two + '(minimize x)(minimize y)', {'x': 'Int', 'y': 'Int'}, 'pareto')
    add('box', two + '(minimize x)(minimize y)', {'x': 'Int', 'y': 'Int'}, 'box')
    soft = '(assert-soft (not p) :weight 9 :id preference)'
    add('soft_first', mixed + soft + '(minimize x)', {'x': 'Int', 'p': 'Bool'})
    add('min_first', mixed + '(minimize x)' + soft, {'x': 'Int', 'p': 'Bool'})
    for name, left, right in [('integer', '9', '4'),
                               ('large', '9007199254740993', '9007199254740992'),
                               ('rational', '3.5', '0.5')]:
        add('same_group_' + name, '(declare-const p Bool)'
            f'(assert-soft p :weight {left} :id same)'
            f'(assert-soft (not p) :weight {right} :id same)', {'p': 'Bool'})
    add('later_group_member', mixed + '(assert-soft p :weight 9 :id first)'
        '(minimize x)(assert-soft (not p) :weight 2 :id first)', {'x': 'Int', 'p': 'Bool'})
    add('declared_group_collision', '(declare-const p Bool)(declare-const same Int)'
        '(assert (= same 3))(assert-soft p :weight 9 :id same)'
        '(assert-soft (not p) :weight 4 :id same)', {'p': 'Bool', 'same': 'Int'})
    add('default_and_named_I', '(declare-const p Bool)(assert-soft p :weight 3)'
        '(assert-soft (not p) :weight 7 :id I)', {'p': 'Bool'})
    cases.append(dict(name='packed_wcnf', mode='lex', names={'x1': 'Bool', 'x2': 'Bool'},
                      language='wcnf', source='p wcnf 2 4 10000000000000000\n'
                      '10000000000000000 1 0\n7 -2 0\n3 2 0\n9007199254740993 0\n',
                      reference='(declare-const x1 Bool)(declare-const x2 Bool)(assert x1)'
                      '(assert-soft (not x2) :weight 7)(assert-soft x2 :weight 3)'
                      '(assert-soft false :weight 9007199254740993)(check-sat)'))
    return cases


def optimizer(z3, text):
    opt = z3.Optimize()
    opt.set(timeout=10000)
    opt.from_string(text)
    return opt


def hir_fixtures():
    selected = {case['name']: case for case in fixtures()}
    cases = [dict(selected[name], name='hir_' + name, hir_kind=name)
             for name in ('soft_first', 'declared_group_collision', 'default_and_named_I')]
    case = dict(selected['soft_first'], name='hir_soft_first_max', hir_kind='soft_first_max')
    case['source'] = case['source'].replace('(minimize x)', '(maximize x)')
    return cases + [case]


def make_hir(sp, case):
    n = sp._somtparser
    model = n.HirModel()
    op = lambda name, *args: n._hir_op(name, list(args))
    integer = lambda value: n._hir_literal(n.HirSort.integer(), str(value))
    p = model.declare('p', n.HirSort.boolean())
    kind = case['hir_kind']
    if kind.startswith('soft_first'):
        x = model.declare('x', n.HirSort.integer())
        model.constrain(op('and', op('ge', x, integer(0)), op('le', x, integer(5))))
        model.constrain(op('eq', p, op('eq', x, integer(0))))
        # The HIR contract orders soft groups before explicit objectives,
        # independently of the order of these API calls.
        model.objective(kind == 'soft_first_max', x)
        model.soft_constrain(op('not', p), '9', group='preference')
        model.objective_order('lexicographic')
    elif kind == 'default_and_named_I':
        model.soft_constrain(p, '3')
        model.soft_constrain(op('not', p), '7', group='I')
        model.objective_order('lexicographic')
    else:
        same = model.declare('same', n.HirSort.integer())
        model.constrain(op('eq', same, integer(3)))
        model.soft_constrain(p, '9', group='same')
        model.soft_constrain(op('not', p), '4', group='same')
    return model


def prove_export(z3, reference_opt, text):
    exported = optimizer(z3, text)
    solver = z3.Solver()
    solver.set(timeout=10000)
    solver.add(z3.Xor(z3.And(*reference_opt.assertions()), z3.And(*exported.assertions())))
    hard = str(solver.check())
    costs = list(reference_opt.objectives())
    proofs = []
    if len(exported.objectives()) == len(costs):
        for before, after in zip(costs, exported.objectives()):
            solver = z3.Solver()
            solver.set(timeout=10000)
            solver.add(before != after)
            proofs.append(str(solver.check()))
    return dict(hard_relation=hard, ordered_costs=proofs,
                matches_source=(hard == 'unsat' and len(proofs) == len(costs)
                                and all(value == 'unsat' for value in proofs)))


def reference(z3, case):
    opt = optimizer(z3, case.get('reference', case['source']))
    costs = list(opt.objectives())
    expected, statuses = [], []
    for _ in range(12 if case['mode'] == 'pareto' else 1):
        status = opt.check()
        statuses.append(str(status))
        if status == z3.unsat and case['mode'] == 'pareto':
            break
        if status != z3.sat:
            raise AssertionError('reference not SAT: ' + str(status))
        if case['mode'] == 'box':
            expected = [str(z3.OptimizeObjective(opt, i, False).lower()) for i in range(len(costs))]
        else:
            expected.append(tuple(str(opt.model().eval(cost, model_completion=True)) for cost in costs))
    if case['mode'] == 'pareto' and statuses[-1] != 'unsat':
        raise AssertionError('reference finite Pareto front did not terminate')
    return opt, costs, expected, statuses


def validate_model(z3, case, reference_opt, costs, values):
    assignment = z3.Solver()
    assignment.set(timeout=10000)
    declarations = ''.join(f'(declare-const {name} {sort})' for name, sort in case['names'].items())
    assertions = ''.join(f'(assert (= {name} {smt_text(value)}))' for name, value in values.items())
    assignment.from_string(declarations + assertions)
    assignment.add(*reference_opt.assertions())
    status = assignment.check()
    if status != z3.sat:
        raise AssertionError('OMS assignment violates original hard constraints: ' + str(status))
    return tuple(str(assignment.model().eval(cost, model_completion=True)) for cost in costs)


def run_case(sp, z3, args, case, route):
    output_dir = args.output / (case['name'] + '--' + route)
    output_dir.mkdir()
    started = time.monotonic()
    row = dict(case=case['name'], route=route, mode=case['mode'], status='error',
               objective_costs_agree=False, source_model_feasible=False)
    try:
        (output_dir / 'source.txt').write_text(case['source'])
        ref, costs, expected, ref_statuses = reference(z3, case)
        row.update(reference_expected=expected, reference_statuses=ref_statuses, objective_count=len(costs))
        if route == 'native':
            parser = sp.parse(case['source'])
            text = parser.dump_smt2(dialect=sp.OmtDialect.OptiMathSAT)
            z3_text = parser.dump_smt2(dialect=sp.OmtDialect.Z3)
        else:
            result = (make_hir(sp, case).translate(dialect=sp.OmtDialect.OptiMathSAT) if route == 'hir'
                      else sp.translate(source=case['source'], language=case.get('language', 'smtlib2'),
                                        options={'packed': '1'} if case.get('language') == 'wcnf' else {},
                                        dialect=sp.OmtDialect.OptiMathSAT))
            if not result.ok:
                row['status'] = 'translation_rejected'
                row['diagnostics'] = [dict(code=str(d.code), severity=str(d.severity), message=d.message,
                                           file=d.file, line=d.line, column=d.column) for d in result.diagnostic_items]
                raise AssertionError('translation rejected')
            text = result.to_smt2(sp.OmtDialect.OptiMathSAT)
            z3_text = result.to_smt2(sp.OmtDialect.Z3)
            if route == 'hir':
                proposal = result.to_smt2(sp.OmtDialect.Gomt)
                (output_dir / 'exported-gomt.smt2').write_text(proposal)
                if proposal.count('(optimize-sat ') != 1 or '(check-sat)' in proposal:
                    raise AssertionError('GOMT must have one optimization query')
                restored = sp.parse(proposal).dump_smt2(dialect=sp.OmtDialect.Z3)
                (output_dir / 'gomt-reimport-z3.smt2').write_text(restored)
                row['gomt_reimport_proof'] = prove_export(z3, ref, restored)
                row['gomt_validation_scope'] = 'SOMTParser reimport then Z3 hard/cost proof; no native GOMT solver'
                if not row['gomt_reimport_proof']['matches_source']:
                    raise AssertionError('GOMT reimport changed hard relation or signed ordered costs')
        (output_dir / 'exported-optimathsat.smt2').write_text(text)
        (output_dir / 'exported-z3.smt2').write_text(z3_text)
        row['source_sha256'] = sha256(output_dir / 'source.txt')
        row['optimathsat_export_sha256'] = sha256(output_dir / 'exported-optimathsat.smt2')
        row['z3_export_sha256'] = sha256(output_dir / 'exported-z3.smt2')
        # This independent solver proof compares the Z3 export's complete hard
        # relation and signed ordered costs, not just one optimum/model.
        try:
            exported = optimizer(z3, z3_text)
            proof = z3.Solver()
            proof.set(timeout=10000)
            proof.add(z3.Xor(z3.And(*ref.assertions()), z3.And(*exported.assertions())))
            hard_status = str(proof.check())
            cost_statuses = []
            if len(exported.objectives()) == len(costs):
                for before, after in zip(costs, exported.objectives()):
                    proof = z3.Solver()
                    proof.set(timeout=10000)
                    proof.add(before != after)
                    cost_statuses.append(str(proof.check()))
            row['z3_export_hard_relation_proof'] = hard_status
            row['z3_export_ordered_cost_proofs'] = cost_statuses
            row['z3_export_matches_source'] = (hard_status == 'unsat' and len(cost_statuses) == len(costs)
                                               and all(s == 'unsat' for s in cost_statuses))
        except Exception as error:
            row.update(z3_export_matches_source=False, z3_export_error=str(error))
        if text.count('(check-sat)') != 1:
            raise AssertionError('expected exactly one terminal query in exported snapshot')
        # Append response-only requests to the exported snapshot. Pareto adds
        # explicit extra solve requests; box selects each objective model.
        body = re.sub(r'\(exit\)\s*$', '', text.strip()) + '\n'
        get_values = '(echo "SOMT_VALIDATION_MODEL")\n(get-value (' + ' '.join(case['names']) + '))\n'
        if case['mode'] == 'box':
            body += ''.join(f'(load-objective-model {index})\n' + get_values for index in range(len(costs)))
        else:
            body += get_values
            if case['mode'] == 'pareto':
                body += ('(check-sat)\n' + get_values) * (len(expected) - 1) + '(check-sat)\n'
        body += '(exit)\n'
        (output_dir / 'queried-optimathsat.smt2').write_text(body)

        def limits():
            resource.setrlimit(resource.RLIMIT_AS, (2 << 30, 2 << 30))
            resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
            os.sched_setaffinity(0, {args.cpu})

        solver_start = time.monotonic()
        process = subprocess.run([str(args.solver), '-optimization=true'], input=body,
                                 text=True, capture_output=True, timeout=30, preexec_fn=limits)
        row.update(solver_wall_seconds=time.monotonic() - solver_start, solver_rc=process.returncode)
        (output_dir / 'optimathsat.stdout').write_text(process.stdout)
        (output_dir / 'optimathsat.stderr').write_text(process.stderr)
        responses = sexprs(process.stdout)
        statuses = [item for item in responses if item in ('sat', 'unsat', 'unknown')]
        errors = [item for item in responses if isinstance(item, list) and item and item[0] == 'error']
        row.update(solver_statuses=statuses, solver_errors=errors)
        if process.returncode != 0 or errors or 'unknown' in statuses:
            raise AssertionError('solver failure: ' + json.dumps(dict(rc=process.returncode, errors=errors, statuses=statuses)))
        models = []
        for index, item in enumerate(responses):
            if item not in ('"SOMT_VALIDATION_MODEL"', 'SOMT_VALIDATION_MODEL'):
                continue
            values = responses[index + 1]
            if not isinstance(values, list) or not all(isinstance(pair, list) and len(pair) == 2
                    and isinstance(pair[0], str) and pair[0] in case['names'] for pair in values):
                raise AssertionError('missing get-value response after model marker')
            if set(pair[0] for pair in values) != set(case['names']):
                raise AssertionError('incomplete get-value assignment')
            models.append(dict(values))
        row.update(solver_statuses=statuses, solver_errors=errors, model_count=len(models), models=models)
        observed = [validate_model(z3, case, ref, costs, model) for model in models]
        row['observed_cost_vectors'] = observed
        if case['mode'] == 'box':
            correct = len(observed) == len(costs) and all(observed[i][i] == value for i, value in enumerate(expected))
        elif case['mode'] == 'pareto':
            correct = len(observed) == len(expected) and set(observed) == set(expected) and statuses == ref_statuses
        else:
            correct = observed == expected and statuses == ['sat']
        row['source_model_feasible'] = bool(observed)
        row['objective_costs_agree'] = correct
        if not correct or not row['z3_export_matches_source']:
            raise AssertionError('objective agreement or complete Z3 export comparison failed')
        row['status'] = 'pass'
    except subprocess.TimeoutExpired as error:
        row.update(status='solver_timeout', error=str(error))
    except Exception as error:
        row.update(error=str(error), traceback=traceback.format_exc())
    row['wall_seconds'] = time.monotonic() - started
    (output_dir / 'result.json').write_text(json.dumps(row, indent=2) + '\n')
    return row


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--run', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--solver', type=Path, required=True)
    parser.add_argument('--cpu', type=int, default=145)
    parser.add_argument('--native-receipt', type=Path,
                        help='Explicit diagnostic receipt; never modifies the build status')
    parser.add_argument('--label', default='final-build')
    parser.add_argument('--cohort', choices=('source', 'hir'), default='source')
    parser.add_argument('--expected-native-sha')
    args = parser.parse_args()
    if args.native_receipt and args.label == 'final-build':
        raise SystemExit('diagnostic receipt requires an explicit non-final label')
    status = json.loads((args.native_receipt or args.run / 'build-status.json').read_text())
    if (not args.native_receipt and status.get('stage') not in ('python_tests', 'python_failed', 'complete')) or not status.get('native_sha256'):
        raise SystemExit('new native is not qualified for this validation stage')
    resource.setrlimit(resource.RLIMIT_AS, (2 << 30, 2 << 30))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    os.sched_setaffinity(0, {args.cpu})
    import somtparser as sp
    import somtparser._somtparser as native
    import z3
    actual_sha = sha256(native.__file__)
    if actual_sha != status['native_sha256']:
        raise SystemExit('native hash differs from build receipt')
    if args.expected_native_sha and actual_sha != args.expected_native_sha:
        raise SystemExit('native hash differs from explicitly pinned validation build')
    args.output.mkdir(parents=True, exist_ok=False)
    (args.output / 'validation-script.py').write_bytes(Path(__file__).read_bytes())
    os.sched_setaffinity(0, {args.cpu})
    provenance = dict(native_path=native.__file__, native_sha256=actual_sha,
                      script_sha256=sha256(__file__), solver_path=str(args.solver),
                      solver_sha256=sha256(args.solver), z3_version=z3.get_version_string(),
                      solver_provenance_file='/pub/data/jiafq/SOMTParser-deps/qualification-tools/optimathsat/provenance.json',
                      build_receipt=status, cpu=args.cpu, solver_timeout_seconds=30,
                      validator_address_space_bytes=2 << 30,
                      validation_label=args.label, explicit_native_receipt=str(args.native_receipt),
                      cohort=args.cohort,
                      solver_address_space_bytes=2 << 30, shared_host=True,
                      load_average=os.getloadavg(), started=time.time(),
                      interpretation='Small fixture evidence; unknown/errors are failures; no general equivalence claim.')
    (args.output / 'provenance.json').write_text(json.dumps(provenance, indent=2) + '\n')
    rows = []
    for case in (hir_fixtures() if args.cohort == 'hir' else fixtures()):
        for route in (['hir'] if args.cohort == 'hir' else
                      ['translation'] if case.get('language') == 'wcnf' else ['native', 'translation']):
            row = run_case(sp, z3, args, case, route)
            rows.append(row)
            print(json.dumps({key: row.get(key) for key in ('case', 'route', 'status', 'error')}), flush=True)
    summary = dict(total=len(rows), passed=sum(row['status'] == 'pass' for row in rows),
                   translation_rejected=sum(row['status'] == 'translation_rejected' for row in rows),
                   emitted_outputs=sum('optimathsat_export_sha256' in row for row in rows),
                   emitted_passed=sum(row['status'] == 'pass' for row in rows),
                   emitted_failed=sum('optimathsat_export_sha256' in row and row['status'] != 'pass' for row in rows),
                   failures=[{key: row.get(key) for key in ('case', 'route', 'status', 'error')} for row in rows if row['status'] != 'pass'],
                   native_sha256=actual_sha, finished=time.time())
    (args.output / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    with (args.output / 'summary.csv').open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=['case', 'route', 'mode', 'status', 'objective_count',
                                                   'objective_costs_agree', 'source_model_feasible',
                                                   'z3_export_matches_source', 'solver_wall_seconds', 'wall_seconds', 'error'],
                                extrasaction='ignore')
        writer.writeheader()
        writer.writerows(rows)
    print(json.dumps(summary), flush=True)
    return 0 if summary['passed'] == summary['total'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
