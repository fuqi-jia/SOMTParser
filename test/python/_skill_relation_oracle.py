"""Hand-authored skill API fixtures and complete relation/objective oracle."""

def cases():
    # Hand-authored development tasks, not held-out benchmark rows.
    return [
        dict(id='integer-bound',domain='linear',
             source='Choose an integer x between 4 and 9, inclusive. Minimize x.',
             context={},observables={'x':'Int'},reference='(declare-const x Int) (assert (and (>= x 4) (<= x 9))) (minimize x)'),
        dict(id='scheduling',domain='cp',
             source='Tasks A and B have integer start times a and b, each between 0 and 5 inclusive. Their durations are 2 and 3. One machine executes at most one task at a time; one task may start when the other finishes. Define cost as the last completion time and minimize cost.',
             context={'a':'Integer start of A; preserve this output name.', 'b':'Integer start of B; preserve this output name.', 'cost':'Integer last completion time; preserve this output name.'},observables={'a':'Int','b':'Int','cost':'Int'},
             reference='(declare-const a Int) (declare-const b Int) (declare-const cost Int) (assert (and (<= 0 a) (<= a 5) (<= 0 b) (<= b 5) (or (<= (+ a 2) b) (<= (+ b 3) a)) (= cost (ite (>= (+ a 2) (+ b 3)) (+ a 2) (+ b 3))))) (minimize cost)'),
        dict(id='boolean-count',domain='cp',
             source='布尔变量 p、q、r 中恰好两个为真，并且 p 蕴含 q。找一个满足条件的赋值。',
             context={'p':'Boolean decision variable.', 'q':'Boolean decision variable.', 'r':'Boolean decision variable.'},observables={'p':'Bool','q':'Bool','r':'Bool'},
             reference='(declare-const p Bool) (declare-const q Bool) (declare-const r Bool) (assert (= (+ (ite p 1 0) (ite q 1 0) (ite r 1 0)) 2)) (assert (=> p q))'),
        dict(id='real-profit',domain='linear',
             source='Let x and y be nonnegative real quantities with x + y at most 7. Profit is 3*x + 2*y - 0.5. Maximize profit.',
             context={'x':'Real quantity; preserve this output name.', 'y':'Real quantity; preserve this output name.', 'profit':'Real profit; preserve this output name.'},observables={'x':'Real','y':'Real','profit':'Real'},
             reference='(declare-const x Real) (declare-const y Real) (declare-const profit Real) (assert (and (>= x 0) (>= y 0) (<= (+ x y) 7) (= profit (- (+ (* 3 x) (* 2 y)) (/ 1 2))))) (maximize profit)')]


def check(code, task):
    """Compare existentially projected feasible and normalized objective relations."""
    import z3
    from z3.z3util import get_vars
    candidate, reference = z3.Optimize(), z3.Optimize()
    candidate.from_string(code)
    reference.from_string(task['reference'])
    if len(candidate.objectives()) != len(reference.objectives()):
        return dict(status='semantic-mismatch', reason='objective-count')
    constructors = dict(Int=z3.Int,Real=z3.Real,Bool=z3.Bool)
    observables = [constructors[sort](name) for name,sort in task['observables'].items()]
    expected = {(v.decl().name(),v.sort().sexpr()) for v in observables}
    all_candidate = z3.And(*(list(candidate.assertions()) + [o == o for o in candidate.objectives()]))
    actual = {(v.decl().name(),v.sort().sexpr()) for v in get_vars(all_candidate)}
    if not expected <= actual:
        return dict(status='semantic-mismatch',reason='missing-or-wrong-sort-observable',missing=sorted(expected-actual))
    metrics = [z3.FreshConst(obj.sort(),prefix='pilot_cost') for obj in reference.objectives()]
    def project(optimizer,with_objective):
        formulas=list(optimizer.assertions())
        if with_objective:
            formulas += [obj==metric for obj,metric in zip(optimizer.objectives(),metrics)]
        expression=z3.And(*formulas)
        auxiliaries=[v for v in get_vars(expression) if
                     (v.decl().name(),v.sort().sexpr()) not in expected and not any(v.eq(m) for m in metrics)]
        return z3.Exists(auxiliaries,expression) if auxiliaries else expression
    checks={}
    for name,with_objective in [('feasible_relation',False),('objective_relation',True)]:
        solver=z3.Solver()
        solver.set(timeout=10000)
        solver.add(z3.Xor(project(candidate,with_objective),project(reference,with_objective)))
        answer=solver.check()
        checks[name]=str(answer)
        if answer==z3.sat:
            return dict(status='semantic-mismatch',checks=checks,counterexample=solver.model().sexpr())
        if answer==z3.unknown:
            return dict(status='semantic-unknown',checks=checks,reason=solver.reason_unknown())
    return dict(status='equivalent',checks=checks,z3_version=z3.get_version_string())


