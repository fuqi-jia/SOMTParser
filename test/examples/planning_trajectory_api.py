"""Build an exact soft trajectory constraint and export its complete SMT module.

Run on a qualified server package: python planning_trajectory_api.py
This constructs HIR directly; it makes no PDDL parser coverage claim.
"""
from somtparser import planning as n
from somtparser import planning_trajectory as p


def build_model():
    model = n.HirModel()
    boolean = n.HirSort.boolean(); real = n.HirSort.real()
    true = n.literal(boolean, 'true')
    visits = [model.declare(f'visited_{i}', boolean) for i in range(3)]
    samples = [p.HirTrajectorySample(true, n.literal(real, str(i)),
               n.planning_numeric_predicate(visits[i])) for i in range(3)]
    trajectory = p.planning_finite_trajectory(model, p.TrajectoryOperator.SOMETIME, samples)
    complete = trajectory.to_model(model, hard=False)
    preferences = p.planning_preferences(complete, [
        p.HirPreferenceInstance('goal-visit', 'visit', true, trajectory.satisfied)])
    # A named preference has no implicit penalty: explicitly put its count
    # into the metric. Anonymous preferences would be added by the helper.
    metric = p.planning_preference_metric(complete, preferences.violation_count('visit'),
                                         preferences, minimize=True)
    complete.objective(False, metric)
    return complete


if __name__ == '__main__':
    result = build_model().translate()
    if not result.ok:
        raise RuntimeError([d.message for d in result.diagnostics])
    print(result.to_smt2())
