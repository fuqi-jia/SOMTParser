"""Exact entailment by exhausting explicit scalar source assignments.

This fallback never bounds the source. It proves S => T only after checking T
at every source tuple and proving that no further source tuple exists. All
free constants in S or T must have explicit model values, and the admitted
Bool/Int fragment has no free function interpretations or undefined division.
Thus fixing the complete tuple makes T a closed, interpretation-independent
sentence. SAT then proves that sentence true, even if it contains private
existential witnesses. Exhaustion failure is unknown, never equivalence.
"""
from dataclasses import dataclass
import time


@dataclass(frozen=True)
class FiniteEntailment:
    status: str
    checked_models: int = 0
    reason: str = ""
    counterexample_model: str = None
    counterexample_values: tuple = ()


def _constants_in_standard_lia(z3, formulas, deadline):
    """Reject nonstandard/underspecified interpretations before enumerating."""
    ordinary = {
        z3.Z3_OP_TRUE, z3.Z3_OP_FALSE, z3.Z3_OP_NOT, z3.Z3_OP_AND,
        z3.Z3_OP_OR, z3.Z3_OP_XOR, z3.Z3_OP_IMPLIES, z3.Z3_OP_IFF,
        z3.Z3_OP_EQ, z3.Z3_OP_DISTINCT, z3.Z3_OP_ITE,
        z3.Z3_OP_LE, z3.Z3_OP_GE, z3.Z3_OP_LT, z3.Z3_OP_GT,
        z3.Z3_OP_ADD, z3.Z3_OP_SUB, z3.Z3_OP_UMINUS,
    }
    divisions = {z3.Z3_OP_IDIV, z3.Z3_OP_MOD, z3.Z3_OP_REM}
    constants, visited, stack = {}, set(), [(f, 0) for f in formulas]
    while stack:
        if deadline is not None and time.monotonic() >= deadline:
            return (), "total wall-time budget exhausted"
        expr, depth = stack.pop()
        if (expr.get_id(), depth) in visited:
            continue
        visited.add((expr.get_id(), depth))
        if expr.sort().kind() not in {z3.Z3_BOOL_SORT, z3.Z3_INT_SORT}:
            return (), "unsupported non-Bool/Int sort"
        if z3.is_quantifier(expr):
            if expr.is_lambda() or any(expr.var_sort(i).kind() not in {
                    z3.Z3_BOOL_SORT, z3.Z3_INT_SORT} for i in range(expr.num_vars())):
                return (), "unsupported binder sort"
            stack.append((expr.body(), depth + expr.num_vars()))
            continue
        if z3.is_var(expr):
            if z3.get_var_index(expr) >= depth:
                return (), "unbound de Bruijn variable"
            continue
        if z3.is_int_value(expr):
            continue
        if not z3.is_app(expr):
            return (), "unsupported expression"
        kind = expr.decl().kind()
        if kind == z3.Z3_OP_UNINTERPRETED:
            if expr.num_args():
                return (), "free function interpretation is not fixed"
            constants[expr.get_id()] = expr
        elif kind == z3.Z3_OP_MUL:
            if sum(not z3.is_int_value(child) for child in expr.children()) > 1:
                return (), "nonlinear multiplication outside fallback fragment"
        elif kind in divisions:
            if (expr.num_args() != 2 or not z3.is_int_value(expr.arg(1))
                    or expr.arg(1).as_long() == 0):
                return (), "division/modulo requires a nonzero constant divisor"
        elif kind not in ordinary:
            return (), "unsupported or underspecified operator"
        stack.extend((child, depth) for child in expr.children())
    return tuple(constants.values()), ""


def prove_finite_source_entailment(source, target, *, max_models=64,
                                  deadline=None, per_check_timeout_ms=None):
    """Return proved/counterexample/unknown without changing either formula.

    max_models limits this optional proof strategy, not the source domain. On
    reaching it, the result remains unknown. None timeouts honor the caller's
    unbounded policy. Models are never completed: an omitted free coordinate
    prevents this proof rather than acquiring an invented diagnostic value.
    """
    import z3

    if not z3.is_bool(source) or not z3.is_bool(target):
        raise TypeError("entailment inputs must be Boolean")
    if source.ctx != target.ctx:
        raise ValueError("entailment inputs must share a context")
    if isinstance(max_models, bool) or not isinstance(max_models, int) or max_models < 1:
        raise ValueError("max_models must be a positive integer")
    if (per_check_timeout_ms is not None and
            (isinstance(per_check_timeout_ms, bool)
             or not isinstance(per_check_timeout_ms, int) or per_check_timeout_ms < 1)):
        raise ValueError("per_check_timeout_ms must be a positive integer or None")
    constants, reason = _constants_in_standard_lia(z3, (source, target), deadline)
    if reason:
        return FiniteEntailment("unknown", reason=reason)
    source_solver, target_solver = z3.Solver(ctx=source.ctx), z3.Solver(ctx=source.ctx)
    source_solver.add(source)
    target_solver.add(target)
    checked = 0

    def check(solver):
        remaining = None if deadline is None else int((deadline - time.monotonic()) * 1000)
        if remaining is not None and remaining <= 0:
            return None
        limits = [v for v in (remaining, per_check_timeout_ms) if v is not None]
        solver.set(timeout=max(1, min(limits)) if limits else 0)
        return solver.check()

    while True:
        answer = check(source_solver)
        if answer == z3.unsat:
            return FiniteEntailment("proved", checked)
        if answer is None or answer == z3.unknown:
            return FiniteEntailment("unknown", checked,
                "source: " + (source_solver.reason_unknown() if answer is not None
                              else "total wall-time budget exhausted"))
        if checked == max_models:
            return FiniteEntailment("unknown", checked, "source enumeration not exhausted")
        model = source_solver.model()
        values = [model.eval(c, model_completion=False) for c in constants]
        if any(not (z3.is_int_value(v) or z3.is_true(v) or z3.is_false(v)) for v in values):
            return FiniteEntailment("unknown", checked, "source model omits a free coordinate")
        bindings = [c == value for c, value in zip(constants, values)]
        target_solver.push()
        target_solver.add(*bindings)
        answer = check(target_solver)
        reason = target_solver.reason_unknown() if answer == z3.unknown else None
        target_solver.pop()
        if answer == z3.unsat:
            from .counterexample_coordinates import scalar_model_values
            return FiniteEntailment("counterexample", checked,
                counterexample_model=str(model), counterexample_values=scalar_model_values(model))
        if answer is None or answer == z3.unknown:
            return FiniteEntailment("unknown", checked,
                "target: " + (reason or "total wall-time budget exhausted"))
        checked += 1
        # Every free scalar coordinate is fixed. The negated full tuple blocks
        # exactly that source assignment; with zero coordinates it blocks True.
        source_solver.add(z3.Not(z3.And(*bindings)) if bindings
                          else z3.BoolVal(False, ctx=source.ctx))
