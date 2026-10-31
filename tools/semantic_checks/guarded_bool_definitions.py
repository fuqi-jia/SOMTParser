"""Proof-gated elimination of finite guard-defined Bool/Int auxiliaries.

The recognizer is deliberately narrow: a Bool is bridged to an Int with
``ite(b, 1, 0) == iv`` and ``iv`` is constrained for each value of a bounded
Int guard variable by implications. The replacement is accepted only when the
finite table exactly covers a consistent unary interval and a structural proof
establishes the local existential equivalence and redundancy of every removed
clause. No candidate formula or observable answer is consulted.
"""
from dataclasses import dataclass
import time


@dataclass(frozen=True)
class GuardedBoolResult:
    body: object
    group_count: int = 0
    removed_clause_count: int = 0
    proof_time_ms: float = 0.0
    fallback_reason: str = ""
    proof_phase: str = ""
    proof_phase_time_ms: float = 0.0
    bound_validation_time_ms: float = 0.0
    proof_kind: str = "none"


def _is_kind(z3, expr, kind):
    return z3.is_app(expr) and expr.decl().kind() == kind


def _const_name(z3, expr):
    if (z3.is_const(expr)
            and expr.decl().kind() == z3.Z3_OP_UNINTERPRETED):
        return str(expr.decl().name())
    return None


def _const_key(z3, expr):
    """Use declaration identity, never a display name, to track constants."""
    return (expr.get_id() if z3.is_const(expr)
            and expr.decl().kind() == z3.Z3_OP_UNINTERPRETED else None)


def _int_value(z3, expr):
    return expr.as_long() if z3.is_int_value(expr) else None


class _GuardEqualityIndex:
    """Recognize shared Int guard atoms once per invocation and Z3 context.

    The enclosing body owns every indexed AST for this index's lifetime. Keys
    are AST identities, not names or hashes; no cache crosses bodies/contexts.
    Negative matches are cached too, without treating malformed atoms as rows.
    """

    def __init__(self, z3, body):
        self.z3 = z3
        self.body = body  # Retain original ASTs; IDs cannot be recycled.
        self.equalities = {}
        self.integer_constants = {}
        self.integer_values = {}

    def _constant(self, expression):
        key = expression.get_id()
        if key not in self.integer_constants:
            z3 = self.z3
            self.integer_constants[key] = (
                key if z3.is_const(expression)
                and expression.decl().kind() == z3.Z3_OP_UNINTERPRETED
                and expression.sort().kind() == z3.Z3_INT_SORT else None)
        return self.integer_constants[key]

    def _integer(self, expression):
        key = expression.get_id()
        if key not in self.integer_values:
            self.integer_values[key] = _int_value(self.z3, expression)
        return self.integer_values[key]

    def equality(self, expression):
        key = expression.get_id()
        if key in self.equalities:
            return self.equalities[key]
        z3 = self.z3
        result = None
        if z3.is_eq(expression) and expression.num_args() == 2:
            left, right = expression.children()
            value = self._integer(left)
            if value is not None:
                constant = self._constant(right)
                if constant is not None:
                    result = right, constant, value
            else:
                value = self._integer(right)
                if value is not None:
                    constant = self._constant(left)
                    if constant is not None:
                        result = left, constant, value
        self.equalities[key] = result
        return result


def _top_conjuncts(z3, body):
    return list(body.children()) if _is_kind(z3, body, z3.Z3_OP_AND) else [body]


def _report_progress(callback, phase, **details):
    if callback is not None:
        callback({"component": "guarded_bool", "phase": phase, **details})


def _bound_holds_for_value(z3, clause, const_key, value):
    """Evaluate a direct unary integer bound at one concrete alias value."""
    if not z3.is_app(clause) or clause.num_args() != 2:
        return False
    kind = clause.decl().kind()
    if kind not in (z3.Z3_OP_LE, z3.Z3_OP_GE):
        return False
    left, right = clause.children()
    if _const_key(z3, left) == const_key and _int_value(z3, right) is not None:
        bound = _int_value(z3, right)
        return value <= bound if kind == z3.Z3_OP_LE else value >= bound
    if _const_key(z3, right) == const_key and _int_value(z3, left) is not None:
        bound = _int_value(z3, left)
        return bound <= value if kind == z3.Z3_OP_LE else bound >= value
    return False


def eliminate_guarded_bool_definitions(body, *, budget_ms=5000,
                                       progress_callback=None):
    """Replace precisely guard-defined Bool/Int pairs, or return ``body``.

    ``budget_ms`` covers recognition and structural proof; None removes that
    deadline. An expired budget,
    malformed/ambiguous guard table, or inconsistent bound causes an exact
    no-op fallback. The structural proof uses only the original reference
    conjuncts: exact interval coverage and unique guard outcomes determine the
    auxiliary values, while direct Int bounds are checked at every table bit.
    """
    import z3

    started = time.monotonic()
    deadline = None if budget_ms is None else started + max(0, budget_ms) / 1000.0

    def expired(phase, phase_started, *, bound_validation_ms=0.0):
        now = time.monotonic()
        if deadline is None or now <= deadline:
            return None
        return GuardedBoolResult(
            body, proof_time_ms=(now - started) * 1000.0,
            fallback_reason=f"{phase} budget exhausted",
            proof_phase=phase,
            proof_phase_time_ms=(now - phase_started) * 1000.0,
            bound_validation_time_ms=bound_validation_ms,
            proof_kind="structural" if phase == "structural" else "none")

    clauses = _top_conjuncts(z3, body)
    _report_progress(progress_callback, "clause_scan.start",
                     top_level_clauses=len(clauses))
    if (budget_ms is not None and budget_ms <= 0) or not _is_kind(z3, body, z3.Z3_OP_AND):
        return GuardedBoolResult(body, fallback_reason="disabled or non-conjunctive body")

    definitions = {}
    direct_bounds = {}
    implications = []
    for clause in clauses:
        timeout = expired("recognition", started)
        if timeout is not None:
            return timeout
        if not z3.is_app(clause):
            continue
        kind = clause.decl().kind()
        if kind == z3.Z3_OP_IMPLIES:
            implications.append(clause)
            continue
        if kind == z3.Z3_OP_EQ and clause.num_args() == 2:
            left, right = clause.children()
            if _is_kind(z3, left, z3.Z3_OP_ITE):
                condition, true_value, false_value = left.children()
                other = right
            elif _is_kind(z3, right, z3.Z3_OP_ITE):
                condition, true_value, false_value = right.children()
                other = left
            else:
                condition = true_value = false_value = other = None
            if condition is not None:
                bool_key, iv_key = _const_key(z3, condition), _const_key(z3, other)
                if (bool_key is not None and iv_key is not None
                        and condition.sort().kind() == z3.Z3_BOOL_SORT
                        and other.sort().kind() == z3.Z3_INT_SORT
                        and _int_value(z3, true_value) == 1
                        and _int_value(z3, false_value) == 0):
                    definitions.setdefault(iv_key, []).append((condition, other, clause))
        if kind not in (z3.Z3_OP_LE, z3.Z3_OP_GE) or clause.num_args() != 2:
            continue
        left, right = clause.children()
        left_key, right_key = _const_key(z3, left), _const_key(z3, right)
        left_int, right_int = _int_value(z3, left), _int_value(z3, right)
        if left_key is not None and right_int is not None:
            const_key = left_key
            bound_kind = "lower" if kind == z3.Z3_OP_GE else "upper"
            value = right_int
        elif right_key is not None and left_int is not None:
            const_key = right_key
            bound_kind = "upper" if kind == z3.Z3_OP_GE else "lower"
            value = left_int
        else:
            continue
        direct_bounds.setdefault(const_key, {"lower": None, "upper": None, "clauses": []})
        record = direct_bounds[const_key]
        if bound_kind == "lower":
            record["lower"] = value if record["lower"] is None else max(record["lower"], value)
        else:
            record["upper"] = value if record["upper"] is None else min(record["upper"], value)
        record["clauses"].append(clause)

    if not definitions:
        _report_progress(progress_callback, "clause_scan.done",
                         definitions=0, direct_bound_symbols=len(direct_bounds))
        return GuardedBoolResult(body)

    _report_progress(progress_callback, "clause_scan.done",
                     definitions=sum(len(rows) for rows in definitions.values()),
                     auxiliary_integers=len(definitions),
                     direct_bound_symbols=len(direct_bounds))

    guard_rows = {}
    equality_index = _GuardEqualityIndex(z3, body)
    index_started = time.monotonic()
    for clause in implications:
        timeout = expired("recognition", index_started)
        if timeout is not None:
            return timeout
        antecedent, consequent = clause.children()
        outcome = equality_index.equality(consequent)
        if outcome is None:
            continue
        _iv, iv_key, bit = outcome
        if iv_key not in definitions or bit not in (0, 1):
            continue
        guard = equality_index.equality(antecedent)
        if guard is None:
            continue
        sequence, _sequence_key, value = guard
        guard_rows.setdefault(iv_key, []).append(
            (sequence, value, bit, clause))

    _report_progress(progress_callback, "guard_rows.indexed",
                     auxiliary_integers=len(guard_rows),
                     rows=sum(len(rows) for rows in guard_rows.values()))

    bound_groups = {}
    recognition_started = time.monotonic()
    for iv_key, definition_rows in definitions.items():
        timeout = expired("recognition", recognition_started)
        if timeout is not None:
            return timeout
        bool_terms = {row[0].get_id(): row[0] for row in definition_rows}
        iv_terms = {row[1].get_id(): row[1] for row in definition_rows}
        if len(bool_terms) != 1 or len(iv_terms) != 1:
            continue
        rows = guard_rows.get(iv_key, [])
        if not rows:
            continue
        sequence_ids = {row[0].get_id() for row in rows}
        values_by_guard = {}
        for sequence, value, bit, clause in rows:
            values_by_guard.setdefault(value, set()).add(bit)
        if len(sequence_ids) != 1 or any(len(bits) != 1 for bits in values_by_guard.values()):
            continue
        sequence = rows[0][0]
        sequence_key = _const_key(z3, sequence)
        bound_record = direct_bounds.get(sequence_key)
        if (bound_record is None or bound_record["lower"] is None
                or bound_record["upper"] is None
                or bound_record["lower"] > bound_record["upper"]):
            continue
        lower, upper = bound_record["lower"], bound_record["upper"]
        bound_clauses = bound_record["clauses"]
        ordered_values = sorted(values_by_guard)
        # Check contiguous coverage without allocating a potentially huge range.
        if (lower > min(ordered_values) or upper < max(ordered_values)
                or len(ordered_values) != upper - lower + 1
                or any(value != lower + offset
                       for offset, value in enumerate(ordered_values))):
            continue
        bool_term = next(iter(bool_terms.values()))
        iv_term = next(iter(iv_terms.values()))
        bridge_rows = [row[2] for row in definition_rows]
        if len(bridge_rows) != 1:
            continue
        # Include every direct numeric bound on the Int alias. The structural
        # check below must validate each one before it can be removed.
        iv_bounds = direct_bounds.get(iv_key, {}).get("clauses", [])
        group_clauses = []
        group_ids = set()
        for clause in [row[3] for row in rows] + bridge_rows + iv_bounds:
            if clause.get_id() not in group_ids:
                group_ids.add(clause.get_id())
                group_clauses.append(clause)
        positive = [sequence == z3.IntVal(value, ctx=sequence.ctx)
                    for value, bits in sorted(values_by_guard.items())
                    if next(iter(bits)) == 1]
        replacement_bool = z3.Or(*positive) if positive else z3.BoolVal(False, ctx=sequence.ctx)
        replacement_iv = z3.If(replacement_bool,
                               z3.IntVal(1, ctx=iv_term.ctx),
                               z3.IntVal(0, ctx=iv_term.ctx))
        bound_groups[iv_key] = {
            "bool": bool_term, "iv": iv_term,
            "replacement_bool": replacement_bool,
            "replacement_iv": replacement_iv,
            "sequence": sequence,
            "iv_key": iv_key,
            "range_bounds": (lower, upper),
            "bound_clauses": bound_clauses,
            "iv_bound_clauses": iv_bounds,
            "group_clauses": group_clauses,
        }

    if not bound_groups:
        _report_progress(progress_callback, "groups.recognized", groups=0)
        return GuardedBoolResult(body)

    _report_progress(progress_callback, "groups.recognized",
                     groups=len(bound_groups))

    # Every retained bound here is a direct comparison between one Int
    # constant and an Int numeral. Their conjunction is satisfiable exactly
    # when the strongest lower bound does not exceed the strongest upper
    # bound. That condition was checked while recognizing every group above.
    # The source bound clauses remain in the relation and are not solver
    # premises for the structural proof.
    bounds_check_started = time.monotonic()
    for group in bound_groups.values():
        lower, upper = group["range_bounds"]
        if lower > upper:
            return GuardedBoolResult(
                body,
                fallback_reason="inconsistent finite guard bounds",
                bound_validation_time_ms=(time.monotonic()
                                          - bounds_check_started) * 1000.0)
    bounds_validation_ms = (time.monotonic() - bounds_check_started) * 1000.0

    bool_ids = [group["bool"].get_id() for group in bound_groups.values()]
    iv_ids = [group["iv"].get_id() for group in bound_groups.values()]
    if len(bool_ids) != len(set(bool_ids)) or len(iv_ids) != len(set(iv_ids)):
        return GuardedBoolResult(body, fallback_reason="guard groups share an auxiliary")
    auxiliary_ids = set(bool_ids) | set(iv_ids)
    # Substitutions are deliberately one-pass. If a guard sequence is itself
    # an auxiliary removed by another group, the replacement can retain a
    # now-unconstrained symbol (and cyclic groups can delete each other's
    # bounds). Reject these dependencies unless a future implementation proves
    # and composes the full dependency DAG.
    if any(group["sequence"].get_id() in auxiliary_ids
           for group in bound_groups.values()):
        return GuardedBoolResult(
            body, fallback_reason="guard groups depend on eliminated auxiliaries")

    # A complete table supplies an exact structural proof for every group:
    # within the retained [lower, upper] interval exactly one listed guard
    # equality holds, so its implication fixes iv to the corresponding bit;
    # the bridge then fixes bool to that same bit. The reverse witness is the
    # concrete assignment bool=table(sequence), iv=table(sequence). After
    # substitution each guard implication and bridge is tautological. Unary
    # iv bounds are the only other clauses removed, so check both possible bit
    # values directly before accepting the group. This avoids thousands of
    # solver constructions without weakening the proof obligation.
    _report_progress(progress_callback, "structural_proof.start",
                     groups=len(bound_groups))
    validation_started = time.monotonic()
    for iv_key, group in list(bound_groups.items()):
        timeout = expired("structural", validation_started,
                          bound_validation_ms=bounds_validation_ms
                          + (time.monotonic() - validation_started) * 1000.0)
        if timeout is not None:
            return timeout
        # Rebuild this group's table from its already indexed guard clauses.
        table = {}
        for _sequence, value, bit, _clause in guard_rows[iv_key]:
            table[value] = bit
        valid = all(_bound_holds_for_value(z3, clause, iv_key, bit)
                    for clause in group["iv_bound_clauses"]
                    for bit in set(table.values()))
        if not valid:
            del bound_groups[iv_key]
            _report_progress(progress_callback, "structural_proof.rejected",
                             iv_name=_const_name(z3, group["iv"]),
                             reason="substituted Int bound is not universally true")
    bounds_validation_ms += (time.monotonic() - validation_started) * 1000.0
    _report_progress(progress_callback, "structural_proof.done",
                     groups=len(bound_groups),
                     elapsed_ms=(time.monotonic() - validation_started) * 1000.0)
    if deadline is not None and time.monotonic() > deadline:
        return GuardedBoolResult(
            body, proof_time_ms=(time.monotonic() - started) * 1000.0,
            fallback_reason="structural proof budget exhausted",
            proof_phase="structural",
            proof_phase_time_ms=(time.monotonic() - validation_started) * 1000.0,
            bound_validation_time_ms=bounds_validation_ms,
            proof_kind="structural")
    if not bound_groups:
        return GuardedBoolResult(
            body,
            proof_time_ms=(time.monotonic() - started) * 1000.0,
            fallback_reason="substituted Int bound is not universally true",
            proof_phase="structural",
            proof_phase_time_ms=(time.monotonic() - validation_started) * 1000.0,
            bound_validation_time_ms=bounds_validation_ms,
            proof_kind="structural")

    _report_progress(progress_callback, "substitution.plan.start",
                     groups=len(bound_groups))
    substitutions = []
    remove_ids = set()
    for group in bound_groups.values():
        substitutions.extend([
            (group["bool"], group["replacement_bool"]),
            (group["iv"], group["replacement_iv"]),
        ])
        remove_ids.update(clause.get_id() for clause in group["group_clauses"])
    retained = [clause for clause in clauses
                if clause.get_id() not in remove_ids]
    _report_progress(progress_callback, "substitution.plan.done",
                     substitutions=len(substitutions),
                     removed_clauses=len(remove_ids),
                     retained_clauses=len(retained))
    # Apply the simultaneous substitution once to the retained conjunction.
    # Calling Z3 once per source clause made each of 21k clauses marshal the
    # same 2k-entry substitution map independently on the large case.
    apply_started = time.monotonic()
    _report_progress(progress_callback, "substitution.apply.start",
                     clauses=len(retained), substitutions=len(substitutions))
    retained_formula = (z3.And(*retained) if retained
                         else z3.BoolVal(True, ctx=body.ctx))
    optimized = z3.substitute(retained_formula, *substitutions)
    _report_progress(progress_callback, "substitution.apply.done",
                     elapsed_ms=(time.monotonic() - apply_started) * 1000.0,
                     clauses=len(retained))
    return GuardedBoolResult(
        optimized, len(bound_groups), len(remove_ids),
        (time.monotonic() - started) * 1000.0,
        proof_phase="complete",
        proof_phase_time_ms=(time.monotonic() - validation_started) * 1000.0,
        bound_validation_time_ms=bounds_validation_ms,
        proof_kind="structural")
