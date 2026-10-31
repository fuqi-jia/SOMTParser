"""Exact, conservative formula rewriting for existential projections.

The caller supplies the complete Boolean body, including observation bridge
equations, and (alias, observed-term) pairs for observable values only. Cost
bridges stay in the body but are deliberately not substitution sources. Before
finite quantifier expansion, a narrow exact cardinality rule is applied only
to root-forall conjuncts beneath conjunctions; it never descends through a
negation, disjunction, implication, or another connective.
"""
from dataclasses import dataclass
from typing import Optional

from .finite_at_most_one import rewrite_top_level_and_conjuncts
from .finite_array_reads import scalarize_finite_array_reads
from .closed_array_indices import normalize_closed_int_array_indices
from .bounded_observed_reads import expand_bounded_observed_reads
from .finite_quantifiers import expand_finite_int_quantifiers
from .guarded_bool_definitions import eliminate_guarded_bool_definitions
from .hidden_functions import encode_hidden_functions


@dataclass(frozen=True)
class Optimization:
    body: object
    scalar_terms: tuple
    eliminated_array_roots: tuple
    retained_array_roots: tuple
    skipped_quantifier_context: bool
    quantifier_expansion: object = None
    cardinality_rewrites: int = 0
    finite_array_read_cells: int = 0
    guarded_bool_groups: int = 0
    guarded_bool_removed_clauses: int = 0
    guarded_bool_proof_time_ms: float = 0.0
    guarded_bool_fallback_reason: str = ""
    guarded_bool_budget_ms: Optional[int] = 0
    guarded_bool_proof_phase: str = ""
    guarded_bool_phase_time_ms: float = 0.0
    guarded_bool_bound_validation_time_ms: float = 0.0
    guarded_bool_proof_kind: str = "none"
    boolean_observation_cells: int = 0
    boolean_observation_roots: tuple = ()
    boolean_observation_weighted_ites: int = 0
    bounded_observed_reads: int = 0
    bounded_observed_read_cells: int = 0
    bounded_observed_table_cells: int = 0


def free_constants(expressions):
    """Return uninterpreted constants occurring free in the supplied ASTs."""
    import z3

    found = {}
    stack = list(expressions)
    visited = set()
    while stack:
        expr = stack.pop()
        expr_id = expr.get_id()
        if expr_id in visited:
            continue
        visited.add(expr_id)
        if z3.is_quantifier(expr):
            stack.append(expr.body())
        elif z3.is_const(expr) and expr.decl().kind() == z3.Z3_OP_UNINTERPRETED:
            found[expr.get_id()] = expr
        elif z3.is_app(expr):
            stack.extend(expr.children())
    return list(found.values())


def contains_quantifier(expression):
    """Whether any quantifier occurs; the optimizer conservatively bails out."""
    import z3

    stack = [expression]
    visited = set()
    while stack:
        expr = stack.pop()
        expr_id = expr.get_id()
        if expr_id in visited:
            continue
        visited.add(expr_id)
        if z3.is_quantifier(expr):
            return True
        if z3.is_app(expr):
            stack.extend(expr.children())
    return False


def _uninterpreted_constant(expr):
    import z3

    return (z3.is_const(expr)
            and expr.decl().kind() == z3.Z3_OP_UNINTERPRETED)


def _array_roots(expr):
    import z3

    return [constant for constant in free_constants([expr])
            if constant.sort().kind() == z3.Z3_ARRAY_SORT]


def _full_concrete_scalar_select_root(expr):
    """Return a root only for a full scalar chain at concrete Int numerals."""
    import z3

    if expr.sort().kind() == z3.Z3_ARRAY_SORT or not z3.is_select(expr):
        return None
    current = expr
    saw_select = False
    while z3.is_select(current):
        children = current.children()
        # Multi-domain arrays have one index child per domain. Keep them
        # conservative until the projection proof handles that shape.
        if len(children) != 2:
            return None
        array_expr, index_expr = children
        if (index_expr.sort().kind() != z3.Z3_INT_SORT
                or not z3.is_int_value(index_expr)):
            return None
        saw_select = True
        current = array_expr
    if not saw_select or not _uninterpreted_constant(current):
        return None
    if current.sort().kind() != z3.Z3_ARRAY_SORT:
        return None
    return current


def _substitute(expr, substitutions):
    import z3

    return z3.substitute(expr, *substitutions) if substitutions else expr


def _report_progress(callback, phase, **details):
    if callback is not None:
        callback({"component": "projection", "phase": phase, **details})


def optimize_observation_projection(body, observable_bridges, *,
                                   guarded_bool_budget_ms=5000,
                                   progress_callback=None):
    """Compress exact finite cardinality conjuncts, then project observations.

    Args:
        body: Boolean AST containing constraints and every bridge equation.
        observable_bridges: iterable of ``(fresh_alias, candidate_value)``.
            Do not pass objective/cost bridges here.

    Each observation alias must be a distinct fresh scalar constant absent
    from the source body before bridge equations are added. This is the same
    freshness discipline as the CP checker's FreshConst aliases. Direct
    scalar constants are replaced by their first observed alias
    throughout the whole body. Array roots are replaced only when every bridge
    mentioning that root is a full scalar Select chain with concrete Int
    numeral indices, and the root disappears from the body after simultaneous
    replacement of that root's observed terms. Otherwise every proposed
    replacement for that root is rolled back. ``guarded_bool_budget_ms`` bounds
    the reference-only proof phase for eliminating finite guard-defined
    Bool/Int auxiliaries; callers should deduct it from any total verification
    budget. None removes this deadline. The configured value is included in
    the returned metadata.
    """
    import z3

    bridges = list(observable_bridges)
    for alias, term in bridges:
        if alias.sort() != term.sort():
            raise ValueError("observation alias and candidate term sorts differ")

    _report_progress(progress_callback, "guarded_bool.start",
                     budget_ms=guarded_bool_budget_ms)
    guarded = eliminate_guarded_bool_definitions(
        body, budget_ms=guarded_bool_budget_ms,
        progress_callback=progress_callback)
    body = guarded.body
    _report_progress(
        progress_callback, "guarded_bool.done",
        elapsed_ms=guarded.proof_time_ms,
        groups=guarded.group_count,
        fallback_reason=guarded.fallback_reason)

    cardinality = rewrite_top_level_and_conjuncts(body)
    body = cardinality.formula
    _report_progress(progress_callback, "cardinality.done",
                     rewrite_count=cardinality.rewrite_count)
    expansion = None
    if contains_quantifier(body):
        _report_progress(progress_callback, "quantifier_expansion.start")
        expanded = expand_finite_int_quantifiers(body)
        expansion = expanded.stats
        body = expanded.formula
        _report_progress(progress_callback, "quantifier_expansion.done",
                         stats=str(expansion))
        if contains_quantifier(body):
            return Optimization(
                body, (), (), (), True, expansion,
                cardinality.rewrite_count,
                guarded_bool_groups=guarded.group_count,
                guarded_bool_removed_clauses=guarded.removed_clause_count,
                guarded_bool_proof_time_ms=guarded.proof_time_ms,
                guarded_bool_fallback_reason=guarded.fallback_reason,
                guarded_bool_budget_ms=guarded_bool_budget_ms,
                guarded_bool_proof_phase=guarded.proof_phase,
                guarded_bool_phase_time_ms=guarded.proof_phase_time_ms,
                guarded_bool_bound_validation_time_ms=(
                    guarded.bound_validation_time_ms),
                guarded_bool_proof_kind=guarded.proof_kind)

    # Ordinary function macros also create closed arithmetic indices outside
    # quantified instances. Normalize only select/store indices before exact
    # numeral-cell matching; symbolic/undefined indices still block projection.
    normalization = normalize_closed_int_array_indices(body)
    body = normalization.formula
    bridges = [(alias, normalize_closed_int_array_indices(term).formula)
               for alias, term in bridges]
    _report_progress(progress_callback, "closed_array_indices.done",
                     rewritten_index_positions=normalization.rewritten_index_positions)

    # Mandatory scalar/cell bounds can make dynamic nested reads finite.
    # Keep those original guards and require every possible cell to be observed
    # before replacing a read. Array shape alone never supplies a value domain.
    bounded_reads = expand_bounded_observed_reads(body, bridges)
    body = bounded_reads.formula
    _report_progress(progress_callback, "bounded_observed_reads.done",
                     reads=bounded_reads.expanded_reads,
                     cells=bounded_reads.expanded_cells,
                     table_cells=bounded_reads.materialized_cells)

    # A Bool observed through Int 0/1 has a reversible, domain-preserving
    # encoding. Apply it to the complete body (including all cost bridges).
    from .boolean_observation_projection import eliminate_boolean_observations
    boolean_observations = eliminate_boolean_observations(body, bridges)
    body = boolean_observations.body
    bridges = list(boolean_observations.bridges)
    _report_progress(progress_callback, "boolean_observations.done",
                     cells=boolean_observations.observed_boolean_cells,
                     weighted_ites=boolean_observations.weighted_ites,
                     eliminated_roots=boolean_observations.eliminated_roots,
                     retained_roots=boolean_observations.retained_roots)

    # First remove directly observed scalar constants. Use one representative
    # alias for duplicates; the original bridge equations remain in `body`, so
    # subsequent duplicates still enforce equality to that representative.
    visible_alias_ids = {alias.get_id() for alias, _ in bridges}
    scalar_alias_by_term = {}
    scalar_substitutions = []
    scalar_terms = []
    for alias, term in bridges:
        if (term.sort().kind() == z3.Z3_ARRAY_SORT
                or term.get_id() in visible_alias_ids
                or not _uninterpreted_constant(term)):
            continue
        term_id = term.get_id()
        if term_id not in scalar_alias_by_term:
            scalar_alias_by_term[term_id] = alias
            scalar_substitutions.append((term, alias))
            scalar_terms.append(term)

    current = _substitute(body, scalar_substitutions)
    _report_progress(progress_callback, "scalar_projection.done",
                     substitutions=len(scalar_substitutions))
    rewritten_bridges = []
    for alias, term in bridges:
        # Direct scalar observations already have their exact replacement.
        # Sending the complete substitution table through the Python/Z3
        # boundary for every such leaf costs quadratic work in the number
        # of observations. Composite observations still need simultaneous
        # substitution, including references to other observed scalars.
        rewritten = scalar_alias_by_term.get(term.get_id())
        if rewritten is None:
            rewritten = _substitute(term, scalar_substitutions)
        rewritten_bridges.append((alias, rewritten))

    # An array root is eligible only if every observation that mentions it is
    # itself a full scalar Select chain with concrete Int numeral indices.
    groups = {}
    for alias, term in rewritten_bridges:
        roots = _array_roots(term)
        if not roots:
            continue
        chain_root = _full_concrete_scalar_select_root(term)
        chain_id = chain_root.get_id() if chain_root is not None else None
        for root in roots:
            group = groups.setdefault(root.get_id(), {
                "root": root,
                "safe": True,
                "terms": {},
            })
            if chain_id != root.get_id():
                group["safe"] = False
                continue
            # Duplicate observations keep their separate bridge equations but
            # use the first alias as the single replacement representative.
            group["terms"].setdefault(term.get_id(), (term, alias))

    eliminated = []
    retained = []
    array_substitutions = []
    for root_id, group in groups.items():
        root = group["root"]
        root_name = str(root.decl().name())
        if not group["safe"] or not group["terms"]:
            retained.append(root_name)
            continue
        proposed = list(array_substitutions)
        proposed.extend(group["terms"].values())
        candidate = _substitute(_substitute(body, scalar_substitutions), proposed)
        candidate_roots = {c.get_id() for c in free_constants([candidate])
                           if c.sort().kind() == z3.Z3_ARRAY_SORT}
        if root_id in candidate_roots:
            # Any residual symbolic read, prefix use, whole-array relation,
            # or other use blocks elimination of the entire root group.
            retained.append(root_name)
            continue
        array_substitutions = proposed
        current = candidate
        eliminated.append(root_name)

    # Keep the existing direct-definition elimination first: it can substitute
    # definitional cells without introducing existential scalar witnesses.
    from .defined_array_cells import eliminate_defined_array_cells
    visible_array_roots = {
        root.get_id()
        for alias, term in bridges
        if alias.sort().kind() == z3.Z3_ARRAY_SORT
        or term.sort().kind() == z3.Z3_ARRAY_SORT
        for root in _array_roots(term)
    }
    # Observed cell substitution often removes the only array root (for
    # example, a fully observed output array). In that case both array
    # eliminators are no-ops, but each would otherwise rescan the complete
    # Boolean DAG. Compute the remaining roots once, and invoke each helper
    # only when its corresponding root set is nonempty.
    remaining_roots = _array_roots(current)
    definition_retained = ()
    if remaining_roots:
        nonvisible_arrays = [root for root in remaining_roots
                             if root.get_id() not in visible_array_roots]
        if nonvisible_arrays:
            definitions = eliminate_defined_array_cells(current, nonvisible_arrays)
            current = definitions.body
            eliminated.extend(definitions.eliminated_roots)
            definition_retained = definitions.retained_roots

        # For the remaining hidden roots, a finite set of ground scalar reads
        # is exactly their finite cell tuple under existential projection.
        # Keep every original assertion and bridge equation while replacing
        # each distinct read by a fresh scalar witness. Observable roots stay
        # excluded; unsupported array uses roll back by root.
        remaining_roots = _array_roots(current)
        remaining_hidden_arrays = [root for root in remaining_roots
                                   if root.get_id() not in visible_array_roots]
        remaining_visible_arrays = [root for root in remaining_roots
                                    if root.get_id() in visible_array_roots]
        if remaining_roots:
            finite_reads = scalarize_finite_array_reads(
                current, remaining_hidden_arrays,
                visible_roots=remaining_visible_arrays)
            current = finite_reads.body
            eliminated.extend(finite_reads.eliminated_roots)
            retained.extend(finite_reads.retained_roots)
            finite_array_read_cells = finite_reads.cell_counts
        else:
            finite_array_read_cells = ()
        retained.extend(definition_retained)
    else:
        finite_array_read_cells = ()
    _report_progress(progress_callback, "array_projection.done",
                     eliminated_roots=len(eliminated),
                     retained_roots=len(retained))
    eliminated = list(dict.fromkeys(eliminated))
    eliminated_names = set(eliminated)
    retained = [name for name in dict.fromkeys(retained)
                if name not in eliminated_names]
    return Optimization(
        current, tuple(str(t) for t in scalar_terms),
        tuple(eliminated), tuple(retained), False, expansion,
        cardinality.rewrite_count,
        sum(count for _, count in finite_array_read_cells),
        guarded.group_count, guarded.removed_clause_count,
        guarded.proof_time_ms, guarded.fallback_reason,
        guarded_bool_budget_ms, guarded.proof_phase,
        guarded.proof_phase_time_ms, guarded.bound_validation_time_ms,
        guarded.proof_kind,
        boolean_observation_cells=boolean_observations.observed_boolean_cells,
        boolean_observation_roots=boolean_observations.eliminated_roots,
        boolean_observation_weighted_ites=boolean_observations.weighted_ites,
        bounded_observed_reads=bounded_reads.expanded_reads,
        bounded_observed_read_cells=bounded_reads.expanded_cells,
        bounded_observed_table_cells=bounded_reads.materialized_cells)


def existential_projection(body, visible_aliases):
    """Hide private constants and function interpretations, preserving aliases.

    Free uninterpreted functions are private modeling choices just like local
    constants. Leaving them free would compare two models at fixed auxiliary
    relations instead of comparing the outputs each complete model permits.
    """
    import z3

    body, function_arrays = encode_hidden_functions(body)
    if function_arrays:
        # Ground finite applications admit the existing exact cell-witness
        # reduction. Quantified or symbolic indices retain the total arrays.
        body = scalarize_finite_array_reads(body, function_arrays).body
    visible_ids = {alias.get_id() for alias in visible_aliases}
    hidden = [constant for constant in free_constants([body])
              if constant.get_id() not in visible_ids]
    return z3.Exists(hidden, body) if hidden else body
