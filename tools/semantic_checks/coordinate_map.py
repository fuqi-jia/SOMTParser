"""Explicit finite coordinate maps with proof-gated reconstruction.

This is a checker-side extension. It does not rewrite or constrain either
model. It accepts equal Bool/Int sorts only and refuses when a dropped
candidate coordinate cannot be proved equal to its declared reconstruction.
"""
from dataclasses import dataclass, field
from itertools import product, count
import hashlib


class ObservableMapRefusal(ValueError):
    """Typed refusal: callers must not report equivalence after this failure."""

    code = "E_OBSERVABLE_COORDINATE_MAP"
    status = "translation-refused"

    def __init__(self, reason, message):
        self.reason = reason
        super().__init__(message)


@dataclass(frozen=True)
class CoordinatePair:
    reference_index: tuple
    candidate_index: tuple
    reference_term: object
    candidate_term: object


@dataclass(frozen=True)
class ReconstructionObligation:
    candidate_index: tuple
    candidate_term: object
    reconstruction_term: object


@dataclass(frozen=True)
class CoordinateMapPlan:
    reference_name: str
    candidate_name: str
    sort: str
    reference_shape: tuple
    candidate_shape: tuple
    pairs: tuple
    reconstruction_obligations: tuple
    hidden_candidate_indices: tuple = ()


@dataclass(frozen=True)
class VerifiedCoordinateMap:
    plan: CoordinateMapPlan
    proved_candidate_indices: tuple
    proof_statuses: tuple
    candidate_context: object
    candidate_assertion_fingerprint: str
    plan_fingerprint: str
    _verification_token: object = field(default=None, repr=False, compare=False)


@dataclass(frozen=True)
class ObservationBridges:
    aliases: tuple
    reference_bridges: tuple
    candidate_bridges: tuple
    reference_context: object
    reference_assertion_fingerprint: str
    candidate_assertion_fingerprint: str
    _bridge_token: object = field(default=None, repr=False, compare=False)


@dataclass(frozen=True)
class CandidateBridgeSet:
    bridges: tuple
    public_aliases: tuple
    private_aliases: tuple
    candidate_context: object
    _bridge_token: object = field(default=None, repr=False, compare=False)

    def hide_private_aliases(self, projected_formula):
        """Hide reconstructed coordinates after the normal full projection."""
        import z3
        if (_CANDIDATE_BRIDGE_RECEIPTS.get(id(self)) is not self
                or self._bridge_token is not _BRIDGE_TOKEN):
            raise ObservableMapRefusal("invalid-bridges", "candidate bridge receipt is invalid or has been altered")
        if projected_formula.ctx is not self.candidate_context:
            raise ObservableMapRefusal("proof-context-mismatch", "projected formula is from a different Z3 context")
        if _z3_sort_name(projected_formula) != "Bool":
            raise ObservableMapRefusal("invalid-projection", "projected candidate relation must be Boolean")
        return z3.Exists(self.private_aliases, projected_formula) if self.private_aliases else projected_formula


def _context_identity(expression):
    return id(expression.ctx)


def _assertion_fingerprint(assertions):
    payload = "\n".join(assertion.sexpr() for assertion in assertions).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def _plan_fingerprint(plan):
    pieces = [plan.reference_name, plan.candidate_name, plan.sort,
              repr(plan.reference_shape), repr(plan.candidate_shape)]
    pieces.extend(f"P:{pair.reference_index}:{pair.candidate_index}:"
                  f"{pair.reference_term.sexpr()}:{pair.candidate_term.sexpr()}"
                  for pair in plan.pairs)
    pieces.extend(f"R:{item.candidate_index}:{item.candidate_term.sexpr()}:"
                  f"{item.reconstruction_term.sexpr()}"
                  for item in plan.reconstruction_obligations)
    pieces.extend(f"H:{index}" for index in plan.hidden_candidate_indices)
    return hashlib.sha256("\n".join(pieces).encode("utf-8")).hexdigest()


_VERIFICATION_TOKEN = object()
_BRIDGE_TOKEN = object()
_PLAN_RECEIPTS = {}
_VERIFIED_RECEIPTS = {}
_OBSERVATION_RECEIPTS = {}
_CANDIDATE_BRIDGE_RECEIPTS = {}
_FRESH_ALIAS_COUNTER = count()


def _require_verified(verified_map):
    if not isinstance(verified_map, VerifiedCoordinateMap):
        raise ObservableMapRefusal("unproved-map", "coordinate mapping must pass reconstruction proof first")
    expected_indices = tuple(item.candidate_index for item in verified_map.plan.reconstruction_obligations)
    receipt = _VERIFIED_RECEIPTS.get(id(verified_map))
    if (verified_map._verification_token is not _VERIFICATION_TOKEN
            or receipt is not verified_map
            or verified_map.proved_candidate_indices != expected_indices
            or verified_map.proof_statuses != tuple("unsat" for _ in expected_indices)
            or verified_map.plan_fingerprint != _plan_fingerprint(verified_map.plan)):
        raise ObservableMapRefusal("unproved-map", "coordinate proof receipt is invalid or has been altered")


def _fresh_constant(sort, prefix, protected_ids, context):
    import z3
    while True:
        ordinal = next(_FRESH_ALIAS_COUNTER)
        name = f"{prefix}_{ordinal}"
        alias = z3.Const(name, sort)
        if _context_identity(alias) != id(context):
            raise ObservableMapRefusal("proof-context-mismatch", "fresh alias was created in a different Z3 context")
        if alias.get_id() not in protected_ids:
            protected_ids.add(alias.get_id())
            return alias


def _shape(value, where):
    if not isinstance(value, (list, tuple)):
        raise ObservableMapRefusal("invalid-metadata", f"{where} shape must be a finite sequence")
    if any(type(size) is not int or size <= 0 for size in value):
        raise ObservableMapRefusal("invalid-metadata", f"{where} dimensions must be positive integers")
    return tuple(value)


def _indices(shape):
    return list(product(*(range(size) for size in shape))) if shape else [()]


def _check_index(index, shape, where):
    if not isinstance(index, (list, tuple)) or any(type(i) is not int for i in index):
        raise ObservableMapRefusal("invalid-map", f"{where} coordinate must be an integer sequence")
    index = tuple(index)
    if len(index) != len(shape) or any(i < 0 or i >= n for i, n in zip(index, shape)):
        raise ObservableMapRefusal("invalid-map", f"{where} coordinate {index} is outside shape {shape}")
    return index


def _z3_sort_name(term):
    import z3
    try:
        if term.sort() == z3.BoolSort(ctx=term.ctx):
            return "Bool"
        if term.sort() == z3.IntSort(ctx=term.ctx):
            return "Int"
    except (AttributeError, TypeError):
        return None
    return None


def _literal(sort, value, where, context):
    import z3
    if sort == "Bool" and type(value) is bool:
        return z3.BoolVal(value, ctx=context)
    if sort == "Int" and type(value) is int:
        return z3.IntVal(value, ctx=context)
    raise ObservableMapRefusal("invalid-reconstruction",
                               f"{where} reconstruction literal does not have sort {sort}")


def build_coordinate_map(reference_metadata, candidate_metadata, map_metadata,
                         reference_terms, candidate_terms):
    """Validate an explicit map and return terms plus reconstruction obligations.

    Metadata records have ``name``, ``shape`` and ``sort``. ``map_metadata``
    has ``reference_name``, ``candidate_name``, ``coordinates`` (one explicit
    reference-index/candidate-index pair per reference cell), and
    ``reconstruct`` (one typed literal for every candidate cell not directly
    mapped). By default both term mappings cover their entire shapes. With
    reference_metadata.sparse=True, reference_terms instead lists exactly the
    observed cells (alternatively use explicit observed_indices), and
    hidden_candidate_indices explicitly lists candidate
    cells to hide by existential projection. These cells' constraints remain
    in the complete candidate relation; hiding is not reconstruction.
    """
    if not all(isinstance(value, dict) for value in
               (reference_metadata, candidate_metadata, map_metadata)):
        raise ObservableMapRefusal("invalid-metadata", "observable and map metadata must be objects")
    ref_name = reference_metadata.get("name")
    cand_name = candidate_metadata.get("name")
    if not isinstance(ref_name, str) or not ref_name or not isinstance(cand_name, str) or not cand_name:
        raise ObservableMapRefusal("invalid-metadata", "observable names must be nonempty strings")
    if map_metadata.get("reference_name") != ref_name or map_metadata.get("candidate_name") != cand_name:
        raise ObservableMapRefusal("invalid-map", "map names do not match the supplied observables")
    ref_shape = _shape(reference_metadata.get("shape"), f"reference {ref_name}")
    cand_shape = _shape(candidate_metadata.get("shape"), f"candidate {cand_name}")
    ref_sort = reference_metadata.get("sort")
    cand_sort = candidate_metadata.get("sort")
    if ref_sort not in {"Bool", "Int"} or cand_sort not in {"Bool", "Int"}:
        raise ObservableMapRefusal("unsupported-sort", "coordinate maps currently support Bool and Int only")
    if ref_sort != cand_sort:
        raise ObservableMapRefusal("sort-mismatch", "coordinate maps require exactly equal Bool/Int sorts")

    # Retain both public sparse metadata forms. An explicit observed list is
    # caller-owned just like sparse=True plus an explicit reference-term map.
    raw_observed = reference_metadata.get("observed_indices")
    sparse = reference_metadata.get("sparse", raw_observed is not None)
    if type(sparse) is not bool:
        raise ObservableMapRefusal("invalid-metadata", "sparse must be an explicit Boolean")
    if not isinstance(reference_terms, dict):
        raise ObservableMapRefusal("invalid-reference-terms", "reference terms must list observed coordinates")
    if raw_observed is not None:
        if not isinstance(raw_observed, list):
            raise ObservableMapRefusal("invalid-map", "observed_indices must be an explicit list")
        expected_ref = set()
        for value in raw_observed:
            index = _check_index(value, ref_shape, "reference observed")
            if index in expected_ref:
                raise ObservableMapRefusal("duplicate-reference-coordinate", f"reference observed coordinate {index} is repeated")
            expected_ref.add(index)
        if not sparse and expected_ref != set(_indices(ref_shape)):
            raise ObservableMapRefusal("invalid-metadata", "partial observed_indices require sparse observables")
    else:
        expected_ref = set(reference_terms) if sparse else set(_indices(ref_shape))
    if sparse and not expected_ref:
        raise ObservableMapRefusal("reference-coverage", "sparse reference mapping must observe at least one coordinate")
    expected_cand = set(_indices(cand_shape))
    if not isinstance(reference_terms, dict) or set(reference_terms) != expected_ref:
        raise ObservableMapRefusal("invalid-reference-terms", "reference terms must cover every reference coordinate exactly")
    if not isinstance(candidate_terms, dict) or set(candidate_terms) != expected_cand:
        raise ObservableMapRefusal("invalid-candidate-terms", "candidate terms must cover every candidate coordinate exactly")
    for index in reference_terms:
        _check_index(index, ref_shape, "reference term")
    for index in candidate_terms:
        _check_index(index, cand_shape, "candidate term")
    for index, term in reference_terms.items():
        if _z3_sort_name(term) != ref_sort:
            raise ObservableMapRefusal("sort-mismatch", f"reference term {index} disagrees with declared sort {ref_sort}")
    for index, term in candidate_terms.items():
        if _z3_sort_name(term) != cand_sort:
            raise ObservableMapRefusal("sort-mismatch", f"candidate term {index} disagrees with declared sort {cand_sort}")
    context_ids = {_context_identity(term) for term in
                   list(reference_terms.values()) + list(candidate_terms.values())}
    if len(context_ids) != 1:
        raise ObservableMapRefusal("proof-context-mismatch", "reference and candidate terms must share one Z3 context")

    raw_pairs = map_metadata.get("coordinates")
    if not isinstance(raw_pairs, list):
        raise ObservableMapRefusal("invalid-map", "coordinates must be an explicit list")
    pairs = []
    seen_ref = set()
    seen_cand = set()
    for item in raw_pairs:
        if not isinstance(item, dict):
            raise ObservableMapRefusal("invalid-map", "each coordinate mapping must be an object")
        ri = _check_index(item.get("reference_index"), ref_shape, "reference")
        ci = _check_index(item.get("candidate_index"), cand_shape, "candidate")
        if ri in seen_ref:
            raise ObservableMapRefusal("duplicate-reference-coordinate", f"reference coordinate {ri} is mapped more than once")
        if ci in seen_cand:
            raise ObservableMapRefusal("duplicate-candidate-coordinate", f"candidate coordinate {ci} is mapped more than once")
        if ri not in expected_ref:
            raise ObservableMapRefusal("reference-coverage", f"reference coordinate {ri} is not an observed cell")
        seen_ref.add(ri)
        seen_cand.add(ci)
        pairs.append(CoordinatePair(ri, ci, reference_terms[ri], candidate_terms[ci]))
    if seen_ref != expected_ref:
        missing = sorted(expected_ref - seen_ref)
        extra = sorted(seen_ref - expected_ref)
        raise ObservableMapRefusal("reference-coverage", f"reference map coverage mismatch; missing={missing}, extra={extra}")

    raw_reconstruct = map_metadata.get("reconstruct")
    if not isinstance(raw_reconstruct, list):
        raise ObservableMapRefusal("invalid-reconstruction", "reconstruct must explicitly list every omitted candidate coordinate")
    raw_hidden = map_metadata.get("hidden_candidate_indices", [] if not sparse else None)
    if not isinstance(raw_hidden, list):
        raise ObservableMapRefusal("invalid-map", "sparse maps require an explicit hidden_candidate_indices list")
    if raw_hidden and not sparse:
        raise ObservableMapRefusal("invalid-map", "only explicit sparse observables may hide candidate coordinates")
    hidden = set()
    for index in raw_hidden:
        ci = _check_index(index, cand_shape, "hidden candidate")
        if ci in hidden:
            raise ObservableMapRefusal("duplicate-hidden-coordinate", f"candidate coordinate {ci} is hidden more than once")
        if ci in seen_cand:
            raise ObservableMapRefusal("mapped-coordinate-hidden", f"mapped candidate coordinate {ci} cannot also be hidden")
        hidden.add(ci)
    expected_omitted = expected_cand - seen_cand - hidden
    obligations = []
    seen_reconstruction = set()
    for item in raw_reconstruct:
        if not isinstance(item, dict):
            raise ObservableMapRefusal("invalid-reconstruction", "each reconstruction must be an object")
        ci = _check_index(item.get("candidate_index"), cand_shape, "reconstruction candidate")
        if item.get("sort", cand_sort) != cand_sort:
            raise ObservableMapRefusal("sort-mismatch", f"reconstruction for {ci} declares a different sort")
        if ci in seen_reconstruction:
            raise ObservableMapRefusal("duplicate-reconstruction", f"candidate coordinate {ci} is reconstructed more than once")
        if ci in seen_cand:
            raise ObservableMapRefusal("mapped-coordinate-reconstruction", f"mapped candidate coordinate {ci} cannot also be omitted")
        if ci in hidden:
            raise ObservableMapRefusal("hidden-coordinate-reconstruction", f"hidden candidate coordinate {ci} cannot also be reconstructed")
        seen_reconstruction.add(ci)
        reconstruction = _literal(cand_sort, item.get("value"),
                                  f"candidate coordinate {ci}", candidate_terms[ci].ctx)
        obligations.append(ReconstructionObligation(ci, candidate_terms[ci], reconstruction))
    if seen_reconstruction != expected_omitted:
        missing = sorted(expected_omitted - seen_reconstruction)
        extra = sorted(seen_reconstruction - expected_omitted)
        raise ObservableMapRefusal("candidate-coverage", f"candidate map coverage mismatch; omitted cells need exact reconstructions; missing={missing}, extra={extra}")

    plan = CoordinateMapPlan(ref_name, cand_name, ref_sort, ref_shape, cand_shape,
                             tuple(pairs), tuple(obligations), tuple(sorted(hidden)))
    _PLAN_RECEIPTS[id(plan)] = plan
    return plan


def _free_constant_ids(expressions):
    import z3
    found = set()
    visited = set()
    stack = list(expressions)
    while stack:
        expr = stack.pop()
        expr_id = expr.get_id()
        if expr_id in visited:
            continue
        visited.add(expr_id)
        if z3.is_quantifier(expr):
            stack.append(expr.body())
        elif z3.is_const(expr) and expr.decl().kind() == z3.Z3_OP_UNINTERPRETED:
            found.add(expr_id)
        elif z3.is_app(expr):
            stack.extend(expr.children())
    return found


def verify_reconstruction(plan, candidate_assertions, solver_factory=None,
                          timeout_ms=5000):
    """Prove every omitted candidate cell equals its declared reconstruction.

    Each obligation checks UNSAT of complete candidate assertions plus a
    disequality. SAT means a counterexample; unknown (including timeout) is a
    typed refusal. Pass the full candidate relation including declaration
    domains, not a satisfiability-only abstraction.
    """
    import z3
    if _PLAN_RECEIPTS.get(id(plan)) is not plan:
        raise ObservableMapRefusal("invalid-map", "proof requires a map returned by build_coordinate_map")
    assertions = list(candidate_assertions)
    if any(_z3_sort_name(a) != "Bool" for a in assertions):
        raise ObservableMapRefusal("invalid-proof-context", "candidate proof context must contain Boolean formulas")
    context_terms = assertions + [item.candidate_term for item in plan.reconstruction_obligations]
    if not context_terms and plan.pairs:
        context_terms = [plan.pairs[0].candidate_term]
    if context_terms and any(_context_identity(term) != _context_identity(context_terms[0])
                             for term in context_terms):
        raise ObservableMapRefusal("proof-context-mismatch", "candidate assertions and reconstruction terms must share one Z3 context")
    candidate_context = context_terms[0].ctx if context_terms else None
    if solver_factory is None:
        solver_factory = lambda: z3.Solver(ctx=candidate_context)
    proven = []
    statuses = []
    for obligation in plan.reconstruction_obligations:
        solver = solver_factory()
        if timeout_ms is not None:
            solver.set(timeout=timeout_ms)
        solver.add(*assertions)
        solver.add(obligation.candidate_term != obligation.reconstruction_term)
        try:
            status = solver.check()
        except Exception as exc:
            raise ObservableMapRefusal("proof-error",
                f"reconstruction proof for {obligation.candidate_index} failed to run: {exc}") from exc
        statuses.append(str(status))
        if status != z3.unsat:
            if status == z3.unknown:
                reason = solver.reason_unknown() if hasattr(solver, "reason_unknown") else "unknown"
                raise ObservableMapRefusal("proof-unknown",
                    f"reconstruction proof for candidate coordinate {obligation.candidate_index} was unknown ({reason})")
            raise ObservableMapRefusal("proof-counterexample",
                f"candidate coordinate {obligation.candidate_index} is not fixed to its declared reconstruction")
        proven.append(obligation.candidate_index)
    receipt = VerifiedCoordinateMap(plan, tuple(proven), tuple(statuses), candidate_context,
                                    _assertion_fingerprint(assertions), _plan_fingerprint(plan),
                                    _VERIFICATION_TOKEN)
    _VERIFIED_RECEIPTS[id(receipt)] = receipt
    return receipt


def fresh_observation_bridges(verified_map, reference_assertions=(), candidate_assertions=(),
                              prefix="obs"):
    """Create shared fresh aliases and preserve one bridge per reference cell.

    The resulting reference/candidate bridge lists should be passed to the
    existing `reference_projection` and `candidate_projection` respectively,
    together with the original complete assertion lists. These bridge
    equations expose the entire mapped relation; they are not a replacement
    for either model's constraints.
    """
    import z3
    _require_verified(verified_map)
    plan = verified_map.plan
    candidate_assertions = list(candidate_assertions)
    if _assertion_fingerprint(candidate_assertions) != verified_map.candidate_assertion_fingerprint:
        raise ObservableMapRefusal("proof-context-mismatch", "candidate projection assertions differ from the proved reconstruction context")
    reference_assertions = list(reference_assertions)
    all_context_exprs = reference_assertions + candidate_assertions
    all_context_exprs.extend(pair.reference_term for pair in plan.pairs)
    all_context_exprs.extend(pair.candidate_term for pair in plan.pairs)
    if all_context_exprs and any(_context_identity(expr) != id(verified_map.candidate_context)
                                 for expr in all_context_exprs):
        raise ObservableMapRefusal("proof-context-mismatch", "reference/candidate projection is from a different Z3 context")
    protected = _free_constant_ids(all_context_exprs)
    for pair in plan.pairs:
        protected |= _free_constant_ids([pair.reference_term, pair.candidate_term])
    aliases = []
    for ordinal, pair in enumerate(plan.pairs):
        alias = _fresh_constant(pair.reference_term.sort(), f"{prefix}_{ordinal}",
                                protected, verified_map.candidate_context)
        if aliases and alias.sort() != aliases[0].sort():
            raise ObservableMapRefusal("sort-mismatch", "mapped aliases must all have the declared observable sort")
        aliases.append(alias)
    if len({alias.get_id() for alias in aliases}) != len(aliases):
        raise ObservableMapRefusal("alias-not-fresh", "generated observation aliases are not distinct")
    ref_bridges = tuple(zip(aliases, (pair.reference_term for pair in plan.pairs)))
    cand_bridges = tuple(zip(aliases, (pair.candidate_term for pair in plan.pairs)))
    receipt = ObservationBridges(tuple(aliases), ref_bridges, cand_bridges,
                                 plan.pairs[0].reference_term.ctx,
                                 _assertion_fingerprint(list(reference_assertions)),
                                 verified_map.candidate_assertion_fingerprint,
                                 _BRIDGE_TOKEN)
    _OBSERVATION_RECEIPTS[id(receipt)] = receipt
    return receipt


def complete_candidate_bridges(verified_map, observation_bridges, candidate_assertions,
                               prefix="reconstructed"):
    """Expose all candidate coordinates during projection, hiding only proved ones.

    Pass ``result.bridges`` to the ordinary candidate projection together with
    the exact proved assertions. Then call ``result.hide_private_aliases`` on
    its formula. This lets projection eliminate array roots read solely at
    concrete coordinates while preserving the full relation; reconstructed
    cells remain existentially hidden from the public observable tuple.
    """
    import z3
    _require_verified(verified_map)
    if (_OBSERVATION_RECEIPTS.get(id(observation_bridges)) is not observation_bridges
            or observation_bridges._bridge_token is not _BRIDGE_TOKEN):
        raise ObservableMapRefusal("invalid-bridges", "observation bridge receipt is invalid or has been altered")
    assertions = list(candidate_assertions)
    if _assertion_fingerprint(assertions) != verified_map.candidate_assertion_fingerprint:
        raise ObservableMapRefusal("proof-context-mismatch", "candidate bridge context differs from the proved context")
    if len(observation_bridges.candidate_bridges) != len(verified_map.plan.pairs):
        raise ObservableMapRefusal("invalid-bridges", "one public bridge is required for every reference coordinate")
    if (len(observation_bridges.candidate_bridges) != len(verified_map.plan.pairs)
            or len(observation_bridges.reference_bridges) != len(verified_map.plan.pairs)
            or len(observation_bridges.aliases) != len(verified_map.plan.pairs)):
        raise ObservableMapRefusal("invalid-bridges", "one public bridge is required for every mapped coordinate")
    for ordinal, (alias, term) in enumerate(observation_bridges.candidate_bridges):
        pair = verified_map.plan.pairs[ordinal]
        ref_alias, ref_term = observation_bridges.reference_bridges[ordinal]
        if term.get_id() != pair.candidate_term.get_id() or ref_term.get_id() != pair.reference_term.get_id():
            raise ObservableMapRefusal("invalid-bridges", "bridge terms differ from the explicitly proved coordinate map")
        if alias.get_id() != ref_alias.get_id() or alias.get_id() != observation_bridges.aliases[ordinal].get_id():
            raise ObservableMapRefusal("invalid-bridges", "reference and candidate bridges must share the recorded public alias")
        if _context_identity(alias) != id(verified_map.candidate_context) or _context_identity(term) != id(verified_map.candidate_context):
            raise ObservableMapRefusal("proof-context-mismatch", "public candidate bridges use a different Z3 context")
    if observation_bridges.candidate_assertion_fingerprint != verified_map.candidate_assertion_fingerprint:
        raise ObservableMapRefusal("proof-context-mismatch", "public bridges were created under a different candidate proof context")
    aliases = list(observation_bridges.aliases)
    bridges = list(observation_bridges.candidate_bridges)
    private = []
    protected = _free_constant_ids(assertions) | _free_constant_ids(aliases)
    for obligation in verified_map.plan.reconstruction_obligations:
        protected |= _free_constant_ids([obligation.candidate_term])
    for ordinal, obligation in enumerate(verified_map.plan.reconstruction_obligations):
        alias = _fresh_constant(obligation.candidate_term.sort(), f"{prefix}_{ordinal}",
                                protected, verified_map.candidate_context)
        if any(alias.get_id() == old.get_id() for old in aliases + private):
            raise ObservableMapRefusal("alias-not-fresh", "generated reconstruction alias is not distinct")
        private.append(alias)
        bridges.append((alias, obligation.candidate_term))
    receipt = CandidateBridgeSet(tuple(bridges), tuple(aliases), tuple(private),
                                 verified_map.candidate_context, _BRIDGE_TOKEN)
    _CANDIDATE_BRIDGE_RECEIPTS[id(receipt)] = receipt
    return receipt


def project_reference_relation(observation_bridges, reference_assertions, projection_fn):
    """Run the normal reference projection only on the bridge-bound full relation."""
    assertions = list(reference_assertions)
    if (_OBSERVATION_RECEIPTS.get(id(observation_bridges)) is not observation_bridges
            or observation_bridges._bridge_token is not _BRIDGE_TOKEN):
        raise ObservableMapRefusal("invalid-bridges", "observation bridge receipt is invalid or has been altered")
    if _assertion_fingerprint(assertions) != observation_bridges.reference_assertion_fingerprint:
        raise ObservableMapRefusal("proof-context-mismatch", "reference assertions differ from the bridge-bound reference relation")
    if assertions and any(_context_identity(item) != id(observation_bridges.reference_context) for item in assertions):
        raise ObservableMapRefusal("proof-context-mismatch", "reference assertions use a different Z3 context")
    return projection_fn(assertions, observation_bridges.reference_bridges)


def project_candidate_relation(verified_map, observation_bridges, candidate_assertions, projection_fn):
    """Project all candidate cells through the ordinary adapter, then hide private fixed-cell aliases."""
    expanded = complete_candidate_bridges(verified_map, observation_bridges,
                                          candidate_assertions)
    projected = projection_fn(list(candidate_assertions), expanded.bridges)
    formula = projected.formula if hasattr(projected, "formula") else projected
    return expanded.hide_private_aliases(formula)
