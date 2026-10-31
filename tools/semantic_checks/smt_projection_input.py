"""Parse validated SMT-LIB before applying the acyclic-helper projection rewrite."""
from dataclasses import dataclass

from .nonrecursive_helpers import normalize


@dataclass(frozen=True)
class ParsedProjectionInput:
    optimize: object
    normalization: dict


def parse_for_projection(script, *, z3, context=None):
    """Parse the complete original module, then parse its conservative normalized form.

    The first parse is an independent validation pass over the exact input bytes.
    The second parse changes only singleton ``define-fun-rec`` heads whose own
    name is absent from the body. Assertions and optimization objectives are
    retained byte-for-byte. The caller can pass the resulting AST vectors to
    ``checker_adapter.check_relation_equivalence`` without treating the helper
    as an uninterpreted or recursive function during existential projection.
    """
    raw = script.encode("utf-8") if isinstance(script, str) else bytes(script)
    raw_text = raw.decode("utf-8")
    validation_context = z3.Context()
    validation = z3.Optimize(ctx=validation_context)
    validation.from_string(raw_text)
    normalized, receipt = normalize(raw)
    normalized_text = normalized.decode("utf-8")
    model = z3.Optimize(ctx=context) if context is not None else z3.Optimize()
    model.from_string(normalized_text)
    return ParsedProjectionInput(model, receipt)


def check_smt_relation_equivalence(reference_smt2, candidate_smt2, *, z3,
                                   bridge_builder, context=None,
                                   **check_options):
    """Parse both complete inputs, construct bridges, and compare relations.

    ``bridge_builder(reference_optimize, candidate_optimize)`` runs after both
    targets have been parsed and returns a mapping containing
    ``reference_bridges`` and ``candidate_bridges``; optional entries are
    ``reference_cost_bridge`` and ``candidate_cost_bridge``. Cost bridge terms
    must encode the caller's signed objective, preserving min/max direction.
    """
    from .checker_adapter import check_relation_equivalence

    context = context if context is not None else z3.Context()
    reference = parse_for_projection(reference_smt2, z3=z3, context=context)
    candidate = parse_for_projection(candidate_smt2, z3=z3, context=context)
    reference_objectives = reference.optimize.objectives()
    candidate_objectives = candidate.optimize.objectives()
    if len(reference_objectives) != len(candidate_objectives):
        raise ValueError('reference and candidate objective counts differ')
    if len(reference_objectives) > 1:
        raise ValueError('multiple objectives are unsupported by the single-cost relation checker')

    bridges = bridge_builder(reference.optimize, candidate.optimize)
    required = {'reference_bridges', 'candidate_bridges'}
    if not isinstance(bridges, dict) or not required.issubset(bridges):
        raise ValueError('bridge_builder must return both observable bridge lists')
    reference_cost = bridges.get('reference_cost_bridge')
    candidate_cost = bridges.get('candidate_cost_bridge')
    if len(reference_objectives) == 1 and (reference_cost is None or candidate_cost is None):
        raise ValueError('both signed cost bridges are required when objectives are present')
    if len(reference_objectives) == 0 and (reference_cost is not None or candidate_cost is not None):
        raise ValueError('cost bridges are forbidden when neither model has an objective')
    return check_relation_equivalence(
        reference.optimize.assertions(), candidate.optimize.assertions(),
        reference_bridges=bridges['reference_bridges'],
        candidate_bridges=bridges['candidate_bridges'],
        reference_cost_bridge=reference_cost,
        candidate_cost_bridge=candidate_cost,
        **check_options)
