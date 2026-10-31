"""Compose complete relation certificates, preserving observations and costs.

Positive existential witnesses are opened capture-safely. A complete mutex
clique can then be compressed by an exact Boolean identity. Each resulting
whole body is checked first by conjunct grouping and then, if necessary, by
independent implications in both directions. Local SAT and poor witness
correspondences remain inconclusive for the original existential formulas.
"""
import z3
from .existential_bijection import prove_existential_bijection, _opened_conjunction
from .existential_definitions import eliminate_existential_definitions
from .finite_product_domains import project_finite_product_domains
from .pairwise_cardinality import compress_pairwise_at_most_one
from .packed_tuple_cliques import compress_packed_tuple_cliques
from .arithmetic_context import normalize_arithmetic_context
from .qf_conjuncts import prove_qf_conjunctions
from .qf_implications import prove_qf_conjunct_implications
from .qf_context_refinement import prove_qf_refined_implications


def _complete_body_certificate(left, right):
    arithmetic = [normalize_arithmetic_context(value) for value in (left, right)]
    left, right = (value.formula for value in arithmetic)
    tuples = [compress_packed_tuple_cliques(left, right),
              compress_packed_tuple_cliques(right, left)]
    compressed = [compress_pairwise_at_most_one(x.formula) for x in tuples]
    a, b = (x.formula for x in compressed)
    grouping = prove_qf_conjunctions(a, b)
    result = dict(equivalent=grouping['equivalent'],
                  solver_queries=grouping['solver_queries'],
                  method='complete bodies with exact mutex compression',
                  all_original_conjuncts_retained=True,
                  grouping_certificate=grouping,
                  arithmetic_context=[dict(retained_original_bounds=x.retained_original_bounds,
                                           decided_comparisons=x.decided_comparisons,
                                           quotient_remainders=x.quotient_remainders)
                                      for x in arithmetic],
                  packed_tuple_projection=[dict(certificates=x.certificates,
                                                consumed_clauses=x.consumed_clauses)
                                           for x in tuples],
                  pairwise_compression=[dict(components=x.components,
                                             consumed_clauses=x.consumed_clauses,
                                             generated_indicator_terms=x.generated_indicator_terms)
                                        for x in compressed])
    if grouping['equivalent'] is True:
        return result
    directional = prove_qf_conjunct_implications(a, b)
    result['directional_certificate'] = directional
    result['solver_queries'] += directional['solver_queries']
    # A SAT local obligation does not establish a counterexample to either
    # complete body, and still less to the existentially closed relation.
    if directional['equivalent'] is True:
        result['equivalent'] = True
        return result
    refined = prove_qf_refined_implications(a, b)
    result['refined_directional_certificate'] = refined
    result['solver_queries'] += refined['solver_queries']
    # A counterexample to the opened bodies can still arise solely from the
    # candidate witness correspondence. Keep it inconclusive at this level.
    result['equivalent'] = True if refined['equivalent'] is True else None
    return result


def prove_complete_relation(left, right):
    """Return a sufficient whole-relation certificate without changing inputs.

    The caller supplies complete formulas including its observable and signed
    cost coordinates. Exact finite product images and explicit definitions can remove extra
    compiler witnesses. Residual arity/sort mismatches and nonpositive binders
    are left for the caller's original full-formula solver fallback.
    """
    original = prove_existential_bijection(left, right,
                                            body_checker=_complete_body_certificate)
    if original.get('reason') != 'candidate witness arity or sorts differ':
        return original
    # A different number of compiler witnesses is not a semantic difference.
    # Move only positive conjunction-local existential blocks using fresh
    # constants, then remove explicitly defined witnesses by exact substitution.
    # Every original domain, relation and signed-cost observation remains in
    # the substituted body; no candidate assignment supplies a definition.
    products = [project_finite_product_domains(formula) for formula in (left, right)]
    projections = []
    for product in products:
        formula = product.formula
        body, witnesses = _opened_conjunction(formula)
        outer = z3.Exists(witnesses, body) if witnesses else body
        projections.append(eliminate_existential_definitions(outer))
    counts = [dict(direct=p.direct_definitions,
                   conditional=p.conditional_definitions,
                   scalarized_arrays=p.scalarized_arrays,
                   indicator_products=p.indicator_products) for p in projections]
    if not any(p.direct_definitions or p.conditional_definitions or
               p.scalarized_arrays or p.indicator_products for p in projections) and not any(p.quantifiers for p in products):
        return original
    proof = prove_existential_bijection(projections[0].formula,
                                       projections[1].formula,
                                       body_checker=_complete_body_certificate)
    proof.update(finite_product_projection=[dict(quantifiers=p.quantifiers,
                                                 enumerated_pairs=p.enumerated_pairs,
                                                 distinct_values=p.distinct_values) for p in products],
                 definition_projection=counts,
                 original_witnesses=[original['left_witnesses'],
                                     original['right_witnesses']],
                 exact_positive_conjunction_projection=True)
    return proof
