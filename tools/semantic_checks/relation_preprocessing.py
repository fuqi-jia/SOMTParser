"""Apply exact witness projections before comparing complete relations.

Every public coordinate, including the ordered signed costs supplied by the
caller, stays free. Only existing exact finite-image and existential-definition
rules are applied; their applicability does not depend on witness arity matching.
"""
from dataclasses import dataclass

import z3

from .existential_bijection import _opened_conjunction
from .existential_definitions import eliminate_existential_definitions
from .finite_product_domains import project_finite_product_domains
from .full_relation_certificate import prove_complete_relation


@dataclass(frozen=True)
class RelationPreprocessing:
    formula: object
    certificate: dict


def preprocess_complete_relation(formula, *, progress_callback=None):
    """Return an equivalent complete formula without consulting a solver."""
    if not z3.is_bool(formula):
        raise ValueError('complete relation must be Boolean')

    def phase(name, **details):
        if progress_callback is not None:
            progress_callback(dict(phase=name, **details))

    phase('exact-finite-product-images-started')
    products = project_finite_product_domains(formula)
    phase('exact-finite-product-images-completed', quantifiers=products.quantifiers)
    phase('open-positive-existential-conjunction-started')
    body, witnesses = _opened_conjunction(products.formula)
    outer = z3.Exists(witnesses, body) if witnesses else body
    phase('open-positive-existential-conjunction-completed', witnesses=len(witnesses))
    phase('exact-existential-definitions-started')
    definitions = eliminate_existential_definitions(outer)
    certificate = dict(
        method='exact finite images and positive existential definitions before body comparison',
        finite_product_quantifiers=products.quantifiers,
        enumerated_product_pairs=products.enumerated_pairs,
        distinct_product_values=products.distinct_values,
        opened_witnesses=len(witnesses),
        direct_definitions=definitions.direct_definitions,
        conditional_definitions=definitions.conditional_definitions,
        scalarized_arrays=getattr(definitions, 'scalarized_arrays', 0),
        indicator_products=getattr(definitions, 'indicator_products', 0),
        public_coordinates_preserved=True,
        original_constraints_and_cost_equations_retained_under_substitution=True,
        solver_queries=0,
    )
    phase('exact-existential-definitions-completed', **certificate)
    return RelationPreprocessing(definitions.formula, certificate)


def prove_preprocessed_complete_relation(left, right, *, progress_callback=None):
    """Prove complete relations after exact independent preprocessing of each.

    A failure to find a sufficient certificate remains inconclusive. No model,
    incumbent objective, or solution of either input supplies a projection law.
    """
    if left.ctx != right.ctx:
        raise ValueError('complete relations need one Z3 context')
    if not z3.is_bool(left) or not z3.is_bool(right):
        raise ValueError('complete relations must be Boolean')
    projections = []
    for side, formula in enumerate((left, right)):
        callback = (lambda event, side=side: progress_callback(dict(side=side, **event))) if progress_callback is not None else None
        projections.append(preprocess_complete_relation(formula, progress_callback=callback))
    if progress_callback is not None:
        progress_callback(dict(phase='complete-projected-relation-certificate-started'))
    proof = prove_complete_relation(projections[0].formula, projections[1].formula)
    result = dict(proof, preprocessing=[p.certificate for p in projections],
                  preprocessing_before_body_comparison=True)
    if progress_callback is not None:
        progress_callback(dict(phase='complete-projected-relation-certificate-completed',
                               equivalent=result['equivalent'], solver_queries=result['solver_queries']))
    return result
