"""Proof-gated helpers for comparing finite observable relations.

Z3Py is imported only when a helper function is called, so importing this
package does not make Z3 a mandatory dependency for other SOMTParser tools.
"""

from .checker_adapter import (
    RelationEquivalenceCheck,
    candidate_projection,
    check_relation_equivalence,
    reference_projection,
)
from .directional_equivalence import (
    DirectionResult,
    EquivalenceResult,
    check_equivalence,
)
from .finite_observables import (
    FiniteObservableAlignment,
    align_finite_observables,
)
from .coordinate_map import (
    CandidateBridgeSet,
    CoordinateMapPlan,
    CoordinatePair,
    ObservationBridges,
    ObservableMapRefusal,
    ReconstructionObligation,
    VerifiedCoordinateMap,
    build_coordinate_map,
    complete_candidate_bridges,
    fresh_observation_bridges,
    project_candidate_relation,
    project_reference_relation,
    verify_reconstruction,
)
from .projection import (
    Optimization,
    existential_projection,
    optimize_observation_projection,
)

__all__ = [
    "CandidateBridgeSet",
    "CoordinateMapPlan",
    "CoordinatePair",
    "DirectionResult",
    "EquivalenceResult",
    "FiniteObservableAlignment",
    "ObservationBridges",
    "ObservableMapRefusal",
    "Optimization",
    "ReconstructionObligation",
    "RelationEquivalenceCheck",
    "VerifiedCoordinateMap",
    "align_finite_observables",
    "build_coordinate_map",
    "candidate_projection",
    "check_equivalence",
    "check_relation_equivalence",
    "complete_candidate_bridges",
    "existential_projection",
    "fresh_observation_bridges",
    "optimize_observation_projection",
    "project_candidate_relation",
    "project_reference_relation",
    "reference_projection",
    "verify_reconstruction",
]
