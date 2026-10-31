"""Explicit projection of unused coordinates in nonnegative Real LP references.

This is an evaluation option, not a reference correction or a candidate repair.
The original reference and the strict comparison result remain unchanged.
"""
from dataclasses import dataclass
from fractions import Fraction
import hashlib
import json

from somtparser.nl_datasets import LinearReference


def _number(value):
    if type(value) not in (int, Fraction):
        raise TypeError("reference coefficients must be exact integers or Fractions")
    return Fraction(value)


def _formula(reference):
    """Bind the certificate to every coefficient and the implicit domain."""
    return {
        "domain": "nonnegative-continuous-Real",
        "names": list(reference.names),
        "rows_le": [[list(map(str, coefficients)), str(limit)]
                    for coefficients, limit in reference.rows],
        "objective": list(map(str, reference.objective)),
        "maximize": reference.maximize,
    }


def _digest(value):
    data = json.dumps(value, sort_keys=True, separators=(",", ":"),
                      ensure_ascii=False).encode()
    return hashlib.sha256(data).hexdigest()


@dataclass(frozen=True)
class ReferenceCoordinateProjection:
    reference: LinearReference
    retained_indices: tuple
    omitted_indices: tuple
    original_names: tuple
    original_formula_sha256: str

    def certificate(self):
        return {
            "schema": "somt-unused-reference-coordinate-projection-v1",
            "status": "projection-certified",
            "domain": "nonnegative-continuous-Real",
            "original_formula_sha256": self.original_formula_sha256,
            "projected_formula_sha256": _digest(_formula(self.reference)),
            "retained_coordinates": [
                {"original_index": original, "projected_index": projected,
                 "name": self.original_names[original]}
                for projected, original in enumerate(self.retained_indices)
            ],
            "omitted_coordinates": [
                {"original_index": index, "name": self.original_names[index],
                 "every_row_coefficient": "0", "objective_coefficient": "0",
                 "only_remaining_bound": "coordinate >= 0", "extension_value": "0"}
                for index in self.omitted_indices
            ],
            "proof": "Every projected solution extends with omitted coordinates equal to zero; every original solution restricts to a projected solution, with identical objective.",
            "raw_reference_modified": False,
            "candidate_modified": False,
            "candidate_equivalence": "not-checked",
            "strict_comparison_result": "unchanged",
        }


def project_unused_reference_coordinates(reference, retained_indices=None):
    """Return a new reference and a zero-extension certificate.

    Only the exact ``LinearReference`` contract is accepted: all variables are
    nonnegative Reals, every additional restriction is an explicit <= row, and
    the objective is the recorded linear vector. A coordinate can be omitted
    only if its coefficient is exactly zero in every row and the objective.
    Even a redundant explicit bound with a nonzero coefficient prevents its
    omission. Constant rows, including contradictions, are always retained.

    By default retain every used coordinate in original order. An explicit
    distinct index sequence may also retain unused coordinates or permute the
    retained order; it must include every used coordinate. The caller must
    apply the returned index map when aligning the unchanged candidate.
    """
    if type(reference) is not LinearReference:
        raise TypeError("projection requires the exact LinearReference domain contract")
    names = tuple(reference.names)
    if (any(not isinstance(name, str) or not name for name in names)
            or len(set(names)) != len(names)):
        raise ValueError("reference names must be distinct nonempty strings")
    if type(reference.maximize) is not bool:
        raise TypeError("objective direction must be Boolean")
    size = len(names)
    objective = tuple(_number(value) for value in reference.objective)
    if len(objective) != size:
        raise ValueError("objective dimension differs from reference names")
    rows = []
    for coefficients, limit in reference.rows:
        coefficients = tuple(_number(value) for value in coefficients)
        if len(coefficients) != size:
            raise ValueError("constraint dimension differs from reference names")
        rows.append((coefficients, _number(limit)))
    used = {index for index in range(size)
            if objective[index] != 0 or any(row[index] != 0 for row, _ in rows)}
    retained = tuple(sorted(used)) if retained_indices is None else tuple(retained_indices)
    if any(type(index) is not int or index < 0 or index >= size for index in retained):
        raise ValueError("retained coordinates must be in-range integer indices")
    if len(set(retained)) != len(retained):
        raise ValueError("retained coordinates must be distinct")
    if not used.issubset(retained):
        raise ValueError("cannot omit a coordinate used by a row or objective")
    omitted = tuple(index for index in range(size) if index not in retained)
    normalized = LinearReference(names, tuple(rows), objective,
                                 reference.maximize, reference.adjustments)
    projected = LinearReference(
        tuple(names[index] for index in retained),
        tuple((tuple(row[index] for index in retained), limit) for row, limit in rows),
        tuple(objective[index] for index in retained),
        reference.maximize, reference.adjustments,
    )
    return ReferenceCoordinateProjection(projected, retained, omitted, names,
                                         _digest(_formula(normalized)))
