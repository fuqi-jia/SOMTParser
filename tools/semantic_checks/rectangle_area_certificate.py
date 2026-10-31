"""Check a packing-area lower bound using premises from the actual target.

Finitely many axis-aligned rectangles with nonnegative side lengths, disjoint
interiors, and contained in one rectangle have total area at most its area.
We check every premise of that theorem, including the objective equality.
Only an UNSAT implication query authorizes the bound. No candidate coordinates
or incumbent objective are used, and caller-provided hypotheses are forbidden:
the support is selected by index from the complete target assertion sequence.

The caller must bind ``signed_cost`` to the actual single ordered objective of
the parsed target. Extra original constraints can only strengthen the bound.
This proves an objective bound, not equivalence of the two complete relations.
"""
from __future__ import annotations

from dataclasses import dataclass
from hashlib import sha256
from typing import Sequence

import z3


@dataclass(frozen=True)
class Rectangle:
    x: z3.ArithRef
    y: z3.ArithRef
    width: z3.ArithRef
    height: z3.ArithRef
    area: int


def certify_rectangle_area(
    assertions: Sequence[z3.BoolRef],
    signed_cost: z3.ArithRef,
    origin_x: z3.ArithRef,
    origin_y: z3.ArithRef,
    region_width: z3.ArithRef,
    region_height: z3.ArithRef,
    rectangles: Sequence[Rectangle],
    *,
    support_indices: Sequence[int] | None = None,
) -> dict:
    """Prove the total integer rectangle area is a lower bound on signed cost.

    A caller may choose a smaller *original* support to avoid unrelated search.
    Each support index refers to the supplied complete sequence; it cannot add
    an assumption. The serialized query and hashes are returned for retention.
    SAT or unknown never produce a certified lower bound.
    """
    assertions = tuple(assertions)
    rectangles = tuple(rectangles)
    if not rectangles:
        raise ValueError("at least one rectangle is required")
    numeric = [signed_cost, origin_x, origin_y, region_width, region_height]
    for rectangle in rectangles:
        if not isinstance(rectangle, Rectangle):
            raise ValueError("rectangle descriptor required")
        if type(rectangle.area) is not int or rectangle.area <= 0:
            raise ValueError("rectangle areas must be positive integers")
        numeric.extend((rectangle.x, rectangle.y, rectangle.width, rectangle.height))
    if any(not isinstance(term, z3.ArithRef) or term.sort().kind() not in
           (z3.Z3_INT_SORT, z3.Z3_REAL_SORT) for term in numeric):
        raise ValueError("all coordinates and costs must be integer or real expressions")
    ctx = signed_cost.ctx
    if any(term.ctx != ctx for term in numeric):
        raise ValueError("all expressions must use the same context")
    if any(not z3.is_bool(term) or term.ctx != ctx for term in assertions):
        raise ValueError("original assertions must be Boolean expressions in the same context")
    indices = tuple(range(len(assertions))) if support_indices is None else tuple(support_indices)
    if any(type(i) is not int or not 0 <= i < len(assertions) for i in indices):
        raise ValueError("support indices must select existing original assertions")
    if len(set(indices)) != len(indices):
        raise ValueError("duplicate support indices")

    premises = [("region-width-nonnegative", region_width >= 0),
                ("region-height-nonnegative", region_height >= 0)]
    for i, rect in enumerate(rectangles):
        premises.extend([
            (f"rectangle-{i}-positive-width", rect.width > 0),
            (f"rectangle-{i}-positive-height", rect.height > 0),
            (f"rectangle-{i}-left-contained", rect.x >= origin_x),
            (f"rectangle-{i}-bottom-contained", rect.y >= origin_y),
            (f"rectangle-{i}-right-contained", rect.x + rect.width <= origin_x + region_width),
            (f"rectangle-{i}-top-contained", rect.y + rect.height <= origin_y + region_height),
            (f"rectangle-{i}-exact-area", rect.width * rect.height == rect.area),
        ])
    for i, left in enumerate(rectangles):
        for j in range(i + 1, len(rectangles)):
            right = rectangles[j]
            premises.append((f"rectangles-{i}-{j}-disjoint", z3.Or(
                left.x + left.width <= right.x, right.x + right.width <= left.x,
                left.y + left.height <= right.y, right.y + right.height <= left.y)))
    premises.append(("signed-objective-is-region-area", signed_cost == region_width * region_height))
    solver = z3.Solver(ctx=ctx)
    solver.add(*[assertions[i] for i in indices])
    solver.add(z3.Not(z3.And(*[formula for _, formula in premises])))
    query = solver.to_smt2()
    status = solver.check()
    original_hashes = [sha256(term.sexpr().encode()).hexdigest() for term in assertions]
    result = dict(
        passed=status == z3.unsat,
        status=str(status),
        method="contained-disjoint-rectangle-area",
        lower_bound=sum(rect.area for rect in rectangles) if status == z3.unsat else None,
        theorem_area_sum=sum(rect.area for rect in rectangles),
        rectangle_count=len(rectangles),
        original_assertion_count=len(assertions),
        original_assertion_hashes=original_hashes,
        original_support_indices=list(indices),
        premise_labels=[name for name, _ in premises],
        signed_cost=signed_cost.sexpr(),
        query_sha256=sha256(query.encode()).hexdigest(),
        query_smt2=query,
        candidate_assignments_used=False,
        candidate_cost_used=False,
        full_relation_equivalence_claimed=False,
    )
    if status == z3.unknown:
        result["reason_unknown"] = solver.reason_unknown()
    elif status == z3.sat:
        result["unproved_premises"] = [name for name, formula in premises
                                        if not z3.is_true(solver.model().eval(formula, model_completion=True))]
    return result
