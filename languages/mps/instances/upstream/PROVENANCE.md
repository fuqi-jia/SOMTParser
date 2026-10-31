# Upstream corpus — MPS

Unmodified files from HiGHS `check/instances/` (the 30 smallest `.mps` files,
including Netlib's `afiro.mps`).

- Source: https://github.com/ERGO-Code/HiGHS/tree/master/check/instances
- Retrieved: 2026-08-17
- Licence: MIT (HiGHS developers, University of Edinburgh)

## Audit on 2026-08-25

The frontend accepts **13/30**, including scientific and Fortran-style decimals,
integrality markers, SC semi-continuous variables, and SI semi-integer variables.

Eleven valid files use `QUADOBJ`, `QMATRIX`, or `QSECTION`. These quadratic
objective extensions were named coverage gaps and returned
`E_UNSUPPORTED_CONSTRUCT`; they were not approximated as linear models.

## Update on 2026-09-20 — quadratic objectives implemented

**23/30.** Ten of those eleven now translate (`mps.md` §4.7). The eleventh,
`qjh_quadobj_qmatrix.mps`, carries BOTH a `QUADOBJ` and a `QMATRIX` stating the
same matrix; reading both would double every coefficient and picking one would
be a silent choice between two statements of the model, so it is refused by
name until HiGHS's own behaviour on it is checked.

This corpus turned out to be unusually good at settling a semantic question.
`2821.mps`, `2821-quadobj.mps`, `2821-duplicate.mps` (a repeated entry),
`2821-summation.mps` (both triangles inside a `QUADOBJ`) and `2821-qmatrix.mps`
state **one model five ways**, and `qjh{,_quadobj,_qmatrix}.mps` do the same for
`QSECTION`. Requiring byte-identical output across each family pins the `1/2`
notation, the one-triangle-versus-full-matrix distinction, and duplicate
summation at once — none of which a single file could establish.

The remaining six are malformed-reader tests and are correctly rejected:
`garbage`, three `nan` files, `warnings` (undeclared rows), and `comment` (an
inline `*Comment`, although `*` is only a full-line comment marker). CPLEX 22.1
also rejects `warnings.mps` and `comment.mps` at those records.

The accepted-path audit also fixes the first-vector rule for RHS/RANGES/BOUNDS,
the negative objective-offset sign, marker-integer 0/1 defaults, CPLEX's SC
lower default of 1, and exact `D`/`E` scientific notation conversion.

## Update on 2026-09-22 — HiGHS answered the `qjh_quadobj_qmatrix` question

**24/30.** The note above refused `qjh_quadobj_qmatrix.mps` "until HiGHS's own
behaviour on it is checked", because reading both quadratic sections would
double every coefficient and picking one would be a silent choice between two
statements of the model.

Checked, with HiGHS 1.15.1:

| file | HiGHS optimum |
|---|---|
| `qjh.mps` (QSECTION) | −5.25 |
| `qjh_quadobj.mps` (QUADOBJ) | −5.25 |
| `qjh_qmatrix.mps` (QMATRIX) | −5.25 |
| `qjh_quadobj_qmatrix.mps` (both) | **−2.75** |

Three spellings of one model agree; the fourth does not, and a doubled
quadratic form is exactly what separates those two numbers. **HiGHS sums the
sections** — which is also what this reader already did for a repeated entry
*within* one section (`2821-duplicate.mps`, on the argument that last-wins
would read a model nobody wrote). So the refusal was the odd one out, and
removing it required no other change: the per-entry convention already keys off
the current section, and repeats already sum.

Our emitted objective now carries every quadratic coefficient at exactly twice
the single-section value with the linear terms untouched, which is what
`test_mps_quadratic.cpp` pins — on the coefficients rather than on an optimum,
because z3's quadratic optimisation does not terminate quickly on this model.

The remaining six are the malformed-reader tests named above.

## Correction on 2026-09-23 — two defined reader interpretations

The prior blanket classification of the six refusals as malformed was too broad.
HiGHS 1.15.1 imports `warnings.mps` with kWarning and an infeasible model.
`highs_warning_recovery=1` now selects its documented first-nonzero/first-record
interpretation and records every recovered entry. This option remains separate
from the strict default and from the historical strict-MPS sweep counts.

Gurobi 13.0.3 accepts unchanged `comment.mps`, including inline asterisk comments,
and obtains optimum -4. Complete-record trailing comments are now supported,
with a recorded convention. Column names and declared row names containing or
starting with a marker are preserved. Gurobi's inconsistent auto-detection on
malformed free-field probes is not emulated. The remaining garbage and NaN files
remain refused; accepting an empty model or NaN arithmetic is not exact
real-arithmetic translation.
