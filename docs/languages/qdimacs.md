# QDIMACS — quantified Boolean formulas

SOMTParser imports QDIMACS CNF matrices and Boolean quantifier prefixes into
one closed HIR formula. Implementation: `languages/qdimacs/src/qdimacs.cpp`.

## Specification and implicit variables

The [QDIMACS 1.1 specification](https://www.qbflib.org/qdimacs.html), released
December 21, 2005, defines unbound matrix atoms as **existentially quantified
at the outermost level** (Input format, third additional constraint).
The specification was checked directly on October 11, 2026.

The earlier version of this document incorrectly required every matrix atom
to occur in the explicit prefix. The implementation and tests inherited that
mistake. The corrected frontend accepts ordinary DIMACS input and partial
quantifier prefixes.

<!-- implicit-constraints:
  a matrix variable absent from the prefix => implicitly existential at the outermost level; never place it under a universal
  explicit prefix order => quantifier dependencies and nesting must be preserved
  the prefix scopes over the entire matrix => never quantify clauses separately
  repeated matrix occurrences of an implicit variable => introduce one binder
-->

For example:

```text
p cnf 3 3
a 1 0
e 3 0
-1 2 0
1 -2 0
3 0
```

means `exists x2. forall x1. exists x3. (x1 = x2) and x3`, which is false.
Putting `x2` in the inner existential block would make it true. If the first
explicit block is existential, implicit variables join that block; otherwise
an existential block is prepended. With no explicit prefix, all matrix
variables form one existential block.

QCIR differs in representation: its unquantified non-gate variables remain
free declarations. Both formats accept these inputs. QDIMACS has a closed
truth-value query; QCIR may expose a relation over free variables.

## Construct to HIR mapping

| Source construct | HIR representation |
|---|---|
| Positive or negative matrix literal | `BOUND_VAR`, optionally under `NOT` |
| Clause | `OR`; the empty clause is `false` |
| Matrix | `AND`; the empty matrix is `true` |
| `a ... 0` / `e ... 0` | `FORALL` / `EXISTS` with Boolean binders |
| Unquantified matrix variables | One outermost existential block, or added to the first existential block |
| Whole instance | One constraint, with the entire prefix outside the matrix |

The frontend declares no free source model variables. The original HIR keeps
quantifier order and the specified implicit outer existential completion;
repeated implicit occurrences share one binder.

SMT export replaces an existential at the outermost positive assertion or
conjunction position by fresh private constants. For example, `exists x. P(x)`
becomes an assertion `P(w)` with a private declaration for `w`. An existential
under a universal, negation, disjunction or reification keeps its scope.
Existential projection of the private witnesses recovers the complete source
relation. The source signature and its observables never include these new
constants. Witness multiplicity is not claimed to preserve model counts.

`num_constraints` remains one. `num_vars` and
`max_quantifier_alternations` describe the exported HIR: declarations include
private witnesses, and an eliminated outer existential does not contribute an
alternation. These output statistics are not the original QDIMACS prefix depth
or source-variable count. Use the original prefix for source stratification and
the semantic contract for the source signature.

## Accepted syntax and diagnostics

The reader supports comments, a `p cnf V C` problem line, prefix blocks,
clauses spanning lines, and multiple zero-terminated clauses on one line.
Repeated explicit quantification, negative prefix indices, missing terminators,
and quantifier blocks after the matrix produce parse diagnostics.

Header count mismatches retain all content and produce warnings by default.
`TranslateOptions::parse.strict` turns these mismatches into errors. This flag
is a header-consistency policy, not a validator for every normal-form
restriction in QDIMACS 1.1.

The frontend also retains semantically meaningful extensions accepted by its
existing interface: unused explicit binders, adjacent blocks of the same
quantifier, an innermost universal block, and an empty matrix. The standard
places additional normal-form restrictions on these forms; their acceptance
does not alter the formula's meaning. Unused header indices are not introduced
as model variables or implicit binders.

## Correctness checks

`test/languages/test_qdimacs.cpp` checks prefix structure, whole-matrix scope,
implicit existential completion, header diagnostics, and malformed input.
`test/languages/test_sat_cross_format.cpp` checks free versus bound variables
across DIMACS, QCIR, and QDIMACS.
`test/python/test_qdimacs_implicit_exists.py` compares translated formulas with
independently written quantified Boolean formulas using Z3. Its dependency
example changes truth value if implicit variables are moved into an inner
existential block. Eight additional Boolean controls exhaustively evaluate both
existential/universal orders independently of the translator and compare the
complete projected output against that truth value.

A successful import or SMT load alone does not establish source equivalence.
Competition conversion counts, full target loading, and semantic verification
must be reported separately. These unit checks do not stand in for a complete
competition evaluation.

## Fidelity and output

The supported translation is exact: it preserves the closed QBF truth value,
quantifier dependencies, every matrix clause, and the standard's implicit
closure. QBF strategies or Skolem-function certificates are not exposed as
ordinary model assignments by this frontend. There is no optimization
objective.

Incorrect encodings include quantifying each clause separately, permuting
opposite quantifiers, or placing implicit variables inside a universal scope.
A fully quantified reference and its corresponding partially quantified input
must denote the same closed formula under the specification's completion rule.
