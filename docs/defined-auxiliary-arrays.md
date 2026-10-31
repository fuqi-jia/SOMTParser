# Defined auxiliary arrays in observable projection

After finite quantifier expansion and observable substitution, the checker can
eliminate a hidden array whose remaining scalar reads are fully defined by
unconditional equalities. This transformation preserves the complete projected
relation, including observation and cost equations. It does not edit the
candidate or reference model.

Let `E` contain equalities `A[i] = t_i` for finitely many distinct concrete
integer index tuples. Each `t_i` is free of `A`. If every remaining occurrence
of `A` disappears after replacing these full scalar reads, then

```text
exists A. (E and R)  <=>  (E and R)[A[i] := t_i]
```

Necessity follows by substitution of the defining equalities. For sufficiency,
choose an arbitrary total array and update the finitely many distinct cells to
the values of `t_i`. Nested arrays use nested stores. All array sorts are
inhabited, so unmentioned cells admit arbitrary values. Every defining equation
is retained: if a cell has multiple definitions, choosing the first replacement
keeps the equalities between its proposed values.

The implementation accepts only top-level conjunct equalities and full scalar
select chains at literal integer indices. Self-dependent definitions, residual
symbolic reads, array prefixes or whole-array uses prevent elimination of that
root. A group is committed only after checking that the root disappeared from
the entire body. Acyclic dependencies between auxiliary arrays can be processed
in sequence; a remaining group is kept intact. Quantified bodies must first use
the separately validated finite expansion, or remain on the original projection
path. Partially observed array roots stay on the observation-specific path.

Focused checks include free observable values, duplicate definitions, explicit
nested-array witnesses, acyclic definitions, missing cells, symbolic reads,
conditional definitions, and cost preservation. Direct quantified-array XOR
queries can return `unknown`; the nested and acyclic tests instead check both
necessary and sufficient conditions using explicit total-array witnesses.

In the six archived DCP candidates, this removes the internal `degree` array in
the two Diamond Free models. Their remaining equivalence checks still time out
at the original 5000 ms limit. The observed result remains one established
equivalence and five unknowns, rather than a new natural-language accuracy rate.
Knights Tour's inverse arrays use symbolic indices and remain quantified.
